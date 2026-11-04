import Langlands.GroupScheme.Torus.NoTorusStructuralReductionStatement
import Langlands.GroupScheme.Torus.NoClosedTorus
import Langlands.GroupScheme.Nilpotent.FiniteHom
import Langlands.GroupScheme.Cartan.LieInduction
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.ElementCentralizerNonunipotent
import Langlands.GroupScheme.Lie.SmoothIsogenyDimension

/-! # The conditional structural reduction for no-torus unipotence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem elementCentralizerLie_one {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    Lie.elementCentralizerLie G (1 : lieKernel G k) = ⊤ := by
  apply top_unique
  intro Y _
  change Y.toMul.val ∈ (Lie.elementCentralizer G 1).carrier _
  intro A _ _ a
  simp only [map_one, OneMemClass.coe_one, Commute.one_right]

/-- The six explicit structural propositions imply the exact arbitrary-field
no-torus unipotence statement. -/
theorem noTorusStructuralReduction : NoTorusStructuralReductionStatement.{u} := by
  intro hnil hfinite halgclosed hsmooth hspanning hisog k _ G _ _ _ hG
  have hclosed : HasNoNontrivialClosedTorus G :=
    HasNoNontrivialClosedTorus.of_forall_hom hG
  rcases finite_or_infinite k with hk | hk
  · let := hk
    exact HasNoNontrivialClosedTorus.isUnipotent_of_finiteField
      hfinite halgclosed hclosed
  · let := hk
    apply smoothConnectedAffineGroup_lieDimension_induction
      (fun H => HasNoNontrivialClosedTorus H → IsUnipotent H) ?_ G hclosed
    intro H _ _ _ ih hH
    obtain ⟨H', q, hsm, haff, hconn, hrest⟩ := hisog k H
    let := hsm
    let := haff
    let := hconn
    obtain ⟨hq, hcases, hlift⟩ := hrest
    have hH' : HasNoNontrivialClosedTorus H' := hH.of_torus_lifting q hlift
    rcases hcases with hnilH' | hgeo
    · let : IsFinite q.hom.hom.left := hq.1
      exact HasNoNontrivialClosedTorus.isUnipotent_of_nilpotent hnil hH
        (IsNilpotentGroupScheme.of_finiteHom q hnilH')
    · obtain ⟨X, hX, hproper⟩ := (hspanning k H' hgeo).1
      obtain ⟨C, j, hrep, hj⟩ := Lie.elementCentralizer_isClosedRepresentable H' X
      let : Smooth C.X.hom := hsmooth k H' X hX C j hrep hj
      let : IsClosedImmersion j.hom.hom.left := hj
      let : IsAffineHom C.X.hom := by
        rw [← Over.w j.hom.hom]
        infer_instance
      have hdim : Lie.dimension (identityComponent C) < Lie.dimension H' :=
        Lie.dimension_identityComponent_lt_of_lie_ne_top hrep hj hproper
      have heq : Lie.dimension H = Lie.dimension H' :=
        Lie.finrank_kernel_eq_of_isogeny q hq
      have hsub : HasNoNontrivialClosedTorus (identityComponent C) :=
        hH'.of_closedSubgroup (identityComponentι C ≫ j)
          ((IdentityComponent.isClosedSubgroup_identityComponentι C).comp hj)
      have huni : IsUnipotent (identityComponent C) :=
        ih (identityComponent C) (hdim.trans_eq heq.symm) hsub
      have hne : X ≠ 1 := by
        intro he
        exact hproper (he ▸ elementCentralizerLie_one H')
      exact False.elim
        (Lie.not_isUnipotent_identityComponent_elementCentralizer X hX hne j hrep huni)

end Langlands.GroupScheme
