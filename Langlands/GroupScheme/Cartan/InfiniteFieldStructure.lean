import Langlands.GroupScheme.Torus.NoTorusStructuralReductionProof
import Langlands.GroupScheme.Nilpotent.CentralTorusProof
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningProof
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReduction
import Langlands.GroupScheme.Cartan.CentralTorusQuotient

/-! # Cartan structure over every infinite field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem elementCentralizerLie_one_of_infiniteField {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    Lie.elementCentralizerLie G (1 : lieKernel G k) = ⊤ := by
  apply top_unique
  intro Y _
  change Y.toMul.val ∈ (Lie.elementCentralizer G 1).carrier _
  intro A _ _ a
  simp only [map_one, OneMemClass.coe_one, Commute.one_right]

variable {k : Type u} [Field k] [Infinite k]
    {G C : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an infinite field, absence of nontrivial closed tori forces
unipotence. All four inputs in the published induction are supplied here. -/
theorem HasNoNontrivialClosedTorus.isUnipotent_of_infiniteField
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : HasNoNontrivialClosedTorus G) : IsUnipotent G := by
  apply smoothConnectedAffineGroup_lieDimension_induction
    (fun H => HasNoNontrivialClosedTorus H → IsUnipotent H) ?_ G hG
  intro H _ _ _ ih hH
  obtain ⟨H', q, hsm, haff, hconn, hrest⟩ := semisimpleIsogenyReduction k H
  let := hsm
  let := haff
  let := hconn
  obtain ⟨hq, hcases, hlift⟩ := hrest
  have hH' : HasNoNontrivialClosedTorus H' := hH.of_torus_lifting q hlift
  rcases hcases with hnilH' | hgeo
  · let : IsFinite q.hom.hom.left := hq.1
    exact HasNoNontrivialClosedTorus.isUnipotent_of_nilpotent
      nilpotentCentralTorusStatement hH (IsNilpotentGroupScheme.of_finiteHom q hnilH')
  · obtain ⟨X, hX, hproper⟩ := (Lie.semisimpleCentralizerSpanning k H' hgeo).1
    obtain ⟨D, j, hrep, hj⟩ := Lie.elementCentralizer_isClosedRepresentable H' X
    let : Smooth D.X.hom := Lie.semisimpleCentralizerSmooth k H' X hX D j hrep hj
    let : IsClosedImmersion j.hom.hom.left := hj
    let : IsAffineHom D.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    have hdim : Lie.dimension (identityComponent D) < Lie.dimension H' :=
      Lie.dimension_identityComponent_lt_of_lie_ne_top hrep hj hproper
    have heq : Lie.dimension H = Lie.dimension H' :=
      Lie.finrank_kernel_eq_of_isogeny q hq
    have hsub : HasNoNontrivialClosedTorus (identityComponent D) :=
      hH'.of_closedSubgroup (identityComponentι D ≫ j)
        ((IdentityComponent.isClosedSubgroup_identityComponentι D).comp hj)
    have huni : IsUnipotent (identityComponent D) :=
      ih (identityComponent D) (hdim.trans_eq heq.symm) hsub
    have hne : X ≠ 1 := by
      intro he
      exact hproper (he ▸ elementCentralizerLie_one_of_infiniteField H')
    exact False.elim
      (Lie.not_isUnipotent_identityComponent_elementCentralizer X hX hne j hrep huni)

/-- The actual quotient by a central maximal torus is unipotent over any
infinite ground field. -/
theorem CentralMaximalTorusQuotientData.isUnipotent_of_infiniteField
    (D : CentralMaximalTorusQuotientData G) : IsUnipotent D.quotient := by
  let := D.smooth_quotient
  let := D.affine_quotient
  let := D.connected_quotient
  exact (HasNoNontrivialClosedTorus.of_forall_hom D.no_tori).isUnipotent_of_infiniteField

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {j : C ⟶ G}

/-- A Cartan subgroup over an infinite field has a uniform nilpotence
bound on points over every relative scheme test. -/
theorem IsCartanSubgroup.exists_hasUniformNilpotentPoints_of_infiniteField
    (hj : IsCartanSubgroup j) : ∃ d, HasUniformNilpotentPoints C d := by
  let D := hj.centralTorusQuotient
  exact D.exists_hasUniformNilpotentPoints D.isUnipotent_of_infiniteField

/-- A chosen all-test nilpotence bound for a Cartan subgroup over any
infinite ground field. -/
def IsCartanSubgroup.nilpotenceBoundOfInfiniteField (hj : IsCartanSubgroup j) : ℕ :=
  Classical.choose hj.exists_hasUniformNilpotentPoints_of_infiniteField

/-- The chosen infinite-field bound applies to every relative scheme test. -/
theorem IsCartanSubgroup.nilpotenceBoundOfInfiniteField_spec
    (hj : IsCartanSubgroup j) :
    HasUniformNilpotentPoints C hj.nilpotenceBoundOfInfiniteField :=
  Classical.choose_spec hj.exists_hasUniformNilpotentPoints_of_infiniteField

/-- A Cartan subgroup is geometrically nilpotent over every infinite field. -/
theorem IsCartanSubgroup.isNilpotentGroupScheme_of_infiniteField
    (hj : IsCartanSubgroup j) : IsNilpotentGroupScheme C :=
  hj.nilpotenceBoundOfInfiniteField_spec.isNilpotentGroupScheme

/-- The full Cartan structure conclusion over every infinite field. -/
theorem IsCartanSubgroup.structure_of_infiniteField (hj : IsCartanSubgroup j) :
    Smooth C.X.hom ∧ ConnectedSpace C.X.left ∧ IsNilpotentGroupScheme C :=
  ⟨hj.smooth_connected.1, hj.smooth_connected.2,
    hj.isNilpotentGroupScheme_of_infiniteField⟩

end Langlands.GroupScheme
