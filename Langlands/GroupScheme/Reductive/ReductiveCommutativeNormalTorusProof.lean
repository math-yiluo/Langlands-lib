import Langlands.GroupScheme.Reductive.ReductiveCommutativeNormalTorusStatement
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Unipotent.TorusHom

/-! # Commutative normal subgroups and reductivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Smooth connected commutative normal subgroups of a connected reductive group
are tori, and this property characterizes reductivity over perfect fields. -/
theorem reductiveCommutativeNormalTorus :
    ReductiveCommutativeNormalTorusStatement.{u} := by
  intro k _ G hsm haff hconn
  have : Smooth G.X.hom := hsm
  have : IsAffineHom G.X.hom := haff
  have : ConnectedSpace G.X.left := hconn
  constructor
  · intro hG H j hj hHsm hHconn hHcomm hnormal
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Smooth H.X.hom := hHsm
    have : ConnectedSpace H.X.left := hHconn
    have : IsCommMonObj H.X := hHcomm
    have : IsAffineHom H.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    let b := toAlgebraicClosure k
    let Gbar := (GroupScheme.baseChange b).obj G
    let Hbar := (GroupScheme.baseChange b).obj H
    have hGbar : IsPseudoReductive Gbar :=
      { smooth := (hG.baseChange_toAlgebraicClosure).smooth
        isAffineHom := (hG.baseChange_toAlgebraicClosure).isAffineHom
        connectedSpace := (hG.baseChange_toAlgebraicClosure).connectedSpace
        hasTrivialUnipotentRadical := hG.hasTrivialGeometricUnipotentRadical }
    have : Smooth Hbar.X.hom :=
      inferInstanceAs (Smooth (Limits.pullback.snd H.X.hom b))
    have : IsCommMonObj Hbar.X :=
      Functor.isCommMonObj_obj (F := Over.pullback b) (M := H.X)
    have hHbarconn : ConnectedSpace Hbar.X.left :=
      H.connectedSpace_baseChange_of_smooth_affine b
    have hnormalbar :
        (SubgroupFunctor.range ((GroupScheme.baseChange b).map j)).IsNormal := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hnormal.baseChange b
    have hHbar : IsTorus Hbar :=
      (algClosedReductiveNormalSolvableTorus (AlgebraicClosure k) Gbar hGbar
        Hbar ((GroupScheme.baseChange b).map j) (hj.baseChange b)
        inferInstance hHbarconn (isSolvableGroupScheme_of_isCommMonObj Hbar)
        hnormalbar).1
    exact IsTorus.of_baseChange (K := AlgebraicClosure k) hHbar
  · intro hk htori
    have : PerfectField k := hk
    apply (perfectFieldPseudoReductive k G).mp
    refine ⟨hsm, haff, hconn, ?_⟩
    intro U i hi hUsm hUconn hU hnormal
    have : IsClosedImmersion i.hom.hom.left := hi
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    have : Smooth U.X.hom := hUsm
    have : ConnectedSpace U.X.left := hUconn
    have : IsAffineHom U.X.hom := by
      rw [← Over.w i.hom.hom]
      infer_instance
    by_contra hnontrivial
    have hUnontrivial : SubgroupFunctor.range (𝟙 U) ≠ ⊥ := by
      intro hz
      apply hnontrivial
      apply SubgroupFunctor.ext
      intro T
      apply le_antisymm _ bot_le
      intro x hx
      obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.1 hx
      have hv : v ∈ (SubgroupFunctor.range (𝟙 U)).carrier T :=
        SubgroupFunctor.mem_range.2 ⟨v, by simp⟩
      rw [hz, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hv
      change v ≫ i.hom.hom = 1
      rw [hv, MonObj.one_comp]
    have hnormalized :
        (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range (𝟙 G)) :=
      fun T g x _ hx => hnormal T g x (Subgroup.mem_top _) hx
    let b : AutomorphicAction G U :=
      AutomorphicAction.ofNormalizedConjugation i (𝟙 G) hnormalized
    obtain ⟨Z, z, bZ, hz, hZsm, hZaff, hZgeom, hZconn, hcentral, hstable,
        hZnontrivial, hequiv⟩ :=
      hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent b haff hUnontrivial hU
    have : IsClosedImmersion z.hom.hom.left := hz
    have : Mono z.hom.hom := Over.mono_of_mono_left _
    have hZcomm : IsCommMonObj Z.X := hcentral.isCommMonObj
    have hzclosed : IsClosedSubgroup (z ≫ i) := by
      change IsClosedImmersion (z.hom.hom.left ≫ i.hom.hom.left)
      infer_instance
    have hznormal : (SubgroupFunctor.range (z ≫ i)).IsNormal := by
      intro T g x _ hx
      obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.1 hx
      have hmem := hstable T g (v ≫ z.hom.hom)
        (SubgroupFunctor.mem_range.2 ⟨v, rfl⟩)
      obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.1 hmem
      refine SubgroupFunctor.mem_range.2 ⟨w, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, hw]
      simpa only [b, AutomorphicAction.act, AutomorphicAction.ofNormalizedConjugation,
        Grp.id_hom_hom, Category.comp_id, Grp.comp_hom_hom, Category.assoc] using
        SubgroupFunctor.lift_comp_normalizedConjugation_comp
          i (𝟙 G) hnormalized g (v ≫ z.hom.hom)
    have hZtorus : IsTorus Z :=
      htori Z (z ≫ i) hzclosed hZsm hZconn hZcomm hznormal
    exact hZnontrivial (hU.range_eq_bot_of_isTorus hZtorus z)

end Langlands.GroupScheme
