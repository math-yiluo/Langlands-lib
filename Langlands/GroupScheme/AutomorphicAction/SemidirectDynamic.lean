import Langlands.GroupScheme.AutomorphicAction.SemidirectMaps
import Langlands.GroupScheme.Dynamic.ActionFunctoriality
import Langlands.GroupScheme.Dynamic.ActionUniqueness
import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Transport of dynamic functors through a semidirect group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {H G : GroupScheme B} (a : AutomorphicAction H G)
    (χ : (Gm B).toGrp ⟶ H)

/-- The normal-factor inclusion intertwines the original action and ambient conjugation. -/
theorem semidirectInl_isEquivariant :
    (a.restrict χ).IsEquivariant (cocharacterAction (χ ≫ a.semidirectInr))
      a.semidirectInl := by
  intro T t g
  rw [cocharacterAction_eq_conjugation, ← restrict_conjugation, restrict_act, restrict_act]
  exact (a.semidirect_conjugation (t ≫ χ.hom.hom) g).symm

/-- Fixed points are the preimage of the ambient conjugation centralizer. -/
theorem semidirect_centralizer_eq_comap :
    (a.restrict χ).centralizer =
      (Dynamic.centralizer (χ ≫ a.semidirectInr)).comap a.semidirectInl := by
  have h := IsEquivariant.centralizer_eq_comap_of_mono (a.semidirectInl_isEquivariant χ)
  rwa [cocharacterAction_centralizer] at h

/-- For a separated acting group, the parabolic is the preimage under the closed inclusion. -/
theorem semidirect_parabolic_eq_comap [IsSeparated H.X.hom] :
    (a.restrict χ).parabolic =
      (Dynamic.parabolic (χ ≫ a.semidirectInr)).comap a.semidirectInl := by
  have h := IsEquivariant.parabolic_eq_comap_of_isClosedSubgroup (a.semidirectInl_isEquivariant χ)
    a.isClosedSubgroup_semidirectInl
  rwa [cocharacterAction_parabolic] at h

/-- For a separated acting group, the identity-limit functor is the same preimage. -/
theorem semidirect_unipotent_eq_comap [IsSeparated H.X.hom] :
    (a.restrict χ).unipotent =
      (Dynamic.unipotent (χ ≫ a.semidirectInr)).comap a.semidirectInl := by
  have h := IsEquivariant.unipotent_eq_comap_of_isClosedSubgroup (a.semidirectInl_isEquivariant χ)
    a.isClosedSubgroup_semidirectInl
  rwa [cocharacterAction_unipotent] at h

/-- A commutative acting factor gives an invariant projection for ambient conjugation. -/
theorem semidirectProjection_isInvariant [IsCommMonObj H.X] :
    (cocharacterAction (χ ≫ a.semidirectInr)).IsInvariantMorphism
      a.semidirectProjection.hom.hom := by
  intro T t x
  rw [cocharacterAction_eq_conjugation, ← restrict_conjugation, restrict_act]
  exact a.semidirectProjection_conjugation (t ≫ χ.hom.hom) x

/-- Every ambient identity-limit point lies in the original normal factor. -/
theorem semidirect_unipotent_le_range [IsCommMonObj H.X] [IsSeparated H.X.hom] :
    Dynamic.unipotent (χ ≫ a.semidirectInr) ≤ SubgroupFunctor.range a.semidirectInl := by
  rw [a.range_semidirectInl]
  have h := (cocharacterAction (χ ≫ a.semidirectInr)).unipotent_le_comap_bot_of_invariant
    a.semidirectProjection (a.semidirectProjection_isInvariant χ)
  rwa [cocharacterAction_unipotent] at h

/-- The abstract identity-limit functor maps onto the whole ambient unipotent functor. -/
theorem semidirect_unipotent_map [IsCommMonObj H.X] [IsSeparated H.X.hom] :
    (a.restrict χ).unipotent.map a.semidirectInl =
      Dynamic.unipotent (χ ≫ a.semidirectInr) := by
  have h := IsEquivariant.range_inf_unipotent (a.semidirectInl_isEquivariant χ)
    a.isClosedSubgroup_semidirectInl
  rw [cocharacterAction_unipotent] at h
  have hle : SubgroupFunctor.range a.semidirectInl ⊓
      Dynamic.unipotent (χ ≫ a.semidirectInr) =
      Dynamic.unipotent (χ ≫ a.semidirectInr) :=
    SubgroupFunctor.ext fun T => inf_eq_right.mpr (a.semidirect_unipotent_le_range χ T)
  rw [hle] at h
  exact h.symm

section Representatives

variable [IsCommMonObj H.X] [IsSeparated H.X.hom]
    {U : GroupScheme B} {j : U ⟶ a.semidirectProduct}
    (hj : (Dynamic.unipotent (χ ≫ a.semidirectInr)).IsRepresentedBy j)

/-- Factor an ambient unipotent representative through the normal factor. -/
def semidirectUnipotentLift : U ⟶ G :=
  hj.lift
    (⟨inferInstance, rfl⟩ :
      (SubgroupFunctor.range a.semidirectInl).IsRepresentedBy a.semidirectInl)
    (fun T => Subgroup.inclusion (a.semidirect_unipotent_le_range χ T))
    (fun _ _ => rfl)

/-- The factored representative has the original ambient inclusion as its composite. -/
theorem semidirectUnipotentLift_comp :
    a.semidirectUnipotentLift χ hj ≫ a.semidirectInl = j :=
  hj.lift_comp_eq
    (⟨inferInstance, rfl⟩ :
      (SubgroupFunctor.range a.semidirectInl).IsRepresentedBy a.semidirectInl)
    (fun T => Subgroup.inclusion (a.semidirect_unipotent_le_range χ T))
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The same group scheme represents the original identity-limit functor. -/
theorem isRepresentedBy_semidirectUnipotentLift :
    (a.restrict χ).unipotent.IsRepresentedBy (a.semidirectUnipotentLift χ hj) := by
  have hfac : (a.semidirectUnipotentLift χ hj).hom.hom ≫ a.semidirectInl.hom.hom =
      j.hom.hom :=
    congrArg (fun f : U ⟶ a.semidirectProduct => f.hom.hom)
      (a.semidirectUnipotentLift_comp χ hj)
  constructor
  · have : Mono j.hom.hom := hj.1
    exact mono_of_mono_fac hfac
  · rw [a.semidirect_unipotent_eq_comap χ]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [SubgroupFunctor.mem_comap, ← hj.2, SubgroupFunctor.mem_range,
      SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by rw [Category.assoc, hfac]⟩
    · rintro ⟨u, hu⟩
      refine ⟨u, (cancel_mono a.semidirectInl.hom.hom).mp ?_⟩
      rw [Category.assoc, hfac]
      exact hu

/-- Closedness of the ambient representative passes to its normal-factor lift. -/
theorem isClosedSubgroup_semidirectUnipotentLift (hjc : IsClosedSubgroup j) :
    IsClosedSubgroup (a.semidirectUnipotentLift χ hj) := by
  have hfac : (a.semidirectUnipotentLift χ hj).hom.hom.left ≫
      a.semidirectInl.hom.hom.left = j.hom.hom.left :=
    congrArg (fun f : U ⟶ a.semidirectProduct => f.hom.hom.left)
      (a.semidirectUnipotentLift_comp χ hj)
  have hc : IsClosedImmersion ((a.semidirectUnipotentLift χ hj).hom.hom.left ≫
      a.semidirectInl.hom.hom.left) := hfac.symm ▸ hjc
  have : IsClosedImmersion a.semidirectInl.hom.hom.left :=
    a.isClosedSubgroup_semidirectInl
  exact @IsClosedImmersion.of_comp _ _ _ _ _ hc inferInstance

end Representatives

end Langlands.GroupScheme.AutomorphicAction
