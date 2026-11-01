import Langlands.Algebra.IdempotentAnnihilatorComparisonStatements
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Quotient idempotence and fixed-part comparisons

Proofs of the closed comparison targets for the actual named quotient and
corner functors. See the paired Markdown for source correspondence and scope.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM uN uC

namespace IdempotentAnnihilatorComparisons

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]

/-- The annihilator of the actual quotient vanishes. -/
theorem quotient_annihilator_eq_zero (x : annihilatorQuotientCarrier e M)
    (hx : x ∈ NonUnitalSubmodule.idempotentAnnihilator e
      (annihilatorQuotientCarrier e M)) : x = 0 := by
  obtain ⟨m, rfl⟩ := annihilatorQuotientProjection_surjective e x
  apply (annihilatorQuotientProjection_eq_zero_iff e m).2
  intro a
  have hm : ((e : A) * a) • m ∈ NonUnitalSubmodule.idempotentAnnihilator e M :=
    (annihilatorQuotientProjection_eq_zero_iff e _).1 (by
      rw [← smul_annihilatorQuotientProjection]
      exact hx a)
  have h := NonUnitalSubmodule.idempotent_smul_eq_zero_of_mem hm
  rwa [← mul_smul, ← mul_assoc, e.property.eq] at h

/-- The second quotient projection is bijective with its named structures. -/
theorem second_projection_bijective :
    Function.Bijective (annihilatorQuotientProjection e (annihilatorQuotientCarrier e M)) := by
  refine ⟨(injective_iff_map_eq_zero
    (annihilatorQuotientProjection e (annihilatorQuotientCarrier e M)).toAddMonoidHom).2 ?_,
    annihilatorQuotientProjection_surjective e⟩
  intro x hx
  exact quotient_annihilator_eq_zero e M x
    ((annihilatorQuotientProjection_eq_zero_iff e x).1 hx)

/-- The inverse is the published descent of the identity through the second quotient. -/
def secondProjectionInverse :
    NonUnitalModuleHom A (annihilatorQuotientCarrier e (annihilatorQuotientCarrier e M))
      (annihilatorQuotientCarrier e M) :=
  (NonUnitalModuleHom.id A (annihilatorQuotientCarrier e M)).annihilatorQuotientDesc e
    (fun x hx => quotient_annihilator_eq_zero e M x hx)

@[simp] theorem secondProjectionInverse_comp_projection :
    (secondProjectionInverse e M).comp
      (annihilatorQuotientProjection e (annihilatorQuotientCarrier e M)) =
        NonUnitalModuleHom.id A (annihilatorQuotientCarrier e M) := rfl

@[simp] theorem projection_comp_secondProjectionInverse :
    (annihilatorQuotientProjection e (annihilatorQuotientCarrier e M)).comp
      (secondProjectionInverse e M) =
        NonUnitalModuleHom.id A
          (annihilatorQuotientCarrier e (annihilatorQuotientCarrier e M)) :=
  annihilatorQuotient_hom_ext e rfl

/-- Quotienting the first projection gives exactly the second projection. -/
theorem map_projection :
    NonUnitalModuleHom.annihilatorQuotientMap e (annihilatorQuotientProjection e M) =
      annihilatorQuotientProjection e (annihilatorQuotientCarrier e M) :=
  annihilatorQuotient_hom_ext e rfl

/-- The complete pointwise quotient-idempotence target. -/
theorem quotient_idempotence : IdempotentAnnihilatorQuotientIdempotence e M :=
  ⟨quotient_annihilator_eq_zero e M, second_projection_bijective e M,
    ⟨secondProjectionInverse e M, secondProjectionInverse_comp_projection e M,
      projection_comp_secondProjectionInverse e M⟩, map_projection e M⟩

/-- Both directions of quotient idempotence are natural for arbitrary original maps. -/
theorem quotient_naturality (N : Type uN) [AddCommGroup N] [NonUnitalModule A N] :
    IdempotentAnnihilatorQuotientIdempotenceNaturality e M N := by
  refine ⟨quotient_idempotence e M, quotient_idempotence e N, ?_⟩
  intro f
  refine ⟨NonUnitalModuleHom.annihilatorQuotientMap_comp_projection e
    (NonUnitalModuleHom.annihilatorQuotientMap e f), ?_⟩
  intro rM rN hM _hM' hN _hN'
  apply NonUnitalModuleHom.ext
  intro y
  obtain ⟨x, rfl⟩ := annihilatorQuotientProjection_surjective e y
  have hx := congrArg (fun k => k x) hM
  have hn := congrArg (fun k => k (NonUnitalModuleHom.annihilatorQuotientMap e f x)) hN
  change NonUnitalModuleHom.annihilatorQuotientMap e f
    (rM (annihilatorQuotientProjection e _ x)) =
      rN (annihilatorQuotientProjection e _ (NonUnitalModuleHom.annihilatorQuotientMap e f x))
  change rM (annihilatorQuotientProjection e _ x) = x at hx
  rw [hx]
  exact hn.symm

/-- The actual restricted projection is bijective on the fixed subtypes. -/
theorem fixed_projection_bijective :
    Function.Bijective (NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M)) := by
  refine ⟨(injective_iff_map_eq_zero
    (NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M)).toAddMonoidHom).2 ?_, ?_⟩
  · intro x hx
    apply Subtype.ext
    have hm : x.val ∈ NonUnitalSubmodule.idempotentAnnihilator e M :=
      (annihilatorQuotientProjection_eq_zero_iff e _).1
        (congrArg Subtype.val hx)
    exact x.property.symm.trans (NonUnitalSubmodule.idempotent_smul_eq_zero_of_mem hm)
  · intro x
    obtain ⟨m, hm⟩ := annihilatorQuotientProjection_surjective e x.val
    refine ⟨NonUnitalModuleCorner.projection e m, ?_⟩
    apply Subtype.ext
    change annihilatorQuotientProjection e M ((e : A) • m) = x.val
    rw [NonUnitalModuleHom.map_smul, hm]
    exact x.property

/-- The corner-linear equivalence has the actual restriction as its entire forward map. -/
noncomputable def fixedProjectionEquiv :
    NonUnitalModuleCorner.FixedPart e M ≃ₗ[Idempotent.Corner e]
      NonUnitalModuleCorner.FixedPart e (annihilatorQuotientCarrier e M) :=
  LinearEquiv.ofBijective (NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M))
    (fixed_projection_bijective e M)

/-- The complete pointwise fixed-part target. -/
theorem fixed_comparison : IdempotentAnnihilatorFixedPartComparison e M := by
  refine ⟨fixed_projection_bijective e M, (fixedProjectionEquiv e M).symm.toLinearMap, ?_, ?_,
    fixedProjectionEquiv e M, rfl, rfl⟩
  · exact (fixedProjectionEquiv e M).symm_comp
  · exact (fixedProjectionEquiv e M).comp_symm

/-- Both directions of the fixed-part comparisons are natural as whole linear maps. -/
theorem fixed_naturality (N : Type uN) [AddCommGroup N] [NonUnitalModule A N] :
    IdempotentAnnihilatorFixedPartComparisonNaturality e M N := by
  refine ⟨fixed_comparison e M, fixed_comparison e N, ?_⟩
  intro f
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  · intro rM rN hM _hM' hN _hN'
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (fixed_projection_bijective e M).2 y
    have hx := congrArg (fun k => k x) hM
    have hn := congrArg (fun k => k (NonUnitalModuleCorner.restrict e f x)) hN
    change rM (NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M) x) = x at hx
    change NonUnitalModuleCorner.restrict e f
      (rM (NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M) x)) = _
    rw [hx]
    exact hn.symm

/-- Objectwise quotient idempotence in the actual ambient category. -/
def quotientIso (X : NonUnitalModuleCat.{uA, uC} A) :
    (NonUnitalModuleCat.annihilatorQuotientFunctor e).obj X ≅
      (NonUnitalModuleCat.annihilatorQuotientFunctor e ⋙
        NonUnitalModuleCat.annihilatorQuotientFunctor e).obj X where
  hom := annihilatorQuotientProjection e (annihilatorQuotientCarrier e X)
  inv := secondProjectionInverse e X
  hom_inv_id := secondProjectionInverse_comp_projection e X
  inv_hom_id := projection_comp_secondProjectionInverse e X

/-- Ambient quotient idempotence, with the second projection as its forward component. -/
def quotientNaturalIso :
    NonUnitalModuleCat.annihilatorQuotientFunctor.{uA, uC} e ≅
      NonUnitalModuleCat.annihilatorQuotientFunctor e ⋙
        NonUnitalModuleCat.annihilatorQuotientFunctor e :=
  NatIso.ofComponents (quotientIso e) (fun f =>
    (NonUnitalModuleHom.annihilatorQuotientMap_comp_projection e
      (NonUnitalModuleHom.annihilatorQuotientMap e f)).symm)

/-- The same components lifted to the actual nondegenerate full subcategory. -/
def nondegenerateQuotientIso (X : NondegenerateModuleCat.{uA, uC} A) :
    (NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e).obj X ≅
      (NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e ⋙
        NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e).obj X where
  hom := ObjectProperty.homMk (quotientIso e X.obj).hom
  inv := ObjectProperty.homMk (quotientIso e X.obj).inv
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact (quotientIso e X.obj).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact (quotientIso e X.obj).inv_hom_id

/-- Quotient idempotence on nondegenerate modules. -/
def nondegenerateQuotientNaturalIso :
    NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor.{uA, uC} e ≅
      NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e ⋙
        NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e :=
  NatIso.ofComponents (nondegenerateQuotientIso e) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact (NonUnitalModuleHom.annihilatorQuotientMap_comp_projection e
      (NonUnitalModuleHom.annihilatorQuotientMap e f.hom)).symm)

/-- The specified ambient and nondegenerate isomorphisms agree in both directions. -/
theorem quotient_natural_iso :
    IdempotentAnnihilatorQuotientIdempotenceNaturalIso.{uA, uC} e := by
  refine ⟨quotientNaturalIso e, ?_, nondegenerateQuotientNaturalIso e, ?_, ?_, ?_⟩
  all_goals
    apply NatTrans.ext
    funext X
    rfl

/-- Objectwise fixed-part comparison in the actual corner-module category. -/
noncomputable def fixedIso (X : NonUnitalModuleCat.{uA, uC} A) :
    (NonUnitalModuleCorner.functor e).obj X ≅
      (NonUnitalModuleCat.annihilatorQuotientFunctor e ⋙
        NonUnitalModuleCorner.functor e).obj X :=
  (fixedProjectionEquiv e X).toModuleIso

/-- Ambient fixed-part comparison with the actual restricted quotient projection. -/
noncomputable def fixedNaturalIso :
    NonUnitalModuleCorner.functor.{uA, uC} e ≅
      NonUnitalModuleCat.annihilatorQuotientFunctor e ⋙ NonUnitalModuleCorner.functor e :=
  NatIso.ofComponents (fixedIso e) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

/-- The fixed-part comparison restricted along the nondegenerate inclusion. -/
noncomputable def nondegenerateFixedNaturalIso :
    NonUnitalModuleCorner.nondegenerateFunctor.{uA, uC} e ≅
      NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e ⋙
        NonUnitalModuleCorner.nondegenerateFunctor e :=
  NatIso.ofComponents (fun X => fixedIso e X.obj) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

/-- Both transformations are the restrictions of the ambient ones, as specified. -/
theorem fixed_natural_iso :
    IdempotentAnnihilatorFixedPartComparisonNaturalIso.{uA, uC} e := by
  refine ⟨fixedNaturalIso e, ?_, nondegenerateFixedNaturalIso e, ?_, ?_, ?_⟩
  all_goals
    apply NatTrans.ext
    funext X
    rfl

end IdempotentAnnihilatorComparisons

/-- The entire closed quotient-idempotence family, without additional premises. -/
theorem idempotentAnnihilatorQuotientIdempotence :
    IdempotentAnnihilatorQuotientIdempotenceTheorem.{uA, uM, uN, uC} := by
  intro A _ e
  refine ⟨?_, ?_, IdempotentAnnihilatorComparisons.quotient_natural_iso e⟩
  · intro M _ _
    exact IdempotentAnnihilatorComparisons.quotient_idempotence e M
  · intro M N _ _ _ _
    exact IdempotentAnnihilatorComparisons.quotient_naturality e M N

/-- The entire closed fixed-part comparison family, without additional premises. -/
theorem idempotentAnnihilatorFixedPartComparison :
    IdempotentAnnihilatorFixedPartComparisonTheorem.{uA, uM, uN, uC} := by
  intro A _ e
  refine ⟨?_, ?_, IdempotentAnnihilatorComparisons.fixed_natural_iso e⟩
  · intro M _ _
    exact IdempotentAnnihilatorComparisons.fixed_comparison e M
  · intro M N _ _ _ _
    exact IdempotentAnnihilatorComparisons.fixed_naturality e M N

/-- Renard I.3.2 quotient idempotence and canonical fixed-part comparisons,
including actual-map naturality and both nondegenerate inclusion comparisons. -/
theorem idempotentAnnihilatorComparisons :
    IdempotentAnnihilatorComparisonsTheorem.{uA, uM, uN, uC} :=
  ⟨idempotentAnnihilatorQuotientIdempotence, idempotentAnnihilatorFixedPartComparison⟩

/-! Complete unapplied types preserve four independent universes. -/

example : IdempotentAnnihilatorComparisonsTheorem.{uA, uM, uN, uC} :=
  idempotentAnnihilatorComparisons.{uA, uM, uN, uC}

example : IdempotentAnnihilatorComparisonsTheorem.{2, 1, 0, 3} :=
  idempotentAnnihilatorComparisons.{2, 1, 0, 3}

example : IdempotentAnnihilatorComparisonsTheorem.{0, 1, 2, 0} :=
  idempotentAnnihilatorComparisons.{0, 1, 2, 0}

end Langlands.Algebra
