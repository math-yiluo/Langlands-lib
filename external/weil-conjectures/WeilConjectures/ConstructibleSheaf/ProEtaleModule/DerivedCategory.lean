/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme, `R` a
commutative ring object of `Sheaf (Scheme.ProEt.topology X) A`. The derived category of
sheaves of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
The *bounded constructible* derived category `ProEtale.BoundedConstructible R` is the full
subcategory of `D(X_proét, R)` (`ProEtale.boundedConstructible R`) consisting of the complexes
`K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval (for the canonical
   t-structure, see `ProEtale.mem_boundedConstructible_iff`);
2. every cohomology sheaf `Hⁱ(K)` is constructible (`ProEtale.IsConstructibleModuleObject R`).

Morphisms are computed in `D(X_proét, R)`. For `R = 𝒪_{E,X}` this is `D_cons(X_proét, 𝒪_E)`;
for `R = E_X` it is `D_cons(X_proét, E)`.
No derived completeness condition is imposed.

## Main results

For the `ℓ`-adic coefficient rings `Λ_X = p_X^* Λ` with `Λ` one of `𝒪̲_E` or `E̲` for a finite
extension `E` of `ℚ_ℓ`, or `ℚ̲̄_ℓ`, the bounded constructible complexes on a topologically
noetherian scheme form a triangulated subcategory. This is stated separately for each of these
coefficient rings (`ProEtale.isTriangulated_boundedConstructible_padicIntegersRingObj`,
`ProEtale.isTriangulated_boundedConstructible_integralCoeff`,
`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj`,
`ProEtale.isTriangulated_boundedConstructible_padicAlgClRingObj`). It rests on the fact that
constructible sheaves of `Λ_X`-modules on such a scheme are closed under kernels, cokernels and
extensions (Bhatt–Scholze, Section 6.8): see
`ProEtale.CondensedRing.integralConstructible_serre` for `𝒪̲_E`, and
`WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre` for `E̲` and `ℚ̲̄_ℓ`. The complexes
whose cohomology sheaves lie in such a class form a triangulated subcategory
(`DerivedCategory.homologyProperty_isTriangulated`); for any commutative ring object `R` whose
constructible module objects are closed under kernels, cokernels and extensions this is
`ProEtale.isTriangulated_boundedConstructible_of_serre`.
It is false for a general commutative ring object `R`: for `X = Spec k̄` and `R` the constant
sheaf of the non-coherent ring `k[x₁, x₂, …]/(x₁xᵢ)ᵢ`, the cone of `x₁ : R ⟶ R` has `H⁻¹` the
constant sheaf of the ideal `(x₂, x₃, …)`, which is not finitely generated. Noetherianity is
assumed only there: the definition `ProEtale.boundedConstructible` makes sense on any scheme.

## Sorried input

The derived category itself uses the `sorry`ed instances of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R] [IsCommMonObj R]

/-- The bounded constructible complexes of sheaves of `R`-modules on `X`: the complexes `K`
which are bounded for the canonical t-structure and all of whose cohomology sheaves `Hⁿ(K)`
are constructible. -/
noncomputable def boundedConstructible :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstructibleModuleObject R ((DerivedCategory.homologyFunctor _ n).obj K)

omit [IsCommMonObj R] in
/-- A complex is bounded constructible iff its cohomology sheaves vanish outside a finite
interval `[a, b]` and are all constructible. -/
lemma mem_boundedConstructible_iff
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :
    boundedConstructible R K ↔
      (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℤ, IsConstructibleModuleObject R ((DerivedCategory.homologyFunctor _ n).obj K) := by
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i hi
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ h i (Or.inl hi)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ h i (Or.inr hi)⟩⟩

/-- The bounded constructible derived category `D_cons(X_proét, R)`. -/
abbrev BoundedConstructible : Type _ :=
  (boundedConstructible R).FullSubcategory

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj ZeroObject

/-- A zero module object is finitely presented: it is the cokernel of the zero map between free
modules of rank zero. -/
private lemma finitelyPresented_of_isZero {C : Type*} [Category* C] [MonoidalCategory C]
    [Abelian C] [MonoidalPreadditive C] {S : C} [MonObj S]
    [PreservesFiniteColimits (tensorLeft S)] {M : Mod C S} (hM : IsZero M) :
    Mod.IsFinitelyPresented S M := by
  refine ⟨0, 0, 0, ⟨hM.iso ?_⟩⟩
  have h0 : IsZero (Mod.finiteFree S 0) := by
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun i ↦ i.elim0
  have := h0.epi (0 : Mod.finiteFree S 0 ⟶ Mod.finiteFree S 0)
  exact isZero_cokernel_of_epi _

omit [IsCommMonObj R] in
/-- The pullback of a zero module object is zero. -/
private lemma isZero_mapMod_upperStar_obj {Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (hM : IsZero M) :
    IsZero (((ProEtale.upperStar A f).mapMod R).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  refine (Mod.forget _).map_injective ?_
  exact ((ProEtale.upperStar A f).map_isZero ((Mod.forget R).map_isZero hM)).eq_of_src _ _

omit [IsCommMonObj R] in
/-- A zero module object is constructible, for the trivial stratification and the identity
cover. -/
private lemma constructible_of_isZero {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (hM : IsZero M) : IsConstructibleModuleObject R M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun _ ↦ ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun _ ↦
    finitelyPresented_of_isZero
      (isZero_mapMod_upperStar_obj _ _ (isZero_mapMod_upperStar_obj R _ hM))⟩⟩

/-- The zero complex is bounded constructible: it is bounded, and its cohomology
sheaves are zero, which is constructible for the trivial stratification (the cokernel of `R⁰ ⟶ R⁰`).
This makes `BoundedConstructible R` have a zero object without going through the triangulated
structure. -/
instance containsZero_boundedConstructible : (boundedConstructible R).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, (mem_boundedConstructible_iff R 0).2
    ⟨⟨0, 0, fun i _ ↦ (DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _)⟩,
      fun n ↦ constructible_of_isZero R
        ((DerivedCategory.homologyFunctor _ n).map_isZero (isZero_zero _))⟩⟩

namespace CondensedRing

/-- The bounded constructible derived category `D_cons(X_proét, Λ_X)` of module objects over
`Λ_X = p_X^* Λ`, for a commutative condensed ring `Λ`. -/
scoped notation "Dᵇc(" X ")⟦" Λ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X)

end CondensedRing

/-- The coefficient ring `E̲` of a finite extension `E` of `ℚ_ℓ` satisfies the local freeness
hypothesis of `condensed_constructible_serre_of_locally_free`: a locally finitely presented
module over `E_X` on a noetherian scheme is pro-étale locally free. -/
private lemma continuous_lf (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj E) X)).obj M) := by
  let E' := ULift.{u} E
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (by
        intro S a b
        apply ULift.ext
        change (a.down * b.down : C(S.unop, E')) = b.down * a.down
        exact mul_comm a.down b.down)
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
  let φ := (upperStarFromPoint X).map e.hom
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (liftCoefficientIso E).hom
  have : IsMonHom φ := inferInstance
  have h := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
    ((Mod.comap (inv φ)).obj M) (lfp_comap (inv φ) hM)
  exact locally_free_of_iso (locally_free_comap φ h)
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app M)

omit [IsCommMonObj R] in
/-- If the constructible module objects over `R` are closed under kernels, cokernels and
extensions, the bounded constructible complexes form a triangulated subcategory. -/
lemma isTriangulated_boundedConstructible_of_serre
    (hk : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) A) R)
      (f : M ⟶ N), IsConstructibleModuleObject R M →
      IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧
      IsConstructibleModuleObject R (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) A) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e ⟨S, hS⟩ ↦ ⟨S, fun a ↦
      lfp_of_iso (hS a) (((ProEtale.upperStar A (S.immersion a)).mapMod R).mapIso e)⟩⟩
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact ObjectProperty.prop_of_iso _ (limit.isoLimitCone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).1⟩
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact ObjectProperty.prop_of_iso _ (colimit.isoColimitCocone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).2⟩
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) := ⟨he _⟩
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) :=
    ⟨0, isZero_zero _, constructible_of_isZero R (isZero_zero _)⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated
  infer_instance

section Triangulated

open CondensedRing
open scoped CategoryTheory.Obj

variable (X : Scheme.{u})

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Blueprint `prop-sfb-bounded-constructible-triangulated`, for `𝒪̲_E`: for a finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the bounded constructible complexes of `𝒪_{E,X}`-modules on a
topologically noetherian scheme form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_padicIntegersRingObj
    [TopologicalSpace.NoetherianSpace X] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).IsTriangulated := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨hker, hcok, hext⟩ := CondensedRing.integralConstructible_serre ℓ E X
  change ObjectProperty.IsClosedUnderKernels
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hker
  change ObjectProperty.IsClosedUnderCokernels
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hcok
  change ObjectProperty.IsClosedUnderExtensions
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hext
  exact isTriangulated_boundedConstructible_of_serre _
    (fun M N f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
      ObjectProperty.prop_cokernel _ f hM hN⟩)
    (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)

/-- Blueprint `prop-sfb-bounded-constructible-triangulated`, for `𝒪̲_E` given as the closed unit
ball of a finite normed extension `E` of `ℚ_ℓ` (`CondensedRing.integralCoeff`): the bounded
constructible complexes of `𝒪_{E,X}`-modules on a topologically noetherian scheme form a
triangulated subcategory. -/
instance isTriangulated_boundedConstructible_integralCoeff
    [TopologicalSpace.NoetherianSpace X] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructible
      (condensedRingObj (CondensedRing.integralCoeff.{u} ℓ E) X)).IsTriangulated := by
  obtain ⟨hker, hcok, hext⟩ := CondensedRing.integralConstructible_serre ℓ E X
  exact isTriangulated_boundedConstructible_of_serre _
    (fun M N f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
      ObjectProperty.prop_cokernel _ f hM hN⟩)
    (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)

-- The prime `ℓ` of `E̲` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
/-- Blueprint `prop-sfb-bounded-constructible-triangulated`, for `E̲`: for a finite
extension `E` of `ℚ_ℓ`, the bounded constructible complexes of `E_X`-modules on a topologically
noetherian scheme form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_continuousMapRingObj
    [TopologicalSpace.NoetherianSpace X] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).IsTriangulated := by
  obtain ⟨hk, he⟩ := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
    (Profinite.continuousMapRingObj E) (continuous_lf ℓ E) X
  exact isTriangulated_boundedConstructible_of_serre _ hk he

/-- Blueprint `prop-sfb-bounded-constructible-triangulated`, for `ℚ̲̄_ℓ`: the bounded
constructible complexes of `ℚ̄_{ℓ,X}`-modules on a topologically noetherian scheme form a
triangulated subcategory. -/
instance isTriangulated_boundedConstructible_padicAlgClRingObj
    [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated := by
  obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicAlgCl X ℓ
  exact isTriangulated_boundedConstructible_of_serre _ hk he

end Triangulated

end AlgebraicGeometry.ProEtale
