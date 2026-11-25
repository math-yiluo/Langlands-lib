/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!

# The constructible bounded derived category of étale sheaves

For a scheme `X` and a concrete abelian coefficient category `A`, this file defines the
subcategory `Dᵇc(X, A)` of the derived category
`DerivedCategory (Sheaf X.smallEtaleTopology A)` of étale sheaves consisting of the
bounded complexes all of whose homology sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf`). Boundedness refers to the canonical
t-structure `DerivedCategory.TStructure.t`.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
concrete Grothendieck abelian category with small-site sheafification
(`CategoryTheory.HasSmallSiteSheafify`) and `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes. Nothing beyond that is assumed:

- the left Kan extensions along base change, needed by the pullback `Etale.upperStar`
  entering `IsConstructibleSheaf`, come from the instance
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
  `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`;
- the chosen localized category `D(X_ét)` comes from the instance
  `HasDerivedCategory.ofIsGrothendieckAbelian` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`, which installs
  `HasDerivedCategory.{u + 1}` on every sheaf category out of the Grothendieck abelian
  structure supplied by `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`. In
  particular the derived category is no longer taken at an auxiliary universe `w`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology`: the property of an
  object of the derived category of étale sheaves that all its homology sheaves are
  constructible.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible`: the property of being
  bounded with constructible homology.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible`: the subcategory
  `Dᵇc( X, A)` cut out by the property above, the constructible bounded derived
  category of the `ℓ`-adic formalism.
- `AlgebraicGeometry.Etale.DerivedCategoryConstructibleIn`: the subcategory `D_c^[a, b](X, A)`
  of `Dᵇc(X, A)` of bounded constructible complexes with homology concentrated in `[a, b]`.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_isTriangulated`: `Dᵇc(X, A)`
  is a triangulated subcategory of `D(X_ét)`, provided the constructible sheaves are closed
  under kernels, cokernels and extensions (`Etale.constructibleSheaf`, the property of being
  constructible as an `ObjectProperty`; the closure properties are the content of the blueprint
  theorem `thm:constructible-serre`, not yet formalised, and are taken as hypotheses). This is
  `DerivedCategory.homologyProperty_isTriangulated` of
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

variable (X : Scheme.{u})

section ConstructibleHomology

/-- An object of the derived category of étale sheaves has constructible homology if all
its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ n : ℤ, IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj M)

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of étale sheaves is bounded constructible if it is
bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.TStructure.t.bounded ⊓ Etale.DerivedCategory.constructibleHomology A X

/-- The constructible bounded derived category `Dᵇc( X, A)`, realized as the full
subcategory of bounded complexes with constructible homology in the derived category of
étale sheaves. (blueprint: `def-weil-pbc-constructible-complexes`) -/
noncomputable def Etale.DerivedCategoryBoundedConstructible : Type _ :=
  (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

noncomputable instance : Category (Etale.DerivedCategoryBoundedConstructible A X) :=
  inferInstanceAs <|
    Category (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The inclusion of `Dᵇc(X, A)` into the derived category of étale sheaves. -/
noncomputable def Etale.DerivedCategoryBoundedConstructible.ι :
    Etale.DerivedCategoryBoundedConstructible A X ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (Etale.DerivedCategory.boundedConstructible A X).ι

@[inherit_doc Etale.DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc(" X ", " A ")" =>
  Etale.DerivedCategoryBoundedConstructible A X

/-- Blueprint `definition-constructible-sheaves`: the inclusion of the small category `Dᵇc(X, A)`
into the ambient bounded derived category `Dᵇ(X, A)` of étale sheaves. -/
noncomputable def Etale.DerivedCategoryBoundedConstructible.toBounded :
    Etale.DerivedCategoryBoundedConstructible A X ⥤
      DerivedCategory.Bounded (Sheaf X.smallEtaleTopology A) :=
  ObjectProperty.ιOfLE inf_le_left

/-- Membership in `D_c^[a, b](X, A)` as an object property of `D(X_ét)`: bounded constructible
with homology concentrated in `[a, b]` (blueprint `def-weil-constructible-intervals`). -/
noncomputable def Etale.DerivedCategory.constructibleIn (a b : ℤ) :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  Etale.DerivedCategory.boundedConstructible A X ⊓ DerivedCategory.homologyConcentratedIn a b

omit [HasSmallSiteSheafify A] in
lemma Etale.DerivedCategory.constructibleIn_iff (a b : ℤ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Etale.DerivedCategory.constructibleIn A X a b K ↔
      Etale.DerivedCategory.boundedConstructible A X K ∧
        DerivedCategory.homologyConcentratedIn a b K :=
  Iff.rfl

/-- Blueprint `definition-constructible-sheaves`: Ambient categories and small subcategories.

The small category `D_c^[a, b](X, A)` of bounded constructible complexes of étale sheaves with
homology concentrated in `[a, b]`, as a full subcategory of `D(X_ét)`. -/
noncomputable def Etale.DerivedCategoryConstructibleIn (a b : ℤ) : Type _ :=
  (Etale.DerivedCategory.constructibleIn A X a b).FullSubcategory

noncomputable instance (a b : ℤ) : Category (Etale.DerivedCategoryConstructibleIn A X a b) :=
  inferInstanceAs <| Category (Etale.DerivedCategory.constructibleIn A X a b).FullSubcategory

/-- The inclusion of `D_c^[a, b](X, A)` into the derived category of étale sheaves. -/
noncomputable def Etale.DerivedCategoryConstructibleIn.ι (a b : ℤ) :
    Etale.DerivedCategoryConstructibleIn A X a b ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (Etale.DerivedCategory.constructibleIn A X a b).ι

/-- The inclusion `D_c^[a, b](X, A) ⊆ Dᵇc(X, A)`. -/
noncomputable def Etale.DerivedCategoryConstructibleIn.toBoundedConstructible (a b : ℤ) :
    Etale.DerivedCategoryConstructibleIn A X a b ⥤
      Etale.DerivedCategoryBoundedConstructible A X :=
  ObjectProperty.ιOfLE inf_le_left

end BoundedConstructible

section Triangulated

/-- The property of being constructible, as a property of objects of the category of étale
sheaves; the closure of this property under kernels, cokernels and extensions is the blueprint
theorem `thm:constructible-serre`. -/
def Etale.constructibleSheaf : ObjectProperty (Sheaf X.smallEtaleTopology A) :=
  fun F ↦ IsConstructibleSheaf F

omit [HasSmallSiteSheafify A] in
lemma Etale.constructibleSheaf_iff (F : Sheaf X.smallEtaleTopology A) :
    Etale.constructibleSheaf A X F ↔ IsConstructibleSheaf F :=
  Iff.rfl

instance : (Etale.constructibleSheaf A X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have := (Etale.constructibleSheaf_iff A X _).mp h
    exact IsConstructibleSheaf.of_iso e

instance [PreservesFiniteLimits (CategoryTheory.forget A)] :
    (Etale.constructibleSheaf A X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, IsConstructibleSheaf.of_isZero (isZero_zero _)⟩

omit [HasSmallSiteSheafify A] in
/-- The constructible-homology property is the homology property of
`Etale.constructibleSheaf`. -/
lemma Etale.DerivedCategory.constructibleHomology_eq :
    Etale.DerivedCategory.constructibleHomology A X =
      _root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X) :=
  rfl

instance : (Etale.DerivedCategory.boundedConstructible A X).IsClosedUnderIsomorphisms := by
  rw [Etale.DerivedCategory.boundedConstructible, Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

/-- `Dᵇc(X, A)` is stable under the shifts of the derived category; unlike
`Etale.DerivedCategory.boundedConstructible_isTriangulated` this needs no closure property of
the constructible sheaves. -/
instance : (Etale.DerivedCategory.boundedConstructible A X).IsStableUnderShift ℤ := by
  rw [Etale.DerivedCategory.boundedConstructible, Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

variable {A X}

/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

At a finite coefficient stage, `Dᵇc(X, A)` is stable under the truncation `τ^{≤ n}` of the
canonical t-structure: the homology sheaves of `τ^{≤ n} K` are those of `K` in degrees `≤ n`,
and zero above. So the canonical truncations restrict to `Dᵇc(X, A)`. -/
lemma Etale.DerivedCategory.boundedConstructible_truncLE
    [PreservesFiniteLimits (CategoryTheory.forget A)]
    {K : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : Etale.DerivedCategory.boundedConstructible A X K) (n : ℤ) :
    Etale.DerivedCategory.boundedConstructible A X
      ((DerivedCategory.TStructure.t.truncLE n).obj K) := by
  obtain ⟨⟨⟨a, ha⟩, -⟩, hc⟩ := hK
  refine ⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩, ?_⟩
  rw [Etale.DerivedCategory.constructibleHomology_eq] at hc ⊢
  exact DerivedCategory.homologyProperty_truncLE hc n

/-- Blueprint `prop-constructible-truncations`: Construction of constructible truncations.

At a finite coefficient stage, `Dᵇc(X, A)` is stable under the truncation `τ^{≥ n}` of the
canonical t-structure: the homology sheaves of `τ^{≥ n} K` are those of `K` in degrees `≥ n`,
and zero below. -/
lemma Etale.DerivedCategory.boundedConstructible_truncGE
    [PreservesFiniteLimits (CategoryTheory.forget A)]
    {K : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : Etale.DerivedCategory.boundedConstructible A X K) (n : ℤ) :
    Etale.DerivedCategory.boundedConstructible A X
      ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
  obtain ⟨⟨-, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩, ?_⟩
  rw [Etale.DerivedCategory.constructibleHomology_eq] at hc ⊢
  exact DerivedCategory.homologyProperty_truncGE hc n

/-- A constructible sheaf placed in degree `n` is a bounded constructible complex: its only
nonzero homology sheaf is itself, in degree `n`. -/
lemma Etale.DerivedCategory.boundedConstructible_singleFunctor_obj
    [PreservesFiniteLimits (CategoryTheory.forget A)] (F : Sheaf X.smallEtaleTopology A)
    [IsConstructibleSheaf F] (n : ℤ) :
    Etale.DerivedCategory.boundedConstructible A X
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) n).obj F) := by
  refine ⟨⟨⟨n, inferInstanceAs (DerivedCategory.IsGE _ n)⟩,
    ⟨n, inferInstanceAs (DerivedCategory.IsLE _ n)⟩⟩, fun m ↦ ?_⟩
  obtain hm | rfl | hm := lt_trichotomy m n
  · exact IsConstructibleSheaf.of_isZero ((DerivedCategory.isGE_iff _ n).1 inferInstance m hm)
  · have : IsConstructibleSheaf ((𝟭 _).obj F) := ‹_›
    exact IsConstructibleSheaf.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ m).app F).symm
  · exact IsConstructibleSheaf.of_isZero ((DerivedCategory.isLE_iff _ n).1 inferInstance m hm)

/-- The derived pullback `D(g^*)` of the exact functor `g^*` sends bounded constructible
complexes to bounded constructible complexes: `H^n(D(g^*) K) ≅ g^* H^n(K)` and the pullback of
a constructible sheaf is constructible. -/
lemma Etale.DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar {Y : Scheme.{u}}
    (g : Y ⟶ X) {K : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : Etale.DerivedCategory.boundedConstructible A X K) :
    Etale.DerivedCategory.boundedConstructible A Y
      ((Etale.upperStar A g).mapDerivedCategory.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
    have : IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj K) := hK.2 n
    have : IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ n ⋙
        Etale.upperStar A g).obj K) :=
      IsConstructibleSheaf.upperStar (FA := FA) (CA := CA) _ _
    IsConstructibleSheaf.of_iso ((Functor.mapDerivedCategoryHomologyFunctorIso _ n).app K)⟩

variable (A X)

variable [(Etale.constructibleSheaf A X).IsClosedUnderKernels]
  [(Etale.constructibleSheaf A X).IsClosedUnderCokernels]
  [(Etale.constructibleSheaf A X).IsClosedUnderExtensions]
  [PreservesFiniteLimits (CategoryTheory.forget A)]

/-- Blueprint `corollary-ambient-ind-derived--1`, first assertion: **Complexes with
constructible homology form a triangulated subcategory**, provided the
constructible sheaves are closed under kernels, cokernels and extensions
(blueprint: `thm:constructible-serre`). (blueprint: `prop:constructible-derived-subcategory`) -/
instance Etale.DerivedCategory.constructibleHomology_isTriangulated :
    (Etale.DerivedCategory.constructibleHomology A X).IsTriangulated := by
  rw [Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

/-- Blueprint `corollary-ambient-ind-derived--1`: **`Dᵇc(X, A)` is a triangulated
subcategory of `D(X_ét)`**, provided the constructible
sheaves are closed under kernels, cokernels and extensions (blueprint:
`thm:constructible-serre`). (blueprint: `prop:constructible-derived-subcategory`) -/
instance Etale.DerivedCategory.boundedConstructible_isTriangulated :
    (Etale.DerivedCategory.boundedConstructible A X).IsTriangulated :=
  inferInstanceAs (DerivedCategory.TStructure.t.bounded ⊓
    Etale.DerivedCategory.constructibleHomology A X).IsTriangulated

end Triangulated

section ModuleCat

variable {Λ : Type (u + 1)} [Ring Λ]

/-- Constructible sheaves of `Λ`-modules over a noetherian ring are closed under kernels. -/
instance [IsNoetherianRing Λ] :
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.1
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.2
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      ((Etale.constructibleSheaf_iff _ _ _).mpr (IsConstructibleSheaf.kernel f))

/-- Constructible sheaves of `Λ`-modules are closed under cokernels. -/
instance : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.1
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.2
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      ((Etale.constructibleSheaf_iff _ _ _).mpr (IsConstructibleSheaf.cokernel f))

/-- Constructible sheaves of `Λ`-modules are closed under binary products: the product is the
direct sum, which is constructible by `IsConstructibleSheaf.biprod`. -/
instance : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro _ ⟨p, hp⟩
    have := (Etale.constructibleSheaf_iff _ _ _).mp (hp ⟨.left⟩)
    have := (Etale.constructibleSheaf_iff _ _ _).mp (hp ⟨.right⟩)
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_iso
      ((biprod.isoProd _ _ ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair p.diag)).symm ≪≫
        (p.isLimit.conePointUniqueUpToIso (limit.isLimit p.diag)).symm))
      ((Etale.constructibleSheaf_iff _ _ _).mpr (IsConstructibleSheaf.biprod _ _))

/-- Constructible sheaves of `Λ`-modules are closed under finite products: they contain zero
and are closed under binary products. -/
instance : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderFiniteProducts :=
  .mk'

/-- Constructible sheaves of modules over a finite ring are closed under extensions
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact`). -/
instance [Finite Λ] :
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have := (Etale.constructibleSheaf_iff _ _ _).mp h₁
    have := (Etale.constructibleSheaf_iff _ _ _).mp h₃
    exact (Etale.constructibleSheaf_iff _ _ _).mpr (IsConstructibleSheaf.of_shortExact hS)

/-- `Dᵇc(X, Λ)` is stable under retracts, for a noetherian ring `Λ`: the homology sheaves of a
retract are retracts of constructible sheaves (`IsConstructibleSheaf.of_retract`). -/
instance [IsNoetherianRing Λ] :
    (Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).IsStableUnderRetracts where
  of_retract {M N} e := by
    rintro ⟨hb, hc⟩
    obtain ⟨a, b, hab⟩ := (DerivedCategory.exists_homologyConcentratedIn_iff_bounded N).2 hb
    exact ⟨(DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).1
      ⟨a, b, (DerivedCategory.homologyConcentratedIn a b).prop_of_retract e hab⟩,
      fun n ↦ have := hc n; IsConstructibleSheaf.of_retract
        (e.map (DerivedCategory.homologyFunctor _ n))⟩

end ModuleCat

end AlgebraicGeometry
