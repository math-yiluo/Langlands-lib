/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.Mathlib.SetTheory.Cardinal.Finite
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Finite.GlobalSections

/-!

# Cohomology of the affine line with coefficients in an Artin–Schreier sheaf

Let `k` be a finite field with `q` elements, `Ω` an algebraically closed field containing `k`,
`Λ` a finite coefficient ring in which `q` is invertible, and `Ψ` a primitive additive
character of `k` with values in `Λ`. On the affine line `𝔸¹_Ω`, viewed as a `k`-scheme, the
Artin–Schreier sheaf `ℒ_{Ψ, a x}` of the linear function `x ↦ a x` has no cohomology at all
when `a ≠ 0`, while for `a = 0` it is the constant sheaf, whose cohomology is `Λ` in degree
`0` and vanishes in the other degrees.

## Main statements

- `AlgebraicGeometry.Etale.cohomology_affineLine_unit`: `H^0(𝔸¹_Ω, Λ) ≅ Λ` and
  `H^q(𝔸¹_Ω, Λ) = 0` for `q ≠ 0`.
- `AlgebraicGeometry.Etale.isZero_cohomology_affineLine_artinSchreierSheafOf`: for `a ≠ 0`,
  `H^q(𝔸¹_Ω, ℒ_{Ψ, a x}) = 0` for every `q`.
- `AlgebraicGeometry.Etale.cohomology_affineLine_artinSchreierSheafOf`: the cohomology of
  `ℒ_{Ψ, a x}` on `𝔸¹_Ω` for every `a`.

## Implementation notes

The cohomology `H^q(X, F)` of an étale sheaf `F` of `Λ`-modules is
`AlgebraicGeometry.Etale.cohomology` applied to `F` placed in degree `0`, the `q`-th cohomology
of the derived global sections `RΓ(X, F)`.
The blueprint works with `ℚ̄_ℓ`-coefficients; here the coefficients are a finite domain `Λ` in
which `q` is invertible, a finite level of the `ℓ`-adic coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The affine line `𝔸¹_Ω` over a field extension `Ω` of `k`, as a `k`-scheme. -/
@[instance_reducible]
def affineLineOverOfAlgebra (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] :
    (𝔸(PUnit; Spec (CommRingCat.of Ω))).Over (Spec (.of k)) :=
  ⟨𝔸(PUnit; Spec (CommRingCat.of Ω)) ↘ Spec (.of Ω) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩

variable (Λ) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- **Constant cohomology of the affine line.** For an algebraically closed field `Ω` of
characteristic `p` and a finite coefficient ring `Λ` in which `p` is invertible,
`H^0(𝔸¹_Ω, Λ) ≅ Λ` and `H^q(𝔸¹_Ω, Λ) = 0` for `q ≠ 0`: the affine line is connected, its
cohomological dimension is one, and `H^1(𝔸¹_Ω, ℤ/n) ≅ Pic(𝔸¹_Ω)[n] = 0` for `n` prime to `p`.
(blueprint: `lemma-integral-linear-character--2`) -/
theorem cohomology_affineLine_unit [Finite Λ] (p : ℕ) [CharP Ω p] [Invertible (p : Λ)] :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≅ ModuleCat.of Λ Λ) ∧
      ∀ q : ℤ, q ≠ 0 →
        IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj
          ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) := by
  -- `H^0` is `Λ` as `𝔸¹_Ω` is connected; `H^q = 0` for `q ≥ 2` by the cohomological dimension
  -- of an affine curve (`theorem-cohomology-curves--2`); and
  -- `H^1 = 0` by the Kummer sequence (`proposition-cohomology-smooth-affine-curve--2`), the units
  -- of `Ω[x]` being divisible and `Pic(𝔸¹_Ω) = 0`
  -- (`proposition-cohomology-smooth-affine-curve--3`). Here these facts enter through the
  -- acyclicity `Rp_* Λ ≅ Λ` of the affine line of the purity chapter
  -- (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_affineLine`).
  have := HasInvertibleExponent.spec_of_charP Λ (Ω := Ω) p
  let S := Spec (CommRingCat.of Ω)
  -- `𝔸¹_Ω = 𝔸(PUnit; S)` is isomorphic to the affine line `𝔸(ULift (Fin 1); S)` of the purity
  -- chapter, on which `Rp_* Λ ≅ Λ_S`; so `RΓ(𝔸¹_Ω, Λ) ≅ RΓ(S, Rp_* Λ) ≅ RΓ(S, Λ)`
  let E : 𝔸(PUnit; S) ≅ 𝔸(ULift.{u} (Fin 1); S) :=
    AffineSpace.reindexIso S (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)
  obtain ⟨eR⟩ := nonempty_iso_rightDerivedLowerStar_affineLine Λ (𝟙 S)
  let e : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) 𝔸(PUnit; S)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S).obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) :=
    (rightDerivedGlobalSections _ _).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso (E.hom)^*[_]) ≪≫
          ((((E.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app
            (𝟙_ _)).symm) ≪≫
      (upperStarCompRightDerivedGlobalSectionsIso _ E).app _ ≪≫
      (rightDerivedGlobalSections _ _).mapIso (constantComplexIsoSingleFunctor Λ _).symm ≪≫
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _
        (𝔸(ULift.{u} (Fin 1); S) ↘ S)).app _).symm ≪≫
      (rightDerivedGlobalSections _ S).mapIso (eR ≪≫ constantComplexIsoSingleFunctor Λ S)
  -- `Ω` is separably closed, so `RΓ(S, Λ)` is `Γ(S, Λ) = Λ` in degree `0`
  obtain ⟨⟨e₀⟩, hq⟩ := cohomology_singleFunctor_of_isSepClosed Ω Λ (𝟙_ _)
  let E' (q : ℤ) := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).mapIso e
  exact ⟨⟨E' 0 ≪≫ e₀ ≪≫ Scheme.globalSectionsUnitIsoOfIsSepClosed Ω Λ⟩,
    fun q hq0 ↦ (hq q hq0).of_iso (E' q)⟩

variable {k : Type u} [Field k] [Fintype k] [Algebra k Ω] [Invertible (Fintype.card k : Λ)]

omit [IsAlgClosed Ω] in
/-- For `k = Ω`, the structure morphism of `affineLineOverOfAlgebra` is the canonical one. -/
lemma over_affineLineOverOfAlgebra_self :
    @CategoryTheory.over _ _ 𝔸(PUnit; Spec (CommRingCat.of Ω)) (Spec (.of Ω))
      (affineLineOverOfAlgebra Ω Ω) = 𝔸(PUnit; Spec (CommRingCat.of Ω)) ↘ Spec (.of Ω) := by
  simp [affineLineOverOfAlgebra]
  rfl

attribute [local instance] affineLineOverOfAlgebra

/-- The linear function `x ↦ a x` on `𝔸¹_Ω`, for `a ∈ k`. -/
abbrev affineLineLinearFunction (a : k) : Γ(𝔸(PUnit; Spec (CommRingCat.of Ω)), ⊤) :=
  (𝔸(PUnit; Spec (CommRingCat.of Ω)) ↘ Spec (.of Ω)).appTop
      ((Scheme.ΓSpecIso (.of Ω)).inv.hom (algebraMap k Ω a)) *
    AffineSpace.coord _ PUnit.unit

omit [IsAlgClosed Ω] [Fintype k] in
/-- The linear function `x ↦ a x` on `𝔸¹_Ω`, as a morphism to `𝔸¹_k`, is the base change map
`𝔸¹_Ω ⟶ 𝔸¹_k` followed by the scaling `[a]` of `𝔸¹_k`. -/
lemma homOfVector_affineLineLinearFunction (a : k) :
    AffineSpace.homOfVector (𝔸(PUnit; Spec (CommRingCat.of Ω)) ↘ Spec (.of k))
      (fun _ ↦ affineLineLinearFunction a) =
    AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≫
      AffineSpace.smul PUnit (Spec (.of k)) ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · simp
    rfl
  · simp only [affineLineLinearFunction, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.smul_appTop_coord, map_mul, AffineSpace.homOfVector_appTop_coord,
      AffineSpace.map_appTop_coord]
    congr 1
    have h₁ := congr(ConcreteCategory.hom (Scheme.Hom.appTop
      $(AffineSpace.map_over (n := PUnit) (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
        ((Scheme.ΓSpecIso (.of k)).inv.hom a))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h₁
    have h₂ := congr(ConcreteCategory.hom
      $(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k Ω))) a)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h₂
    rw [h₁, ← h₂, over_affineLineOverOfAlgebra_self]
    rfl

omit [IsAlgClosed Ω] in
/-- For `a ≠ 0`, the Artin–Schreier sheaf `ℒ_{Ψ, a x}` on `𝔸¹_Ω` is the pullback of
`ℒ_{Ψ(a ·)}` along the base change map `𝔸¹_Ω ⟶ 𝔸¹_k`, as `[a]^* ℒ_Ψ ≅ ℒ_{Ψ(a ·)}`
(`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_smul`). -/
theorem nonempty_iso_artinSchreierSheafOf_affineLineLinearFunction (Ψ : AddChar k Λ) {a : k}
    (ha : a ≠ 0) :
    Nonempty (artinSchreierSheafOf 𝔸(PUnit; Spec (CommRingCat.of Ω)) Ψ
        (affineLineLinearFunction a) ≅
      (AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))^*[_].obj
        (artinSchreierSheaf (Ψ.mulShift a))) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_smul Ψ (Units.mk0 a ha)
  rw [Units.val_mk0] at e
  exact ⟨(upperStarComp _ _ _ _ (homOfVector_affineLineLinearFunction a)).app _ ≪≫
    (AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))^*[_].mapIso e⟩

omit [IsAlgClosed Ω] in
attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **The cohomology of `𝔸¹_Ω` splits along the characters of `k`.** For a primitive character
`Ψ` with values in a domain `Λ`, `⨁_{b ∈ k} H^q(𝔸¹_Ω, g^* ℒ_{Ψ(b ·)}) ≅ H^q(𝔸¹_Ω, Λ)`, where
`g : 𝔸¹_Ω ⟶ 𝔸¹_k` is the base change map: the isotypic decomposition
`(AS_q)_* Λ ≅ ⨁_b ℒ_{Ψ(b ·)}` pulls back along `g` to a decomposition of the pushforward of `Λ`
along the Artin–Schreier map of `𝔸¹_Ω` (finite base change), whose cohomology is that of `Λ`
(finite pushforward). -/
theorem nonempty_iso_biproduct_cohomology_affineLine [IsDomain Λ] (Ψ : AddChar k Λ)
    (hΨ : Ψ.IsPrimitive) (q : ℤ) :
    Nonempty ((⨁ fun b : k ↦ (cohomology (ModuleCat.{u + 1} Λ)
        𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))^*[_].obj
            (artinSchreierSheaf (Ψ.mulShift b))))) ≅
      (cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) := by
  let g := AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  let π := AffineSpace.artinSchreierMap PUnit (Spec (.of Ω)) (Fintype.card k)
  have sq := AffineSpace.isPullback_map_artinSchreierMap (n := PUnit)
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (Fintype.card k)
  have : IsFinite π := isFinite_of_isPullback sq
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) sq
  let G := (g)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.singleFunctor _ 0 ⋙
    cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q
  have : G.Additive := by
    unfold G cohomology
    infer_instance
  -- finite base change: `g^* (AS_q)_* Λ ≅ π_* g^* Λ ≅ π_* Λ`
  let e₁ : (g)^*[ModuleCat.{u + 1} Λ].obj
      ((AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))_*[_].obj (𝟙_ _)) ≅
      (π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _) :=
    asIso ((Etale.baseChangeMap _ sq.toCommSq).app (𝟙_ _)) ≪≫
      (π)_*[_].mapIso (Functor.Monoidal.εIso (g)^*[ModuleCat.{u + 1} Λ]).symm
  -- finite pushforward: `RΓ(𝔸¹_Ω, π_* Λ) ≅ RΓ(𝔸¹_Ω, Λ)`
  let e₂ : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
      𝔸(PUnit; Spec (CommRingCat.of Ω))).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω))).obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) :=
    (rightDerivedGlobalSections _ _).mapIso
      ((((π)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app (𝟙_ _)).symm ≪≫
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ π).app _
  exact ⟨(G.mapBiproduct (fun b ↦ artinSchreierSheaf (Ψ.mulShift b))).symm ≪≫
    G.mapIso (artinSchreierPushforwardIsoBiproduct Ψ hΨ).symm ≪≫
    (DerivedCategory.singleFunctor _ 0 ⋙
      cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q).mapIso e₁ ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e₂⟩

/-- **Vanishing of the cohomology of a nontrivial Artin–Schreier sheaf on the affine line.**
For a primitive additive character `Ψ` of `k` with values in a finite domain `Λ` and `a ≠ 0`,
`H^q(𝔸¹_Ω, ℒ_{Ψ, a x}) = 0` for every `q`. The scaling `x ↦ a x` identifies `ℒ_{Ψ, a x}` with
`ℒ_{Ψ(a ·), x}`, and `Ψ(a ·)` is a nontrivial character; by the finite pushforward along the
Artin–Schreier covering `y ↦ y ^ q - y` and the isotypic decomposition, the cohomology of
`𝔸¹_Ω` with constant coefficients is the direct sum of the cohomology of the `ℒ_{Ψ(b ·), x}`,
and only the trivial character contributes, in degree `0`. -/
theorem isZero_cohomology_affineLine_artinSchreierSheafOf [IsDomain Λ] [Finite Λ]
    (Ψ : AddChar k Λ) (hΨ : Ψ.IsPrimitive) {a : k} (ha : a ≠ 0) (q : ℤ) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a)))) := by
  classical
  obtain ⟨eL⟩ := nonempty_iso_artinSchreierSheafOf_affineLineLinearFunction Λ (Ω := Ω) Ψ ha
  refine IsZero.of_iso ?_
    ((cohomology _ _ q).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eL))
  -- `M b = H^q(𝔸¹_Ω, g^* ℒ_{Ψ(b ·)})`, with `⨁_b M b ≅ H^q(𝔸¹_Ω, Λ)`
  let M := fun b : k ↦ (cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))^*[_].obj
        (artinSchreierSheaf (Ψ.mulShift b))))
  have := Abelian.hasFiniteBiproducts (C := ModuleCat.{u + 1} Λ)
  obtain ⟨E⟩ := nonempty_iso_biproduct_cohomology_affineLine Λ (Ω := Ω) Ψ hΨ q
  -- the characteristic of `Ω` is that of `k`, invertible in `Λ`
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  have := Fact.mk hp
  have : CharP Ω (ringChar k) := charP_of_injective_algebraMap (algebraMap k Ω).injective _
  have hu : IsUnit ((ringChar k : Λ) ^ (m : ℕ)) := by
    rw [← Nat.cast_pow, ← hm]
    exact isUnit_of_invertible _
  let : Invertible (ringChar k : Λ) := ((isUnit_pow_iff m.ne_zero).mp hu).invertible
  obtain ⟨⟨e₀⟩, hq⟩ := cohomology_affineLine_unit (Ω := Ω) Λ (ringChar k)
  by_cases hq0 : q = 0
  · -- `H^0(𝔸¹_Ω, Λ) ≅ Λ ≅ ∏_b M b` with `M 0 ≅ Λ` finite, so the other factors vanish
    subst hq0
    obtain ⟨e₁⟩ := nonempty_iso_artinSchreierSheaf_one (k := k) (Λ := Λ)
    let eM : M 0 ≅ ModuleCat.of Λ Λ :=
      (cohomology _ _ 0).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        ((AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))^*[_].mapIso
          (eqToIso (congrArg artinSchreierSheaf (AddChar.mulShift_zero Ψ)) ≪≫ e₁) ≪≫
          (Functor.Monoidal.εIso _).symm)) ≪≫ e₀
    let P := (ModuleCat.piIsoPi.{u + 1, u, u + 1} M).symm ≪≫ (biproduct.isoProduct M).symm ≪≫
      E ≪≫ e₀
    have h : Nat.card (∀ b, M b) = Nat.card (M 0) :=
      (Nat.card_congr P.toLinearEquiv.toEquiv).trans
        (Nat.card_congr eM.toLinearEquiv.toEquiv).symm
    have h0 : Nat.card (M 0) ≠ 0 := by
      rw [Nat.card_congr eM.toLinearEquiv.toEquiv]
      exact Nat.card_pos.ne'
    have := Nat.subsingleton_of_card_pi_eq ha h h0
    exact ModuleCat.isZero_of_subsingleton _
  · exact IsZero.of_mono (biproduct.ι M a ≫ E.hom) (hq q hq0)

/-- **Cohomology of an affine line with an exponential sheaf.** Let `Ψ` be a primitive additive
character of `k` with values in a finite domain `Λ`, and `a ∈ k`. On `𝔸¹_Ω`,
`H^q(𝔸¹_Ω, ℒ_{Ψ, a x})` is `Λ` for `q = 0` and `a = 0`, and vanishes otherwise.
(blueprint: `lemma-integral-linear-character--2`) -/
theorem cohomology_affineLine_artinSchreierSheafOf [IsDomain Λ] [Finite Λ] (Ψ : AddChar k Λ)
    (hΨ : Ψ.IsPrimitive) (a : k) :
    (a ≠ 0 → ∀ q, IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω))
      q).obj ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a))))) ∧
    (a = 0 → Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω))
        0).obj ((DerivedCategory.singleFunctor _ 0).obj
          (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a))) ≅ ModuleCat.of Λ Λ) ∧
      ∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ)
        𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj ((DerivedCategory.singleFunctor _ 0).obj
          (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a))))) := by
  refine ⟨fun ha q ↦ isZero_cohomology_affineLine_artinSchreierSheafOf Λ Ψ hΨ ha q,
    fun ha ↦ ?_⟩
  subst ha
  -- `ℒ_{Ψ, 0} ≅ Λ`, and the characteristic of `Ω` is that of `k`, invertible in `Λ`
  rw [show affineLineLinearFunction (Ω := Ω) (0 : k) = 0 by simp]
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_zero 𝔸(PUnit; Spec (CommRingCat.of Ω)) Ψ
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  have := Fact.mk hp
  have : CharP Ω (ringChar k) := charP_of_injective_algebraMap (algebraMap k Ω).injective _
  have hu : IsUnit ((ringChar k : Λ) ^ (m : ℕ)) := by
    rw [← Nat.cast_pow, ← hm]
    exact isUnit_of_invertible _
  let : Invertible (ringChar k : Λ) := ((isUnit_pow_iff m.ne_zero).mp hu).invertible
  obtain ⟨⟨e₀⟩, hq⟩ := cohomology_affineLine_unit (Ω := Ω) Λ (ringChar k)
  let E (q : ℤ) := (cohomology (ModuleCat.{u + 1} Λ) _ q).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso e)
  exact ⟨⟨(E 0) ≪≫ e₀⟩, fun q hq0 ↦ (hq q hq0).of_iso (E q)⟩

end AlgebraicGeometry.Etale
