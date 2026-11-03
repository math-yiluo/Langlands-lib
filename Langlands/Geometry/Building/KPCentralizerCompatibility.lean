import Langlands.Geometry.Building.KPBuilding
import Langlands.BruhatTits.Cartan.CentralizerValuationConsequences

/-!
# Axiom V 6 on the actual centralizer `Z(k)` and its translation action

Let `F` be a nonarchimedean local field, `i : S → G` a split torus and `j : Z → G` a
homomorphism, with `s : S → Z`. When `j` represents the actual torus centralizer of `i`,
`Z(F)` is KP's `Z(k) = Z_G(S)(k)`. This module defines:

* KP's translation `ν(z) = -ω_Z(z)` of Axiom 4.1.4 (A 1), where `ω_Z` is the published
  positive centralizer valuation `Cartan.centralizerValuation s h`;
* the full axiom V 6 of KP Definition 6.1.2, `φ_a(z⁻¹ u z) = φ_a(u) + a(ν(z))` for all
  `z ∈ Z(F)`, for a single family and for valid apartment data;
* the homomorphism `Z(F) → N(F)` and the law `z · φ = φ + ν(z)` (KP Proposition 6.2.4);
* that `Z(F)^1` acts trivially on the apartment and lies in every `K_x`, `x ∈ A`;
* the bundled actual centralizer `CentralizerDatum i` and the predicate
  `KPApartmentData.IsOmegaCompatible D C` (KP's `ω`-compatibility).

The bijectivity of `Cartan.restrictionEvaluation s` is an explicit hypothesis. That it holds
for the actual centralizer of a maximal split torus is the separate published statement
target `Cartan.CentralizerValuationComparisonStatement`, which is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel Langlands.BruhatTits

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}

/-! ### The translation `ν : Z(F) → V(S)` -/

/-- KP's translation `ν(z) = -ω_Z(z)` of Axiom 4.1.4 (A 1), with `ω_Z` the published positive
valuation `Cartan.centralizerValuation s h` of `Z(F)` (corrected KP 2.6(d):
`χ(ω_Z(z)) = ω(χ(z))`). -/
def centralizerTranslation (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    rationalPoints Z →* Multiplicative (V S) :=
  (Cartan.centralizerValuation s h)⁻¹

theorem centralizerTranslation_toAdd (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) (z : rationalPoints Z) :
    (centralizerTranslation s h z).toAdd = -(Cartan.centralizerValuation s h z).toAdd :=
  rfl

/-- `χ(ν(z)) = -ω(χ(z))` for every rational character `χ` of `Z`. -/
theorem eval_centralizerTranslation (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) (z : rationalPoints Z)
    (χ : rationalCharacters Z) :
    eval S (Cartan.characterRestriction s χ) (centralizerTranslation s h z).toAdd =
      -((rationalCharacterValuation Z z).toAdd χ : ℝ) := by
  rw [centralizerTranslation_toAdd, map_neg, Cartan.centralizerValuation_spec]

/-- `ν` vanishes exactly on `Z(F)^1`. -/
theorem centralizerTranslation_ker (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    (centralizerTranslation s h).ker = rationalCommonNormKernel Z := by
  ext z
  rw [MonoidHom.mem_ker, ← Cartan.centralizerValuation_ker s h, MonoidHom.mem_ker]
  exact inv_eq_one

/-! ### Axiom V 6 -/

section Compatibility

variable (i : S.toGrp ⟶ G) [IsAffineHom G.X.hom] (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
  (h : Function.Bijective (Cartan.restrictionEvaluation s))

/-- KP axiom V 6 on the actual `Z(F)`: `φ_a(z⁻¹ u z) = φ_a(u) + a(ν(z))` for every root `a`,
`z ∈ Z(F)` and `u ∈ U_a(F)`, where `z` acts through `j` (KP Definition 6.1.2). -/
def IsCentralizerCompatible (φ : RootFunctionFamily S G) : Prop :=
  ∀ a ∈ relativeRoots i, ∀ z : rationalPoints Z, ∀ u ∈ rootGroupPoints i a,
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u + ((eval S a (centralizerTranslation s h z).toAdd : ℝ) : WithTop ℝ)

variable {i j s h}

/-- Translates of a V 6-compatible family are V 6-compatible. -/
theorem IsCentralizerCompatible.vadd {φ : RootFunctionFamily S G}
    (hφ : IsCentralizerCompatible i j s h φ) (v : V S) :
    IsCentralizerCompatible i j s h (v +ᵥ φ) := by
  intro a ha z u hu
  rw [RootFunctionFamily.vadd_apply, RootFunctionFamily.vadd_apply, hφ a ha z u hu,
    add_right_comm]

end Compatibility

/-! ### `Z(F)` inside `N(F)` -/

section Normalizer

variable {i : S.toGrp ⟶ G} {j : Z ⟶ G}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `j` represents the torus centralizer of `i`, then `j(z)` centralizes `i`. -/
theorem map_mem_centralizerPoints (hj : (torusCentralizer i).IsRepresentedBy j)
    (z : rationalPoints Z) : rationalPoints.map j z ∈ centralizerPoints i := by
  rw [← torusCentralizer_carrier_base, ← hj.2]
  exact ⟨z, rfl⟩

variable (i j) in
/-- The homomorphism `Z(F) → N(F)` induced by a representing homomorphism `j`. -/
def centralizerToNormalizer (hj : (torusCentralizer i).IsRepresentedBy j) :
    rationalPoints Z →* normalizerPoints i :=
  (rationalPoints.map j).codRestrict (normalizerPoints i) fun z =>
    centralizerPoints_le_normalizerPoints i (map_mem_centralizerPoints hj z)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem coe_centralizerToNormalizer (hj : (torusCentralizer i).IsRepresentedBy j)
    (z : rationalPoints Z) :
    (centralizerToNormalizer i j hj z : rationalPoints G) = rationalPoints.map j z :=
  rfl

variable [Mono i.hom.hom.left]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem weylAction_centralizerToNormalizer (hj : (torusCentralizer i).IsRepresentedBy j)
    (z : rationalPoints Z) : weylAction i (centralizerToNormalizer i j hj z) = 1 :=
  weylAction_eq_one_of_mem_centralizerPoints i (map_mem_centralizerPoints hj z)

variable [IsAffineHom G.X.hom] {s : S.toGrp ⟶ Z}
  {h : Function.Bijective (Cartan.restrictionEvaluation s)}

/-- Under V 6, `z ∈ Z(F)` acts on a valuation by the translation `ν(z)`:
`z · φ = φ + ν(z)` (KP Proposition 6.2.4). -/
theorem IsCentralizerCompatible.smul_eq_vadd (hj : (torusCentralizer i).IsRepresentedBy j)
    {φ : RootFunctionFamily S G} (hv : IsRootDatumValuation i φ)
    (hφ : IsCentralizerCompatible i j s h φ) (z : rationalPoints Z) :
    centralizerToNormalizer i j hj z • φ = (centralizerTranslation s h z).toAdd +ᵥ φ := by
  set n := centralizerToNormalizer i j hj z with hn
  have hw : weylAction i n⁻¹ = 1 := by
    rw [hn, ← map_inv]
    exact weylAction_centralizerToNormalizer hj z⁻¹
  ext a g
  rw [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hw, LinearEquiv.coe_one,
    id]
  by_cases ha : a ∈ relativeRoots i
  · by_cases hg : g ∈ rootGroupPoints i a
    · exact hφ a ha z g hg
    · have hg' : (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∉ rootGroupPoints i a := by
        intro hmem
        apply hg
        have hc := conj_mem_rootGroupPoints n hmem
        rwa [weylAction_centralizerToNormalizer hj z, LinearEquiv.coe_one, id,
          show (n : rationalPoints G) * ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G)) *
            (n : rationalPoints G)⁻¹ = g by group] at hc
      rw [hv.eq_top_of_not_mem a ha _ hg', hv.eq_top_of_not_mem a ha g hg, WithTop.top_add]
  · rw [hv.eq_top_of_not_mem_roots a ha, hv.eq_top_of_not_mem_roots a ha, WithTop.top_add]

end Normalizer

/-- `j` maps `Z(F)^1` into `G(F)^1`. -/
theorem map_mem_rationalCommonNormKernel (j : Z ⟶ G) {z : rationalPoints Z}
    (hz : z ∈ rationalCommonNormKernel Z) :
    rationalPoints.map j z ∈ rationalCommonNormKernel G := by
  rw [mem_rationalCommonNormKernel] at hz ⊢
  intro χ
  rw [← rationalCharacterEval_characterRestrict]
  exact hz _

/-! ### Valid apartment data satisfying V 6 -/

namespace KPApartmentData

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
  (h : Function.Bijective (Cartan.restrictionEvaluation s))

/-- The valid data `D` satisfy the full axiom V 6 on the actual `Z(F)` (KP Definition 6.1.2 and
the Chapter 7 hypothesis on `A(S)`). -/
def IsCentralizerCompatible : Prop :=
  ∀ φ ∈ D.carrier, Building.IsCentralizerCompatible i j s h φ

variable {D j s h}

/-- V 6 holds for the whole class `A` as soon as it holds for one of its valuations. -/
theorem isCentralizerCompatible_iff_of_mem {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier) :
    D.IsCentralizerCompatible j s h ↔ Building.IsCentralizerCompatible i j s h φ := by
  refine ⟨fun hD => hD φ hφ, fun hc ψ hψ => ?_⟩
  obtain ⟨v, rfl⟩ := D.equipollent_of_mem hφ hψ
  exact hc.vadd v

theorem Apartment.isCentralizerCompatible (hD : D.IsCentralizerCompatible j s h)
    (x : D.Apartment) : Building.IsCentralizerCompatible i j s h x.val :=
  hD x.val x.mem

/-- Under V 6, `z ∈ Z(F)` acts on the apartment by the translation by the class of `ν(z)`
(KP Axiom 4.1.4 (A 1) and Proposition 6.2.4). -/
theorem centralizerToNormalizer_smul (hD : D.IsCentralizerCompatible j s h)
    (hj : (torusCentralizer i).IsRepresentedBy j) (z : rationalPoints Z) (x : D.Apartment) :
    centralizerToNormalizer i j hj z • x =
      (Submodule.Quotient.mk (centralizerTranslation s h z).toAdd : TranslationSpace i) +ᵥ x :=
  Apartment.ext ((x.isCentralizerCompatible hD).smul_eq_vadd hj x.isValuation z)

/-- Under V 6, `Z(F)^1` acts trivially on the apartment (KP Axiom 4.1.4 (A 1)). -/
theorem centralizerToNormalizer_smul_eq_self (hD : D.IsCentralizerCompatible j s h)
    (hj : (torusCentralizer i).IsRepresentedBy j) {z : rationalPoints Z}
    (hz : z ∈ rationalCommonNormKernel Z) (x : D.Apartment) :
    centralizerToNormalizer i j hj z • x = x := by
  rw [centralizerToNormalizer_smul hD hj z x]
  rw [← centralizerTranslation_ker s h, MonoidHom.mem_ker] at hz
  rw [hz, toAdd_one, Submodule.Quotient.mk_zero, zero_vadd]

/-- Under V 6, `j(Z(F)^1) ⊆ K_x` for every point `x` of the apartment. -/
theorem map_mem_compactStabilizer (hD : D.IsCentralizerCompatible j s h)
    (hj : (torusCentralizer i).IsRepresentedBy j) {z : rationalPoints Z}
    (hz : z ∈ rationalCommonNormKernel Z) (x : D.Apartment) :
    rationalPoints.map j z ∈ D.compactStabilizer (D.apartmentMap x) := by
  rw [mem_compactStabilizer]
  refine ⟨map_mem_rationalCommonNormKernel j hz, ?_⟩
  rw [← coe_centralizerToNormalizer hj, ← apartmentMap_smul,
    centralizerToNormalizer_smul_eq_self hD hj hz x]

end KPApartmentData

/-! ### The bundled actual centralizer -/

variable (i : S.toGrp ⟶ G) in
/-- The actual centralizer `Z = Z_G(S)` of `i`, with the data used to define `ν`: a closed
subgroup `j : Z → G` representing the torus centralizer, a factorization `s ≫ j = i`, and the
bijectivity of `Cartan.restrictionEvaluation s`. These are the hypotheses of the published
`Cartan.CentralizerValuationComparisonStatement`, whose conclusion is the last field. -/
structure CentralizerDatum where
  /-- The centralizer group scheme `Z`. -/
  Z : GroupScheme (Spec (CommRingCat.of F))
  /-- The inclusion `Z → G`. -/
  j : Z ⟶ G
  /-- The factorization of `i` through `Z`. -/
  s : S.toGrp ⟶ Z
  isClosedSubgroup : IsClosedSubgroup j
  isRepresentedBy : (torusCentralizer i).IsRepresentedBy j
  comp_eq : s ≫ j = i
  bijective : Function.Bijective (Cartan.restrictionEvaluation s)

namespace CentralizerDatum

variable {i : S.toGrp ⟶ G} (C : CentralizerDatum i)

/-- KP's translation `ν : Z(F) → V(S)`, `ν(z) = -ω_Z(z)`. -/
abbrev translation : rationalPoints C.Z →* Multiplicative (V S) :=
  centralizerTranslation C.s C.bijective

/-- The homomorphism `Z(F) → N(F)`. -/
abbrev toNormalizer : rationalPoints C.Z →* normalizerPoints i :=
  centralizerToNormalizer i C.j C.isRepresentedBy

end CentralizerDatum

namespace KPApartmentData

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (C : CentralizerDatum i)

/-- The valid data `D` are `ω`-compatible in the sense of KP Definition 6.1.2: every
valuation of `A` satisfies the full axiom V 6 on the actual centralizer `C`. -/
abbrev IsOmegaCompatible : Prop :=
  D.IsCentralizerCompatible C.j C.s C.bijective

variable {D C}

/-- `z · x = x + ν(z)` for `z ∈ Z(F)` and `x ∈ A`. -/
theorem IsOmegaCompatible.smul_eq_vadd (hD : D.IsOmegaCompatible C) (z : rationalPoints C.Z)
    (x : D.Apartment) :
    C.toNormalizer z • x =
      (Submodule.Quotient.mk (C.translation z).toAdd : TranslationSpace i) +ᵥ x :=
  centralizerToNormalizer_smul hD C.isRepresentedBy z x

/-- `Z(F)^1` acts trivially on `A`. -/
theorem IsOmegaCompatible.smul_eq_self (hD : D.IsOmegaCompatible C) {z : rationalPoints C.Z}
    (hz : z ∈ rationalCommonNormKernel C.Z) (x : D.Apartment) : C.toNormalizer z • x = x :=
  centralizerToNormalizer_smul_eq_self hD C.isRepresentedBy hz x

/-- `j(Z(F)^1) ⊆ K_x` for every `x ∈ A`. -/
theorem IsOmegaCompatible.map_mem_compactStabilizer (hD : D.IsOmegaCompatible C)
    {z : rationalPoints C.Z} (hz : z ∈ rationalCommonNormKernel C.Z) (x : D.Apartment) :
    rationalPoints.map C.j z ∈ D.compactStabilizer (D.apartmentMap x) :=
  Building.KPApartmentData.map_mem_compactStabilizer hD C.isRepresentedBy hz x

end KPApartmentData

end Langlands.Geometry.Building
