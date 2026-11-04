import Langlands.Geometry.Building.IntegerValuation
import Langlands.Geometry.Building.KPCentralizerCompatibility

/-! # Integer-valued centralizer valuation and full V6 adapters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building.IntegerValuation

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  (v : Valuation k (WithZero (Multiplicative ℤ)))

/-- Positive centralizer valuation transported through actual character restriction. -/
def centralizerValuation (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    rationalPoints Z →* Multiplicative (V S) :=
  (AddMonoidHom.toMultiplicative
    (LinearEquiv.ofBijective (Cartan.restrictionEvaluation s) h).symm.toAddMonoidHom).comp
      (realCharacterValuation v Z)

theorem centralizerValuation_spec (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) (z : rationalPoints Z)
    (χ : rationalCharacters Z) :
    eval S (Cartan.characterRestriction s χ) (centralizerValuation v s h z).toAdd =
      order v (rationalCharacterEval χ z) := by
  have he := (LinearEquiv.ofBijective (Cartan.restrictionEvaluation s) h).apply_symm_apply
    (realCharacterValuation v Z z).toAdd
  exact DFunLike.congr_fun he χ

theorem centralizerValuation_ker (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    (centralizerValuation v s h).ker = characterValuationKernel v Z := by
  rw [centralizerValuation, MonoidHom.ker_comp_of_injective _ _
    (LinearEquiv.ofBijective (Cartan.restrictionEvaluation s) h).symm.injective,
    realCharacterValuation_ker]

/-- KP apartment translation is the negative of the positive centralizer valuation. -/
def centralizerTranslation (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    rationalPoints Z →* Multiplicative (V S) :=
  (centralizerValuation v s h)⁻¹

theorem centralizerTranslation_toAdd (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) (z : rationalPoints Z) :
    (centralizerTranslation v s h z).toAdd = -(centralizerValuation v s h z).toAdd := rfl

theorem eval_centralizerTranslation (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) (z : rationalPoints Z)
    (χ : rationalCharacters Z) :
    eval S (Cartan.characterRestriction s χ) (centralizerTranslation v s h z).toAdd =
      -order v (rationalCharacterEval χ z) := by
  rw [centralizerTranslation_toAdd, map_neg, centralizerValuation_spec]

theorem centralizerTranslation_ker (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    (centralizerTranslation v s h).ker = characterValuationKernel v Z := by
  ext z
  rw [MonoidHom.mem_ker, ← centralizerValuation_ker v s h, MonoidHom.mem_ker]
  exact inv_eq_one

section Compatibility

variable (i : S.toGrp ⟶ G) [IsAffineHom G.X.hom] (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
  (h : Function.Bijective (Cartan.restrictionEvaluation s))

/-- Full V6 on actual centralizer points for the supplied root-function family. -/
def IsCentralizerCompatible (φ : RootFunctionFamily S G) : Prop :=
  ∀ a ∈ relativeRoots i, ∀ z : rationalPoints Z, ∀ u ∈ rootGroupPoints i a,
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u + ((eval S a (centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ)

variable {v i j s h}

theorem IsCentralizerCompatible.vadd {φ : RootFunctionFamily S G}
    (hφ : IsCentralizerCompatible v i j s h φ) (w : V S) :
    IsCentralizerCompatible v i j s h (w +ᵥ φ) := by
  intro a ha z u hu
  rw [RootFunctionFamily.vadd_apply, RootFunctionFamily.vadd_apply, hφ a ha z u hu,
    add_right_comm]

variable [Mono i.hom.hom.left]

theorem IsCentralizerCompatible.smul_eq_vadd (hj : (torusCentralizer i).IsRepresentedBy j)
    {φ : RootFunctionFamily S G} (hv : IsRootDatumValuation i φ)
    (hφ : IsCentralizerCompatible v i j s h φ) (z : rationalPoints Z) :
    centralizerToNormalizer i j hj z • φ = (centralizerTranslation v s h z).toAdd +ᵥ φ := by
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

end Compatibility

section Apartment

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (order v)) (C : CentralizerDatum i)

/-- The same supplied equipollence class satisfies V6 on its actual centralizer. -/
def IsOmegaCompatible : Prop :=
  ∀ φ ∈ D.carrier, IsCentralizerCompatible v i C.j C.s C.bijective φ

variable {v D C}

theorem isOmegaCompatible_iff_of_mem {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier) :
    IsOmegaCompatible v D C ↔ IsCentralizerCompatible v i C.j C.s C.bijective φ := by
  refine ⟨fun hD => hD φ hφ, fun hc ψ hψ => ?_⟩
  obtain ⟨w, rfl⟩ := D.equipollent_of_mem hφ hψ
  exact hc.vadd w

/-- V6 identifies the existing normalizer action with the negative valuation translation. -/
theorem IsOmegaCompatible.smul_eq_vadd (hD : IsOmegaCompatible v D C)
    (z : rationalPoints C.Z) (x : D.Apartment) :
    C.toNormalizer z • x =
      (Submodule.Quotient.mk (centralizerTranslation v C.s C.bijective z).toAdd :
        TranslationSpace i) +ᵥ x :=
  KPApartmentData.Apartment.ext
    ((hD x.val x.mem).smul_eq_vadd C.isRepresentedBy x.isValuation z)

theorem IsOmegaCompatible.smul_eq_self (hD : IsOmegaCompatible v D C)
    {z : rationalPoints C.Z} (hz : z ∈ characterValuationKernel v C.Z) (x : D.Apartment) :
    C.toNormalizer z • x = x := by
  rw [hD.smul_eq_vadd z x]
  rw [← centralizerTranslation_ker v C.s C.bijective, MonoidHom.mem_ker] at hz
  rw [hz, toAdd_one, Submodule.Quotient.mk_zero, zero_vadd]

theorem IsOmegaCompatible.map_mem_reducedFixer (hD : IsOmegaCompatible v D C)
    {z : rationalPoints C.Z} (hz : z ∈ characterValuationKernel v C.Z) (x : D.Apartment) :
    rationalPoints.map C.j z ∈ D.reducedFixer (D.apartmentMap x) := by
  rw [D.mem_reducedFixer, ← coe_centralizerToNormalizer C.isRepresentedBy,
    ← D.apartmentMap_smul, hD.smul_eq_self hz x]

end Apartment

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Equality with the exact real unit order of the existing KP local wrapper. -/
theorem order_normalized :
    order (FML.normalizedMultiplicativeValuation F) = localFieldOrder F := by
  funext a
  unfold order localFieldOrder
  rw [orderUnits_normalized]

theorem centralizerValuation_normalized
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {Z : GroupScheme (Spec (CommRingCat.of F))} (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    centralizerValuation (FML.normalizedMultiplicativeValuation F) s h =
      Cartan.centralizerValuation s h := by
  unfold centralizerValuation Cartan.centralizerValuation
  rw [realCharacterValuation_normalized]

theorem centralizerTranslation_normalized
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {Z : GroupScheme (Spec (CommRingCat.of F))} (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) :
    centralizerTranslation (FML.normalizedMultiplicativeValuation F) s h =
      Building.centralizerTranslation s h := by
  unfold centralizerTranslation Building.centralizerTranslation
  rw [centralizerValuation_normalized]

theorem isCentralizerCompatible_normalized
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G Z : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) (φ : RootFunctionFamily S G) :
    IsCentralizerCompatible (FML.normalizedMultiplicativeValuation F) i j s h φ ↔
      Building.IsCentralizerCompatible i j s h φ := by
  unfold IsCentralizerCompatible Building.IsCentralizerCompatible
  rw [centralizerTranslation_normalized]

end LocalField

end Langlands.Geometry.Building.IntegerValuation
