import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicEisensteinRightTranslation
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Linear Eisenstein summation with compact majorants -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)

local notation "Points" => AdelicGroupPoints F G
local notation "Cosets" => ParabolicRationalCosets F p
local notation "Sections" => (Points → ℂ)

private def termLinear (x : Points) (c : Cosets) : Sections →ₗ[ℂ] ℂ :=
  (LinearMap.proj (((Quotient.out c : rationalSubgroup F G) : Points) * x)).comp
    (hK.parameterTwistEquiv lam).toLinearMap

/-- Scalar sections whose Eisenstein terms admit a summable majorant on
each compact set at the fixed parameter. -/
def compactMajorantSections : Submodule ℂ Sections where
  carrier := {φ | ∀ C : Set Points, IsCompact C →
    ∃ u : Cosets → ℝ, Summable u ∧ ∀ c x, x ∈ C → ‖hK.eisensteinTerm φ lam x c‖ ≤ u c}
  zero_mem' := by
    intro C hC
    refine ⟨0, summable_zero, fun c x _ => ?_⟩
    change ‖hK.termLinear lam x c 0‖ ≤ 0
    rw [map_zero, norm_zero]
  add_mem' {φ ψ} hφ hψ := by
    intro C hC
    obtain ⟨u, hu, hbu⟩ := hφ C hC
    obtain ⟨v, hv, hbv⟩ := hψ C hC
    refine ⟨u + v, hu.add hv, fun c x hx => ?_⟩
    change ‖hK.termLinear lam x c (φ + ψ)‖ ≤ u c + v c
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hbu c x hx) (hbv c x hx))
  smul_mem' z φ hφ := by
    intro C hC
    obtain ⟨u, hu, hbu⟩ := hφ C hC
    refine ⟨fun c => ‖z‖ * u c, hu.mul_left _, fun c x hx => ?_⟩
    change ‖hK.termLinear lam x c (z • φ)‖ ≤ ‖z‖ * u c
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hbu c x hx) (norm_nonneg _)

omit [IsAffine G.X.left] in
theorem summable_eisensteinTerm_of_mem_compactMajorantSections
    {φ : Sections} (hφ : φ ∈ hK.compactMajorantSections lam) (x : Points) :
    Summable (fun c => hK.eisensteinTerm φ lam x c) := by
  obtain ⟨u, hu, hbu⟩ := hφ {x} isCompact_singleton
  exact hu.of_norm_bounded fun c => hbu c x (Set.mem_singleton x)

/-- On sections with compact majorants, the ordinary Eisenstein sum is linear. -/
def eisensteinSeriesLinear : hK.compactMajorantSections lam →ₗ[ℂ] Sections where
  toFun φ := hK.eisensteinSeries φ.val lam
  map_add' φ ψ := by
    funext x
    change (∑' c, hK.termLinear lam x c (φ.val + ψ.val)) =
      (∑' c, hK.termLinear lam x c φ.val) + ∑' c, hK.termLinear lam x c ψ.val
    simp only [map_add]
    exact (hK.summable_eisensteinTerm_of_mem_compactMajorantSections lam φ.property x).tsum_add
      (hK.summable_eisensteinTerm_of_mem_compactMajorantSections lam ψ.property x)
  map_smul' z φ := by
    funext x
    change (∑' c, hK.termLinear lam x c (z • φ.val)) =
      z • ∑' c, hK.termLinear lam x c φ.val
    simp only [map_smul]
    exact (hK.summable_eisensteinTerm_of_mem_compactMajorantSections lam φ.property x).tsum_const_smul z

variable {M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- A finite family of automorphic sections has a common convergence
threshold. At every sufficiently regular parameter all their linear
combinations lie in the compact-majorant domain. -/
theorem exists_regular_compactMajorantSections
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hmax : IsMaximalCompactSubgroup F G K) {N d n : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
    {I : Type*} [Finite I] (φ : I → Sections)
    (hφ : ∀ j, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho (φ j)) :
    ∃ R : ℝ, ∀ t : Fin n → ℂ, r.IsRegularParameter hA hT R (e t) →
      Submodule.span ℂ (Set.range φ) ≤ hK.compactMajorantSections (e t) := by
  choose R hR using fun (j : I) => eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT
    hG hU K hK rho hsmooth hcalc (φ j) hmax hrho (hφ j)
  obtain ⟨S, hS⟩ := (Set.finite_range R).bddAbove
  refine ⟨S, fun t ht => Submodule.span_le.mpr ?_⟩
  rintro _ ⟨j, rfl⟩ C hC
  have hj : r.IsRegularParameter hA hT (R j) (e t) :=
    fun α hα => (hS (Set.mem_range_self j)).trans_lt (ht α hα)
  obtain ⟨b, hb, hbound⟩ := hR j C hC n e {t} isCompact_singleton
    (fun s hs => (Set.mem_singleton_iff.mp hs).symm ▸ hj)
  exact ⟨b, hb, fun c x hx => hbound c x hx t (Set.mem_singleton t)⟩

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact
