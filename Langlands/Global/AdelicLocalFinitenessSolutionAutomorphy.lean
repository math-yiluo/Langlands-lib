import Langlands.Global.AdelicLocalFinitenessSolutionAutomorphyStatement
import Langlands.Global.AdelicLocalFinitenessCenterStabilityStatement
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInclusion

/-! # Solutions of `Ξ_main` are automorphic forms, as a reduction

Bernstein–Lapid, proof of Lemma 8.1 (number field case). A solution `f` of a Harish-Chandra
equation `∑_k b_k δ(h_k) f = c f` with `c ≠ 0` and left `K_∞`-finite kernels `h_k` is right
`K_∞`-finite, because `δ(h) f (x κ) = δ(h(κ⁻¹ ·)) f (x)`. Together with Theorem 7.2
(`UniformGrowthLocalFinitenessStatement`) and the `𝔷`-stability of the solution spaces
(`LocalFinitenessCenterStabilityStatement`), this gives `LocalFinitenessSolutionAutomorphyStatement`
(`localFinitenessSolutionAutomorphy_of`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

section Finite

variable (F G) in
/-- The functions on `G(𝔸)` whose right translates by `K_∞` span a finite-dimensional space
form a submodule. -/
def infiniteSubgroupFiniteSubmodule (K : Subgroup (InfiniteAdelicGroupPoints F G)) :
    Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {φ | IsInfiniteSubgroupFiniteFunction F G K φ}
  zero_mem' := by
    change FiniteDimensional ℂ (Submodule.span ℂ _)
    have : (Set.range fun k : K => fun g : AdelicGroupPoints F G =>
        (0 : AdelicGroupPoints F G → ℂ) (g * ofInfinite F G k)) ⊆ {0} := by
      rintro _ ⟨k, rfl⟩
      rfl
    exact Submodule.finiteDimensional_of_le
      ((Submodule.span_mono this).trans (by rw [Submodule.span_singleton_eq_bot.2 rfl]))
  add_mem' := by
    intro φ ψ hφ hψ
    change FiniteDimensional ℂ (Submodule.span ℂ _) at hφ hψ ⊢
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
      _ ≤ Submodule.span ℂ (Set.range fun k : K => fun g : AdelicGroupPoints F G =>
          φ (g * ofInfinite F G k)) ⊔ Submodule.span ℂ (Set.range fun k : K =>
          fun g : AdelicGroupPoints F G => ψ (g * ofInfinite F G k)))
    rintro _ ⟨k, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.subset_span ⟨k, rfl⟩)
  smul_mem' := by
    intro c φ hφ
    change FiniteDimensional ℂ (Submodule.span ℂ _) at hφ ⊢
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
      _ ≤ Submodule.span ℂ (Set.range fun k : K => fun g : AdelicGroupPoints F G =>
          φ (g * ofInfinite F G k)))
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)

omit [LocallyOfFiniteType G.X.hom] in
theorem mem_infiniteSubgroupFiniteSubmodule (K : Subgroup (InfiniteAdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) :
    φ ∈ infiniteSubgroupFiniteSubmodule F G K ↔ IsInfiniteSubgroupFiniteFunction F G K φ :=
  Iff.rfl

end Finite

section Convolution

/-- Right translation of a convolution moves to a left translation of the kernel:
`δ(h) f (x κ) = δ(h(κ⁻¹ ·)) f (x)`, by left invariance of Haar measure. -/
theorem rightConvolution_mul_right (h f : AdelicGroupPoints F G → ℂ)
    (x κ : AdelicGroupPoints F G) :
    rightConvolution F G h f (x * κ) = rightConvolution F G (fun g => h (κ⁻¹ * g)) f x := by
  unfold rightConvolution
  rw [← integral_mul_left_eq_self (fun g => h (κ⁻¹ * g) * f (x * g)) κ]
  simp only [inv_mul_cancel_left, mul_assoc]

/-- The convolution `δ(h) f` of a continuous function `f` with a continuous compactly
supported kernel `h` that is left `K_∞`-finite (i.e. `g ↦ h g⁻¹` is right `K_∞`-finite) is right
`K_∞`-finite. -/
theorem isInfiniteSubgroupFiniteFunction_rightConvolution
    (K : Subgroup (InfiniteAdelicGroupPoints F G)) {h f : AdelicGroupPoints F G → ℂ}
    (hc : Continuous h) (hs : HasCompactSupport h) (hf : Continuous f)
    (hK : IsInfiniteSubgroupFiniteFunction F G K (fun g => h g⁻¹)) :
    IsInfiniteSubgroupFiniteFunction F G K (rightConvolution F G h f) := by
  -- the left translates of `h`
  let S : Set (AdelicGroupPoints F G → ℂ) :=
    Set.range fun k : K => fun g => h ((ofInfinite F G k)⁻¹ * g)
  let inv : (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun g : AdelicGroupPoints F G => g⁻¹)
  have hS : Submodule.span ℂ S = (Submodule.span ℂ (Set.range fun k : K =>
      fun g : AdelicGroupPoints F G => (fun g => h g⁻¹) (g * ofInfinite F G k))).map inv := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    refine congrArg Set.range (funext fun k => funext fun g => ?_)
    simp [inv, LinearMap.funLeft_apply, mul_inv_rev]
  have hSfin : FiniteDimensional ℂ (Submodule.span ℂ S) := by
    rw [hS]
    change FiniteDimensional ℂ (Submodule.span ℂ _) at hK
    infer_instance
  -- every element of the span is continuous with compact support
  have hcs : ∀ ψ ∈ Submodule.span ℂ S, Continuous ψ ∧ HasCompactSupport ψ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨k, rfl⟩ := hψ
      exact ⟨hc.comp (continuous_const.mul continuous_id),
        hs.comp_homeomorph (Homeomorph.mulLeft _)⟩
    | zero => exact ⟨continuous_const, HasCompactSupport.zero⟩
    | add ψ χ _ _ hψ hχ => exact ⟨hψ.1.add hχ.1, hψ.2.add hχ.2⟩
    | smul c ψ _ hψ => exact ⟨continuous_const.mul hψ.1, hψ.2.smul_left⟩
  have hint : ∀ ψ ∈ Submodule.span ℂ S, ∀ x : AdelicGroupPoints F G,
      Integrable (fun g => ψ g * f (x * g)) (Measure.haar : Measure (AdelicGroupPoints F G)) :=
    fun ψ hψ x => ((hcs ψ hψ).1.mul (hf.comp (continuous_const.mul continuous_id)))
      |>.integrable_of_hasCompactSupport (hcs ψ hψ).2.mul_right
  -- convolution with `f` is linear on the span
  let Φ : Submodule.span ℂ S →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    { toFun := fun ψ => rightConvolution F G ψ.1 f
      map_add' := fun ψ χ => funext fun x => by
        simp only [rightConvolution, Submodule.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint ψ.1 ψ.2 x) (hint χ.1 χ.2 x)
      map_smul' := fun c ψ => funext fun x => by
        simp only [rightConvolution, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  change FiniteDimensional ℂ (Submodule.span ℂ _)
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ : _ ≤ LinearMap.range Φ)
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨_, Submodule.subset_span ⟨k, rfl⟩⟩, funext fun x =>
    (rightConvolution_mul_right h f x (ofInfinite F G k)).symm⟩

end Convolution

section Solutions

variable {Δ : Type u} {r n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
  {Ua : Δ → GroupScheme (Spec (CommRingCat.of F))} [∀ α, IsAffine (Ua α).X.left]
  {u : ∀ α, Ua α ⟶ G} [∀ α, IsClosedImmersion (u α).hom.hom.left]
  {a : Δ → AdelicGroupPoints F G} {z : Fin r → AdelicGroupPoints F G} {N d : ℕ}
  {rho : MatrixRepresentation G (Fin N)} {hN : 0 < N} {hrho : IsClosedSubgroup rho}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {R : ℝ} {L : Subgroup (FiniteAdelicGroupPoints F G)}

omit [LocallyOfFiniteType G.X.hom] in
/-- The function of an element of `𝔉^R_L` is continuous. -/
theorem continuous_toFun_uniformGrowth
    (v : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :
    Continuous (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v) :=
  (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val.property

/-- Bernstein–Lapid, proof of Lemma 8.1: a solution of `Ξ_main(s)` is right `K_∞`-finite when
the kernels of its Harish-Chandra equations are left `K_∞`-finite. Some `c i s` is nonzero, and
`f = (c i s)⁻¹ ∑_k b i k s δ(h i k) f`. -/
theorem LocalFinitenessData.isInfiniteSubgroupFiniteFunction_of_mem_solutions
    (X : LocalFinitenessData F G Δ r n W) (hX : X.IsAdmissible)
    (K : Subgroup (InfiniteAdelicGroupPoints F G))
    (hK : ∀ i k, IsInfiniteSubgroupFiniteFunction F G K (fun g => X.h i k g⁻¹)) (s : W)
    (v : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L)
    (hv : v ∈ X.solutions u a z rho hN hrho hsmooth hcalc R L s) :
    IsInfiniteSubgroupFiniteFunction F G K
      (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v) := by
  obtain ⟨i, hi⟩ := hX.2.2.2.1 s
  set φ := UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v with hφdef
  have hφ : φ = (X.c i s)⁻¹ • ∑ k, X.b i k s • rightConvolution F G (X.h i k) φ := by
    funext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [hv.1 i x, inv_mul_cancel_left₀ hi]
  rw [← mem_infiniteSubgroupFiniteSubmodule, hφ]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
  exact isInfiniteSubgroupFiniteFunction_rightConvolution K (hX.1 i k).1.1 (hX.1 i k).2.1
    (continuous_toFun_uniformGrowth v) (hK i k)

end Solutions

/-- Bernstein–Lapid, Lemma 8.1 ("if" direction for the solutions of `Ξ_main`), as a reduction:
`LocalFinitenessSolutionAutomorphyStatement` follows from Theorem 7.2
(`UniformGrowthLocalFinitenessStatement`) and the `𝔷`-stability of the solution spaces
(`LocalFinitenessCenterStabilityStatement`). -/
theorem localFinitenessSolutionAutomorphy_of
    (h72 : UniformGrowthLocalFinitenessStatement.{u})
    (hstab : LocalFinitenessCenterStabilityStatement.{u}) :
    LocalFinitenessSolutionAutomorphyStatement.{u} := by
  intro F _ _ G T _ _ _ iT ν hG hi hν Ua _ u _ t r z hdata N d rho hN hrho hsmooth hcalc n W X hX
    Kinf hK L hLo hLc R s v hv
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  -- Theorem 7.2 at `s`, at a growth exponent `R' ≥ R`
  obtain ⟨U, -, hsU, R₀, hR₀⟩ := h72 F G T iT ν hG hi hν Ua u t r z hdata rho hN hrho hsmooth
    hcalc n W X hX L hLo hLc s
  obtain ⟨m, ℓ, -, -, hrange⟩ := hR₀ (max R R₀) (le_max_right _ _)
  let E : Submodule ℂ (FinitePlotSmoothRationalFunctions F G) :=
    LinearMap.range ((uniformGrowthLevelSubmodule F G rho hsmooth hcalc (max R R₀) L).subtype ∘ₗ
      (ℓ s).toLinearMap)
  have hsol : ∀ w ∈ X.solutions u (fun α => map F T.toGrp G iT (t α))
      (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc R L s,
      (w : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val ∈ E := by
    intro w hw
    have hw' : UniformGrowthFrechetSpace.inclusion F G rho hsmooth hcalc hN hrho
        (le_max_left R R₀) le_rfl w ∈ X.solutions u (fun α => map F T.toGrp G iT (t α))
          (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc (max R R₀) L s := by
      refine ⟨fun i x => ?_, fun α => ?_, fun j => ?_⟩
      · rw [UniformGrowthFrechetSpace.toFun_inclusion]
        exact hw.1 i x
      · rw [UniformGrowthFrechetSpace.toFun_inclusion]
        exact hw.2.1 α
      · rw [UniformGrowthFrechetSpace.toFun_inclusion]
        exact hw.2.2 j
    obtain ⟨c, hc⟩ := hrange s hsU hw'
    exact ⟨c, congrArg (fun x : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho
      (max R R₀) L => (x : uniformGrowthLevelSubmodule F G rho hsmooth hcalc (max R R₀) L).val) hc⟩
  have hZfin : IsAdelicCenterFinite F G hsmooth hcalc
      (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val := by
    change Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan _ _)
    rw [adelicCenterOrbitSpan_eq_range]
    refine Submodule.finiteDimensional_of_le (?_ :
      LinearMap.range (adelicCenterOrbitMap F G hsmooth hcalc _) ≤ E)
    rintro _ ⟨Y, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hstab F G T iT ν hG hi hν Ua u t r z hdata rho hN hrho hsmooth hcalc n W
      X hX L hLo hLc R s v hv Y
    change adelicCenterAction F G hsmooth hcalc Y _ ∈ E
    rw [← hwv]
    exact hsol w hw
  have hgrowth : HasAdelicModerateGrowth F G rho
      (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val := by
    obtain ⟨C, hC⟩ := (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).2.2 1
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1), R, fun g => ?_⟩
    have hg := hC g
    rw [map_one, Module.End.one_apply] at hg
    exact hg.trans (mul_le_mul_of_nonneg_right (le_max_left C 1)
      (Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos (F := F) (G := G)
        (rho := rho) hN g).le R))
  refine (isAutomorphicFunctionOn_evaluate_iff F G hsmooth hcalc rho Kinf _).mpr
    ⟨?_, hZfin, hgrowth⟩
  exact (isInfiniteSubgroupFiniteFunction_evaluate_iff F G Kinf _).mp
    (X.isInfiniteSubgroupFiniteFunction_of_mem_solutions hX Kinf hK s v hv)

end Langlands.Global
