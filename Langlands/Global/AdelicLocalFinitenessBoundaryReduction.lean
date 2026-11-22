import Langlands.Global.AdelicLocalFinitenessHilbertReduction
import Langlands.Analysis.Meromorphic.FredholmExactFiber

/-! # Local finiteness from a compact boundary operator

The exact base fibre of the Hilbert Fredholm family lets the factorization of
its boundary operator through smoothing give injectivity of the smoothed
finite-type witness.
-/

noncomputable section
set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry Set ContinuousLinearMap
open scoped CategoryTheory.MonObj Manifold

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

namespace LocalFinitenessData

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {Δ : Type u} {r n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
  (X : LocalFinitenessData F G Δ r n W)
  {Ua : Δ → GroupScheme (Spec (CommRingCat.of F))} [∀ α, IsAffine (Ua α).X.left]
  (uMap : ∀ α, Ua α ⟶ G) [∀ α, IsClosedImmersion (uMap α).hom.hom.left]
  (a : Δ → AdelicGroupPoints F G) (z : Fin r → AdelicGroupPoints F G)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "Growth[" R "]" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "eval[" R "]" => UniformGrowthFrechetSpace.evaluation F G rho hsmooth hcalc hN hrho R L

/-- Hilbert input whose compact boundary operator vanishes on the kernel of
smoothing at the base point. The proposed lift of a solution preserves its
reproducing combination and solves the Hilbert equation. -/
structure BoundaryModel (i : X.Idx) (s₀ : W)
    (B : Type v) [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    (C : Type w) [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C] where
  S : Set W
  isOpen_S : IsOpen S
  mem_S : s₀ ∈ S
  R₀ : ℝ
  lhs : W → B →L[ℂ] C
  rhs : W → B →L[ℂ] C
  holomorphic_lhs : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, Fin n → ℂ) lhs S
  holomorphic_rhs : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, Fin n → ℂ) rhs S
  embedding_lhs : Topology.IsEmbedding (lhs s₀)
  compact_rhs : IsCompactOperator (rhs s₀)
  K : Fin (X.m i) → B →L[ℂ] Growth[R₀]
  compatible : ∀ x, (∑ k, X.normalizedCoefficient i k s₀ • K k) x = 0 →
    rhs s₀ x = 0
  lift_solution : ∀ s ∈ S, ∀ R, R₀ ≤ R → ∀ f ∈ X.solutions uMap a z rho hN hrho hsmooth hcalc R L s,
    ∃ x : B, lhs s x = rhs s x ∧
      ∀ g, eval[R₀] g ((∑ k, X.normalizedCoefficient i k s • K k) x) =
        ∑ k, X.normalizedCoefficient i k s * rightConvolution F G (X.h i k)
          (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f) g

/-- A supplied compact boundary model gives the actual Fréchet witnesses on a
single neighbourhood, in every growth space of exponent at least `model.R₀`. -/
theorem finiteType_on_of_boundaryModel (hX : X.IsAdmissible) {i : X.Idx} {s₀ : W}
    (hi : X.c i s₀ ≠ 0)
    {B : Type v} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {C : Type w} [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
    (model : X.BoundaryModel uMap a z rho hN hrho hsmooth hcalc L i s₀ B C) :
    ∃ U : Set W, IsOpen U ∧ s₀ ∈ U ∧ ∀ R : ℝ, model.R₀ ≤ R →
      IsFiniteTypeOn 𝓘(ℂ, Fin n → ℂ) (X.solutions uMap a z rho hN hrho hsmooth hcalc R L) U := by
  let S := model.S ∩ {s | X.c i s ≠ 0}
  have hc : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (X.c i) univ :=
    hX.2.2.1 i (ContinuousLinearMap.id ℂ ℂ)
  have hcC : Continuous (X.c i) := continuousOn_univ.mp hc.continuousOn
  have hS : IsOpen S := model.isOpen_S.inter (isOpen_ne_fun hcC continuous_const)
  have hs₀ : s₀ ∈ S := ⟨model.mem_S, hi⟩
  have hb (k : Fin (X.m i)) :
      MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (X.normalizedCoefficient i k) S := by
    have hbk : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (X.b i k) univ :=
      hX.2.1 i k (ContinuousLinearMap.id ℂ ℂ)
    exact (hbk.mono (subset_univ S)).div (hc.mono (subset_univ S)) (fun _ hs => hs.2)
  let A (s : W) := model.lhs s - model.rhs s
  let K (s : W) : B →L[ℂ] Growth[model.R₀] := ∑ k, X.normalizedCoefficient i k s • model.K k
  have hA : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, Fin n → ℂ) A S := by
    intro x φ
    refine (((model.holomorphic_lhs x φ).sub (model.holomorphic_rhs x φ)).mono
      (inter_subset_left : S ⊆ model.S)).congr fun s _ => ?_
    change φ ((model.lhs s - model.rhs s) x) = φ (model.lhs s x) - φ (model.rhs s x)
    rw [sub_apply, map_sub]
  have hleft : (model.lhs s₀).HasLeftInverse := by
    obtain ⟨c, hanti⟩ := (model.lhs s₀).antilipschitz_of_isEmbedding model.embedding_lhs
    have hclosed : IsClosed (Set.range (model.lhs s₀)) :=
      hanti.isClosed_range (model.lhs s₀).uniformContinuous
    let : CompleteSpace (model.lhs s₀).range := hclosed.completeSpace_coe
    exact HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range
      model.embedding_lhs.injective hclosed (model.lhs s₀).range.isTopCompl_orthogonal.closedComplemented
  let D := hleft.leftInverse
  have hD : IsCompactOperator (D ∘L A s₀ - ContinuousLinearMap.id ℂ B) := by
    have hDμ : D ∘L model.lhs s₀ = ContinuousLinearMap.id ℂ B :=
      ContinuousLinearMap.ext hleft.leftInverse_leftInverse
    have heq : D ∘L A s₀ - ContinuousLinearMap.id ℂ B = -(D ∘L model.rhs s₀) := by
      change D ∘L (model.lhs s₀ - model.rhs s₀) - ContinuousLinearMap.id ℂ B =
        -(D ∘L model.rhs s₀)
      rw [comp_sub, hDμ]
      abel
    rw [heq]
    exact (model.compact_rhs.clm_comp D).neg
  have hsep (f : Growth[model.R₀]) (hf : ∀ g : AdelicGroupPoints F G, eval[model.R₀] g f = 0) : f = 0 := by
    apply toFun_injective F G rho hsmooth hcalc hN hrho model.R₀ L
    funext g
    exact hf g
  obtain ⟨U, hUS, hUo, hsU, m, ℓ, hℓ, hℓi, hℓk, hℓ₀⟩ :=
    exactFiberFredholmCriterion hS hA hs₀ D hD
  let Λ : W → (Fin m → ℂ) →L[ℂ] Growth[model.R₀] := fun s => K s ∘L ℓ s
  have hΛ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, Fin n → ℂ) Λ U :=
    hℓ.finset_smul_comp Finset.univ model.K (fun k _ => (hb k).mono hUS)
  have hΛ₀ : Function.Injective (Λ s₀) := by
    have hker : (Λ s₀).ker = ⊥ := by
      refine le_antisymm (fun x hx => ?_) bot_le
      rw [Submodule.mem_bot]
      have hm : ℓ s₀ x ∈ (A s₀).ker := by
        change ℓ s₀ x ∈ ((A s₀).ker : Set B)
        rw [← hℓ₀]
        exact ⟨x, rfl⟩
      have hrhs : model.rhs s₀ (ℓ s₀ x) = 0 := model.compatible _ hx
      have hlhs : model.lhs s₀ (ℓ s₀ x) = 0 := by
        have heq : model.lhs s₀ (ℓ s₀ x) - model.rhs s₀ (ℓ s₀ x) = 0 := hm
        simpa only [hrhs, sub_zero] using heq
      apply hℓi s₀ hsU
      apply model.embedding_lhs.injective
      simpa only [map_zero] using hlhs
    exact LinearMap.ker_eq_bot.mp hker
  obtain ⟨V, hVU, hVo, hsV, hΛi⟩ := hΛ.exists_open_injective hUo hsU hΛ₀ (eval[model.R₀]) hsep
  refine ⟨V, hVo, hsV, fun R hR => ?_⟩
  let wR := UniformGrowthFrechetSpace.weakenCLM F G rho hsmooth hcalc hN hrho hR
    (le_refl L)
  have hwR : Function.Injective wR := by
    intro f g hfg
    apply toFun_injective F G rho hsmooth hcalc hN hrho model.R₀ L
    exact congrArg (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L) hfg
  refine ⟨m, fun s => wR ∘L Λ s, fun x φ => (hΛ x (φ ∘L wR)).mono hVU,
    fun s hs => hwR.comp (hΛi s hs), ?_⟩
  intro s hs f hf
  have hsS := hUS (hVU hs)
  obtain ⟨x, hμν, hK⟩ := model.lift_solution s hsS.1 R hR f hf
  have hx : A s x = 0 := sub_eq_zero.mpr hμν
  obtain ⟨b, hb'⟩ := hℓk s (hVU hs) x hx
  have hf' : wR (K s x) = f := by
    apply toFun_injective F G rho hsmooth hcalc hN hrho R L
    funext g
    change eval[model.R₀] g (K s x) = eval[R] g f
    have heq := hf.1 i g
    rw [show eval[model.R₀] g (K s x) = _ from hK g]
    simp only [normalizedCoefficient, div_eq_inv_mul, mul_assoc]
    rw [← Finset.mul_sum, heq, ← mul_assoc, inv_mul_cancel₀ hsS.2, one_mul]
    rfl
  exact ⟨b, by change wR (K s (ℓ s b)) = f; rw [hb', hf']⟩

end LocalFinitenessData

/-- The adelic compact boundary model obligation in the proof of the exact local-finiteness
statement. It asks for a weighted Hilbert model at each base point. -/
def UniformGrowthLocalFinitenessBoundaryModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (iT : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus iT → IsGenericCocharacter iT ν →
    ∀ (Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F)))
      [∀ α, IsAffine (Ua α).X.left] (uMap : ∀ α, Ua α ⟶ G)
      [∀ α, IsClosedImmersion (uMap α).hom.hom.left]
      (t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp) (r : ℕ)
      (z : Fin r → AdelicGroupPoints F T.toGrp),
      IsLocalFinitenessGroupData iT ν uMap t z →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
      (hrho : IsClosedSubgroup rho) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (n : ℕ) (W : TopologicalSpace.Opens (Fin n → ℂ))
      (X : LocalFinitenessData F G (simpleRelativeRoots iT ν) r n W),
      X.IsAdmissible →
      ∀ L : Subgroup (FiniteAdelicGroupPoints F G),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
        IsCompact (L : Set (FiniteAdelicGroupPoints F G)) → ∀ s₀ : W,
      ∃ (i : X.Idx), X.c i s₀ ≠ 0 ∧
        ∃ (B : Type v) (_ : NormedAddCommGroup B) (_ : InnerProductSpace ℂ B) (_ : CompleteSpace B)
          (C : Type w) (_ : NormedAddCommGroup C) (_ : InnerProductSpace ℂ C) (_ : CompleteSpace C),
          Nonempty (X.BoundaryModel uMap (fun α => map F T.toGrp G iT (t α))
            (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc L i s₀ B C)

/-- Constructing the compact boundary model implies the number-field target `UniformGrowthLocalFinitenessStatement`. -/
theorem uniformGrowthLocalFiniteness_of_boundaryModel
    (h : UniformGrowthLocalFinitenessBoundaryModelStatement.{u, v, w}) :
    UniformGrowthLocalFinitenessStatement.{u} := by
  intro F _ _ G T _ _ _ iT ν hG hT hν Ua _ uMap _ t r z hz N d rho hN hrho hsmooth hcalc
    n W X hX L hLo hLc s₀
  obtain ⟨i, hi, B, hB, hBi, hBc, C, hC, hCi, hCc, ⟨model⟩⟩ :=
    h F G T iT ν hG hT hν Ua uMap t r z hz rho hN hrho hsmooth hcalc n W X hX L hLo hLc s₀
  obtain ⟨U, hUo, hs₀U, hfin⟩ :=
    X.finiteType_on_of_boundaryModel uMap _ _ rho hN hrho hsmooth hcalc L hX hi model
  exact ⟨U, hUo, hs₀U, model.R₀, hfin⟩

end Langlands.Global
