import Langlands.GroupScheme.Rational.DominantHighestWeight
import Langlands.GroupScheme.Rational.PathFundamentalWeights
import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.Reductive.NondegenerateTensorConjugation
import Langlands.GroupScheme.Chevalley.ActualRepresentationExtension
import Langlands.GroupScheme.Reductive.FrobeniusSocleProducts

/-! # Intertwiners, weight spaces and the positive-root order -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A matrix whose linear map is bijective has a two-sided inverse matrix. -/
theorem exists_mul_eq_one_of_bijective {C : Matrix m n k}
    (hC : Function.Bijective C.mulVecLin) :
    ∃ N : Matrix n m k, N * C = 1 ∧ C * N = 1 := by
  let e := LinearEquiv.ofBijective C.mulVecLin hC
  let f : (m → k) →ₗ[k] (n → k) := e.symm
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · have h : f ∘ₗ Matrix.toLin' C = LinearMap.id :=
      LinearMap.ext fun v => e.symm_apply_apply v
    calc LinearMap.toMatrix' f * C
        = LinearMap.toMatrix' (f ∘ₗ Matrix.toLin' C) := by
          rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
      _ = 1 := by rw [h, LinearMap.toMatrix'_id]
  · have h : Matrix.toLin' C ∘ₗ f = LinearMap.id :=
      LinearMap.ext fun v => e.apply_symm_apply v
    calc C * LinearMap.toMatrix' f
        = LinearMap.toMatrix' (Matrix.toLin' C ∘ₗ f) := by
          rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
      _ = 1 := by rw [h, LinearMap.toMatrix'_id]

/-- A bijective actual intertwiner has an actual intertwiner as inverse. -/
theorem Intertwines.exists_inverse {G : GroupScheme (Spec (CommRingCat.of k))}
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m} {C : Matrix m n k}
    (hC : Intertwines ρ σ C) (hb : Function.Bijective C.mulVecLin) :
    ∃ N : Matrix n m k, Intertwines σ ρ N ∧ Function.Bijective N.mulVecLin := by
  obtain ⟨N, hNC, hCN⟩ := exists_mul_eq_one_of_bijective hb
  refine ⟨N, hC.of_mul_eq_one hNC hCN, ?_⟩
  constructor
  · intro v w h
    have h' := congrArg C.mulVecLin h
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hCN, Matrix.one_mulVec] using h'
  · intro v
    refine ⟨C *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hNC, Matrix.one_mulVec]

end MatrixRepresentation

namespace SplitPinning

open MatrixRepresentation Module

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

local instance highestWeightIntertwinersTorusAffine : IsAffineHom p.torus.toGrp.X.hom :=
  p.isSplitTorus.isAffineHom

variable {p}

/-- An actual intertwiner maps each torus weight space into the weight space of the
same weight. -/
theorem mulVec_mem_representationWeightSpace {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines σ C)
    {μ : characterLattice p.torus} {v : n → k} (hv : v ∈ p.representationWeightSpace ρ μ) :
    C *ᵥ v ∈ p.representationWeightSpace σ μ := by
  have hC' := hC.restrict p.inclusion
  change v ∈ (ρ.restrict p.inclusion).characterSpace _ at hv
  change C *ᵥ v ∈ (σ.restrict p.inclusion).characterSpace _
  rw [mem_characterSpace_iff_affine] at hv ⊢
  intro A x
  have hmap : (fun r => algebraMap k A ((C *ᵥ v) r)) =
      C.map (algebraMap k A) *ᵥ (fun r => algebraMap k A (v r)) := by
    funext r
    exact RingHom.map_mulVec (algebraMap k A) C v r
  rw [hmap, Matrix.mulVec_mulVec, ← hC' A x, ← Matrix.mulVec_mulVec, hv A x,
    Matrix.mulVec_smul]

/-- An injective actual intertwiner does not decrease weight multiplicities. -/
theorem finrank_representationWeightSpace_le_of_intertwines {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines σ C)
    (hi : Function.Injective C.mulVecLin) (μ : characterLattice p.torus) :
    finrank k (p.representationWeightSpace ρ μ) ≤ finrank k (p.representationWeightSpace σ μ) := by
  let f : p.representationWeightSpace ρ μ →ₗ[k] p.representationWeightSpace σ μ :=
    C.mulVecLin.restrict (fun v hv => mulVec_mem_representationWeightSpace hC hv)
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro v w h
  exact Subtype.ext (hi (congrArg Subtype.val h))

/-- A bijective actual intertwiner preserves weight multiplicities. -/
theorem finrank_representationWeightSpace_eq_of_intertwines {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines σ C)
    (hb : Function.Bijective C.mulVecLin) (μ : characterLattice p.torus) :
    finrank k (p.representationWeightSpace ρ μ) = finrank k (p.representationWeightSpace σ μ) := by
  obtain ⟨N, hN, hNb⟩ := hC.exists_inverse hb
  exact le_antisymm (finrank_representationWeightSpace_le_of_intertwines hC hb.1 μ)
    (finrank_representationWeightSpace_le_of_intertwines hN hNb.1 μ)

/-- A bijective actual intertwiner preserves the occurring weights. -/
theorem representationWeightSpace_ne_bot_iff_of_intertwines {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines σ C)
    (hb : Function.Bijective C.mulVecLin) (μ : characterLattice p.torus) :
    p.representationWeightSpace ρ μ ≠ ⊥ ↔ p.representationWeightSpace σ μ ≠ ⊥ := by
  rw [← Submodule.one_le_finrank_iff, ← Submodule.one_le_finrank_iff,
    finrank_representationWeightSpace_eq_of_intertwines hC hb μ]

/-- A bijective actual intertwiner transports the highest-weight predicate. -/
theorem IsHighestWeight.of_intertwines {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines σ C)
    (hb : Function.Bijective C.mulVecLin) {lam : characterLattice p.torus}
    (h : p.IsHighestWeight ρ lam) : p.IsHighestWeight σ lam := by
  refine ⟨hC.isIrreducible_of_bijective h.1 hb, p.iSup_representationWeightSpace_eq_top σ, ?_,
    fun μ hμ => h.2.2.2 μ ((representationWeightSpace_ne_bot_iff_of_intertwines hC hb μ).2 hμ)⟩
  rw [← finrank_representationWeightSpace_eq_of_intertwines hC hb lam]
  exact h.2.2.1

variable (p)

/-- The pairing with the positive cocharacter is nonnegative on the positive-root
monoid and vanishes only at zero. -/
theorem latticePairing_positiveCocharacter_of_mem_positiveRootMonoid
    {x : characterLattice p.torus} (hx : x ∈ p.positiveRootMonoid) :
    0 ≤ latticePairing p.torus x p.positiveCocharacter ∧
      (latticePairing p.torus x p.positiveCocharacter = 0 → x = 0) := by
  rw [positiveRootMonoid] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have hpos : 0 < latticePairing p.torus (p.rootDatum.root a) p.positiveCocharacter :=
      (p.latticePairing_root_positiveCocharacter_pos_iff a).mpr
        (by rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_one_of_mem_support a.2]
            exact one_pos)
    exact ⟨hpos.le, fun h => absurd h hpos.ne'⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    refine ⟨add_nonneg hx.1 hy.1, fun h => ?_⟩
    have h1 : latticePairing p.torus x p.positiveCocharacter = 0 := by linarith [hx.1, hy.1]
    have h2 : latticePairing p.torus y p.positiveCocharacter = 0 := by linarith [hx.1, hy.1]
    rw [hx.2 h1, hy.2 h2, add_zero]

/-- The positive-root order is antisymmetric. -/
theorem eq_of_sub_mem_positiveRootMonoid {lam mu : characterLattice p.torus}
    (h₁ : lam - mu ∈ p.positiveRootMonoid) (h₂ : mu - lam ∈ p.positiveRootMonoid) :
    lam = mu := by
  have a := p.latticePairing_positiveCocharacter_of_mem_positiveRootMonoid h₁
  have b := p.latticePairing_positiveCocharacter_of_mem_positiveRootMonoid h₂
  have hneg : latticePairing p.torus (mu - lam) p.positiveCocharacter =
      -latticePairing p.torus (lam - mu) p.positiveCocharacter := by
    rw [← neg_sub, map_neg, LinearMap.neg_apply]
  rw [hneg] at b
  have h0 : latticePairing p.torus (lam - mu) p.positiveCocharacter = 0 := by
    linarith [a.1, b.1]
  exact sub_eq_zero.mp (a.2 h0)

variable {p}

/-- A highest weight is dominant: its simple reflections are weights, hence lie
below it. -/
theorem IsHighestWeight.isDominantWeight {ρ : MatrixRepresentation G n}
    {lam : characterLattice p.torus} (h : p.IsHighestWeight ρ lam) : p.IsDominantWeight lam := by
  intro a
  have hfr := finrank_representationWeightSpace_simpleReflection ρ a lam
  have hne : p.representationWeightSpace ρ (p.rootDatum.reflection (a : p.rootIndex) lam) ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff, hfr, h.2.2.1]
  have hmem := h.2.2.2 _ hne
  rw [RootPairing.reflection_apply, sub_sub_cancel] at hmem
  have hp := (p.latticePairing_positiveCocharacter_of_mem_positiveRootMonoid hmem).1
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at hp
  have hpos : 0 < latticePairing p.torus (p.rootDatum.root a) p.positiveCocharacter :=
    (p.latticePairing_root_positiveCocharacter_pos_iff a).mpr
      (by rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_one_of_mem_support a.2]
          exact one_pos)
  by_contra hc
  push Not at hc
  exact absurd hp (not_le.mpr (mul_neg_of_neg_of_pos hc hpos))

/-- Two highest weights of the same representation agree. -/
theorem IsHighestWeight.eq {ρ : MatrixRepresentation G n} {lam mu : characterLattice p.torus}
    (hl : p.IsHighestWeight ρ lam) (hm : p.IsHighestWeight ρ mu) : lam = mu := by
  have hl0 : p.representationWeightSpace ρ lam ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff, hl.2.2.1]
  have hm0 : p.representationWeightSpace ρ mu ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff, hm.2.2.1]
  exact p.eq_of_sub_mem_positiveRootMonoid (hl.2.2.2 mu hm0) (hm.2.2.2 lam hl0)

end SplitPinning

end Langlands.GroupScheme
