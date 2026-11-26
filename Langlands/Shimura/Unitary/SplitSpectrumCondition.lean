import Langlands.Shimura.Unitary.SplitSymmetricCondition
import Langlands.Global.Arithmetic.CMHalfWeightLocalNormControl

/-! # Split polynomial conditions at nonsplit finite and real CM places -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra _root_.Polynomial _root_.Topology
open Langlands.CentralSimple Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.Global.FieldRealization
open scoped TensorProduct FiniteExtension

universe u v

variable {E : Type u} {K A : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {n m : ℕ} (D : CentralSimpleUnitaryData E K A n) (B : Module.Basis (Fin m) E A)

section Nonsplit

variable (p : Langlands.Global.FinitePlace E) (hp : ¬ IsSplitPlace E K p)
  (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)

local notation "F" => FiniteCompletion E p
local notation "L" => FiniteCompletion K (Subtype.val (placeAbove K p))
local notation "M" => Matrix (Fin n) (Fin n) L

set_option maxRecDepth 4096 in
include hp hz in
private theorem exists_nonsplitSplitSpectrumCondition :
    Nonempty (SymmetricCoordinateCondition D.involution B F (fun a => ∀ ha : D.involution a = a,
      ((symmetricReducedCharpoly D ha).val.map (algebraMap E F)).Splits)) := by
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (WithZero (Multiplicative ℤ))
  let : IsUltrametricDist F := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm F (WithZero (Multiplicative ℤ)))
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hn : 0 < n := by have := D.rank_gt_one; omega
  let G := nonsplitHermitianChart p D hn hp hz
  let C := nonsplitCompletionCenterEquiv p hp
  have hcen (k : K) : G.equiv (1 ⊗ₜ[E] algebraMap K A k) =
      algebraMap L M (algebraMap K L k) := by
    let z : LocalCenter E K p := 1 ⊗ₜ[E] k
    have h := G.center_eq (C z)
    change G.equiv (localCenterMap E K A p (C.symm (C z))) = Matrix.scalar (Fin n) (C z) at h
    rw [C.symm_apply_apply] at h
    change _ = Matrix.scalar (Fin n) (algebraMap K L k)
    simpa only [z, localCenterMap_tmul, C, nonsplitCompletionCenterEquiv_apply,
      completedCenterMap_tmul, map_one, one_mul] using h
  let f := distinctScalarPolynomial (n := n) F
  have hf : f.Monic := distinctScalarPolynomial_monic F
  have hdeg : f.natDegree = n := distinctScalarPolynomial_natDegree F
  let r := splitCoefficientNeighborhood_nonarchimedean f hf (hdeg.symm ▸ hn)
    (distinctScalarPolynomial_splits F) (distinctScalarPolynomial_separable F)
  have hind : IsInducing (algebraMap F L) :=
    (Langlands.Global.CMHalfWeight.isEmbedding_completionMap p (placeAbove K p).val).isInducing
  let U := matrixCoefficientNeighborhood hind f hf hdeg r.val r.property.1
  let u := G.equiv.toLinearMap.comp (B.baseChange F).equivFun.symm.toLinearMap
  let O := u ⁻¹' U.val
  refine ⟨⟨O, U.property.1.preimage u.continuous_of_finiteDimensional, ?_, ?_⟩⟩
  · let Y := symmetricMatrixWithDistinctScalarRoots (nonsplitCoefficientInvolution p hp)
      G.gram G.hermitian
    let x := G.equiv.symm Y.val
    refine ⟨x, G.equiv.injective ?_, ?_⟩
    · change G.equiv (localInvolution D.toSecondKindInvolution p x) = G.equiv x
      rw [G.adjoint_eq, show G.equiv x = Y.val from G.equiv.apply_symm_apply _]
      exact Y.property.1
    · change G.equiv ((B.baseChange F).equivFun.symm ((B.baseChange F).equivFun x)) ∈ U.val
      rw [LinearEquiv.symm_apply_apply, show G.equiv x = Y.val from G.equiv.apply_symm_apply _]
      exact U.property.2.1 _ Y.property.2
  · intro a _ ha ha'
    change G.equiv ((B.baseChange F).equivFun.symm ((B.baseChange F).equivFun (1 ⊗ₜ[E] a))) ∈ U.val at ha
    rw [LinearEquiv.symm_apply_apply] at ha
    let P := symmetricReducedCharpoly D ha'
    let g := P.val.map (algebraMap E F)
    have hm : P.val.Monic := symmetricReducedCharpoly_monic D ha'
    have hg : g.Monic := hm.map _
    have hd : g.natDegree = n := (hm.natDegree_map _).trans (symmetricReducedCharpoly_natDegree D ha')
    have hpoly : (G.equiv (1 ⊗ₜ[E] a)).charpoly = g.map (algebraMap F L) := by
      have h := reducedCharpoly_eq_of_centerCompatibleChart D.dimension G.equiv.toAlgHom
        G.equiv.surjective hcen a
      change (reducedCharpoly K A a).map (algebraMap K L) = (G.equiv (1 ⊗ₜ[E] a)).charpoly at h
      rw [← h, ← P.property]
      change (P.val.map (algebraMap E K)).map (algebraMap K L) =
        (P.val.map (algebraMap E F)).map (algebraMap F L)
      rw [Polynomial.map_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq E K L,
        ← IsScalarTower.algebraMap_eq E F L]
    exact (r.property.2 g hg (hd.trans hdeg.symm) (U.property.2.2 _ ha g hg hd hpoly)).1

/-- A nonsplit matrix place with zero upper Brauer invariants has an open
symmetric condition forcing the descended polynomial to split at the place. -/
def nonsplitSplitSpectrumCondition :
    SymmetricCoordinateCondition D.involution B F (fun a => ∀ ha : D.involution a = a,
      ((symmetricReducedCharpoly D ha).val.map (algebraMap E F)).Splits) :=
  Classical.choice (exists_nonsplitSplitSpectrumCondition D B p hp hz)

end Nonsplit

section Real

set_option maxRecDepth 4096 in
/-- In the actual Hermitian chart at a real embedding, an open symmetric
condition forces the descended polynomial to split over the reals. -/
def realSplitSpectrumCondition (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    SymmetricCoordinateCondition D.involution B ℝ (fun a => ∀ ha : D.involution a = a,
      ((symmetricReducedCharpoly D ha).val.map τ).Splits) := by
  let : Algebra E ℝ := τ.toAlgebra
  have hn : 0 < n := by have := D.rank_gt_one; omega
  let G := realHermitianChart D hn τ
  let f := distinctScalarPolynomial (n := n) ℝ
  have hf : f.Monic := distinctScalarPolynomial_monic ℝ
  have hdeg : f.natDegree = n := distinctScalarPolynomial_natDegree ℝ
  let r := splitCoefficientNeighborhood_real f hf (hdeg.symm ▸ hn)
    (distinctScalarPolynomial_splits ℝ) (distinctScalarPolynomial_separable ℝ)
  have hind : IsInducing (algebraMap ℝ ℂ) :=
    Complex.isometry_ofReal.isUniformEmbedding.isEmbedding.isInducing
  let U := matrixCoefficientNeighborhood hind f hf hdeg r.val r.property.1
  let u := G.equiv.toLinearMap.comp (B.baseChange ℝ).equivFun.symm.toLinearMap
  refine ⟨u ⁻¹' U.val, U.property.1.preimage u.continuous_of_finiteDimensional, ?_, ?_⟩
  · let Y := symmetricMatrixWithDistinctScalarRoots (AlgebraInvolution.ofStar (R := ℝ) (A := ℂ))
      G.gram G.hermitian
    let x := G.equiv.symm Y.val
    refine ⟨x, G.equiv.injective ?_, ?_⟩
    · rw [G.adjoint_eq, show G.equiv x = Y.val from G.equiv.apply_symm_apply _]
      exact Y.property.1
    · change G.equiv ((B.baseChange ℝ).equivFun.symm ((B.baseChange ℝ).equivFun x)) ∈ U.val
      rw [LinearEquiv.symm_apply_apply, show G.equiv x = Y.val from G.equiv.apply_symm_apply _]
      exact U.property.2.1 _ Y.property.2
  · intro a _ ha ha'
    change G.equiv ((B.baseChange ℝ).equivFun.symm ((B.baseChange ℝ).equivFun (1 ⊗ₜ[E] a))) ∈ U.val at ha
    rw [LinearEquiv.symm_apply_apply] at ha
    let P := symmetricReducedCharpoly D ha'
    let g := P.val.map τ
    have hm : P.val.Monic := symmetricReducedCharpoly_monic D ha'
    have hg : g.Monic := hm.map _
    have hd : g.natDegree = n := (hm.natDegree_map _).trans (symmetricReducedCharpoly_natDegree D ha')
    have hpoly : (G.equiv (1 ⊗ₜ[E] a)).charpoly = g.map (algebraMap ℝ ℂ) := by
      have h := reducedCharpoly_map_realHermitianChart D hn τ a
      change (reducedCharpoly K A a).map (embeddingOverReal τ) = (G.equiv (1 ⊗ₜ[E] a)).charpoly at h
      rw [← h, ← P.property]
      change ((P.val.map (algebraMap E K)).map (embeddingOverReal τ)) =
        (P.val.map τ).map (algebraMap ℝ ℂ)
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext e
      exact embeddingOverReal_apply_algebraMap τ e
    exact (r.property.2 g hg (hd.trans hdeg.symm) (U.property.2.2 _ ha g hg hd hpoly)).1

set_option maxRecDepth 4096 in
/-- The real condition in coordinates of the actual infinite-place completion. -/
def infiniteSplitSpectrumCondition (w : NumberField.InfinitePlace E) (hw : w.IsReal) :
    SymmetricCoordinateCondition D.involution B w.Completion (fun a => ∀ ha : D.involution a = a,
      ((symmetricReducedCharpoly D ha).val.map (InfinitePlace.embedding_of_isReal hw)).Splits) := by
  let τ := InfinitePlace.embedding_of_isReal hw
  let : Algebra E ℝ := τ.toAlgebra
  let f := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
  let fₐ : w.Completion →ₐ[E] ℝ :=
    { toRingHom := f
      commutes' := fun a => by
        change f ((WithAbs.equiv w.val).symm a : w.Completion) = τ a
        rw [show f = InfinitePlace.Completion.extensionEmbeddingOfIsReal hw from rfl,
          InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply] }
  let e := AlgEquiv.ofBijective fₐ (InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw)
  let T : w.Completion ⊗[E] A ≃ₐ[E] ℝ ⊗[E] A := Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[E] A)
  let P := realSplitSpectrumCondition D B τ
  let g (x : Fin m → w.Completion) : Fin m → ℝ := fun j => f (x j)
  have hg : Continuous g := continuous_pi (fun j =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp (continuous_apply j))
  have hcoordinates (x : w.Completion ⊗[E] A) :
      g ((B.baseChange w.Completion).equivFun x) = (B.baseChange ℝ).equivFun (T x) := by
    funext j
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simpa only [g, map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy
    | tmul s a =>
      change f ((B.baseChange w.Completion).repr (s ⊗ₜ[E] a) j) =
        (B.baseChange ℝ).repr ((f s) ⊗ₜ[E] a) j
      rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
        Algebra.smul_def, Algebra.smul_def, map_mul]
      exact congrArg (· * f s) (fₐ.commutes (B.repr a j))
  have hinv (x : w.Completion ⊗[E] A) :
      T (D.involution.baseChange w.Completion x) = D.involution.baseChange ℝ (T x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s a => rfl
  refine ⟨g ⁻¹' P.carrier, P.isOpen_carrier.preimage hg, ?_, ?_⟩
  · obtain ⟨x, hx, hm⟩ := P.fixedPoint
    let y := T.symm x
    have hy : T y = x := T.apply_symm_apply x
    refine ⟨y, T.injective ?_, ?_⟩
    · rw [hinv, hy, hx]
    · change g ((B.baseChange w.Completion).equivFun y) ∈ P.carrier
      rwa [hcoordinates, hy]
  · intro a ha hm
    change g ((B.baseChange w.Completion).equivFun (1 ⊗ₜ[E] a)) ∈ P.carrier at hm
    rw [hcoordinates] at hm
    have ht : T (1 ⊗ₜ[E] a) = 1 ⊗ₜ[E] a := by
      change (f 1) ⊗ₜ[E] a = _
      rw [map_one]
    rw [ht] at hm
    exact P.implies a ha hm

end Real

end Langlands.Shimura.FiniteUnitary
