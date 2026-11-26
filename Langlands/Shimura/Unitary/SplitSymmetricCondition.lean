import Langlands.Shimura.Unitary.SplitFactorCharts
import Langlands.Shimura.Unitary.SymmetricReducedCharpoly
import Langlands.Shimura.Unitary.LocalSymmetricPolynomial
import Langlands.Global.Arithmetic.PolynomialFactorizationNeighborhood
import Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof
import Langlands.Global.CompletionPadic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # An irreducible symmetric polynomial condition at a split finite place -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra _root_.Polynomial Topology
open Langlands.CentralSimple Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Local
open Langlands.Global.FieldRealization
open scoped TensorProduct FiniteExtension

universe u v x y

section Condition

variable {E : Type u} {A : Type v} [Field E] [Ring A] [Algebra E A] {m : ℕ}

/-- Open completed coordinates with a symmetric point and an implication for
symmetric global elements meeting the condition. -/
structure SymmetricCoordinateCondition (σ : AlgebraInvolution E A) (B : Module.Basis (Fin m) E A)
    (L : Type x) [Field L] [Algebra E L] [TopologicalSpace L] (Q : A → Prop) where
  carrier : Set (Fin m → L)
  isOpen_carrier : IsOpen carrier
  fixedPoint : ∃ z : L ⊗[E] A, σ.baseChange L z = z ∧ (B.baseChange L).equivFun z ∈ carrier
  implies (a : A) : σ a = a → (B.baseChange L).equivFun (1 ⊗ₜ[E] a) ∈ carrier → Q a

end Condition

section Comparison

variable {E : Type u} {S : Type x} {K A : Type v} {L : Type y}
  [CommRing E] [CommRing S] [Field K] [Field L] [Ring A]
  [Algebra E A] [Algebra E S] [Algebra K A] [Algebra K L] [Algebra S L]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] {n : ℕ}

/-- A surjective completed matrix chart that preserves the original central
scalars computes the coefficient extension of the reduced polynomial. -/
theorem reducedCharpoly_eq_of_centerCompatibleChart
    (hdim : Module.finrank K A = n ^ 2)
    (e : S ⊗[E] A →ₐ[S] Matrix (Fin n) (Fin n) L) (hsurj : Function.Surjective e)
    (hcenter : ∀ k : K, e (1 ⊗ₜ[E] algebraMap K A k) =
      algebraMap L (Matrix (Fin n) (Fin n) L) (algebraMap K L k)) (a : A) :
    (reducedCharpoly K A a).map (algebraMap K L) = (e (1 ⊗ₜ[E] a)).charpoly := by
  let f := matrixChartOfCenterCompatible hdim e hsurj hcenter
  have hn : reducedDegree K A = n := by
    change Nat.sqrt (Module.finrank K A) = n
    rw [hdim, pow_two, Nat.sqrt_eq]
  let g := f.val.trans (Matrix.reindexAlgEquiv L L (finCongr hn.symm))
  rw [reducedCharpoly_map_chart K A g]
  simp only [g, AlgEquiv.trans_apply, Matrix.coe_reindexAlgEquiv, Matrix.charpoly_reindex]
  exact congrArg Matrix.charpoly (f.property a)

end Comparison

section IrreducibleMatrix

variable {E : Type u} [Field E] [NumberField E] (p : Langlands.Global.FinitePlace E) {n : ℕ}

private theorem exists_irreducibleMatrix (hn : 0 < n) :
    ∃ X : Matrix (Fin n) (Fin n) (FiniteCompletion E p), Irreducible X.charpoly := by
  let F := FiniteCompletion E p
  obtain ⟨L, hg, -, hd⟩ := unramifiedExtensionDegreeExistence (residuePrime p) (padicField p) n hn
  have : IsGalois F L.field := hg
  have hdim : Module.finrank F L.field = n := hd
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F L.field
  let b := (Module.finBasis F L.field).reindex (finCongr hdim)
  let h := Algebra.lmul F L.field a
  let X := LinearMap.toMatrix b b h
  have hc : X.charpoly = h.charpoly := LinearMap.charpoly_toMatrix _ _
  have hdeg := (Field.primitive_element_iff_minpoly_natDegree_eq F a).mp ha
  have hpoly : h.charpoly = minpoly F a := by
    apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsIntegral.of_finite F a))
      (LinearMap.charpoly_monic h) (minpoly.dvd F a (Algebra.aeval_self_charpoly_lmul (R := F) a))
    rw [LinearMap.charpoly_natDegree, hdeg]
  exact ⟨X, by rw [hc, hpoly]; exact minpoly.irreducible (IsIntegral.of_finite F a)⟩

end IrreducibleMatrix

section Split

variable {E : Type u} {K A : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {n m : ℕ} (D : CentralSimpleUnitaryData E K A n) (B : Module.Basis (Fin m) E A)
  (p : Langlands.Global.FinitePlace E) (s : SplitPlaceIdentification E K p)
  (hz : HasCompletedBrauerInvariant K A (placeAbove K p).val 0)

local notation "F" => FiniteCompletion E p
local notation "M" => Matrix (Fin n) (Fin n) F
local notation "C" => LocalCenter E K p
local notation "V" => LocalAlgebra E A p
local notation "σ" => localInvolution D.toSecondKindInvolution p

include s hz in
private theorem exists_splitIrreducibleCoordinateCondition :
    Nonempty (SymmetricCoordinateCondition D.involution B F
      (fun a => Irreducible (reducedCharpoly K A a))) := by
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (WithZero (Multiplicative ℤ))
  let : IsUltrametricDist F := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm F (WithZero (Multiplicative ℤ)))
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  have hn : 0 < n := by have := D.rank_gt_one; omega
  obtain ⟨e, he, -⟩ := s.isQuasiSplitAt_of_zeroCompletedBrauerInvariant (A := A) (placeAbove K p) D hz
  let T : V ≃ₐ[F] M × M := e.trans (s.equiv.mapMatrix.trans
    (ComplexMatrix.prodAlgEquiv F F n F))
  let π : V →ₐ[F] M := (AlgHom.fst F M M).comp T.toAlgHom
  have hπ : Function.Surjective π := fun X => ⟨T.symm (X, 0), by
    change (T (T.symm (X, 0))).1 = X
    rw [T.apply_symm_apply]⟩
  have hT (z : C) : T (localCenterMap E K A p z) =
      (algebraMap F M (s.equiv z).1, algebraMap F M (s.equiv z).2) := by
    change ComplexMatrix.prodAlgEquiv F F n F
      (s.equiv.mapMatrix (e (localCenterMap E K A p z))) = _
    rw [he]
    apply Prod.ext <;> ext i j <;> by_cases hij : i = j <;>
      simp [Matrix.scalar_apply, Matrix.algebraMap_matrix_apply, hij]
  let φ : K →+* F := ((AlgHom.fst F F F).toRingHom.comp s.equiv.toRingHom).comp
    (Algebra.TensorProduct.includeRight : K →ₐ[E] C).toRingHom
  let : Algebra K F := φ.toAlgebra
  have hcen (k : K) : π (1 ⊗ₜ[E] algebraMap K A k) = algebraMap F M (algebraMap K F k) := by
    exact congrArg Prod.fst (hT (1 ⊗ₜ[E] k))
  obtain ⟨X, hX⟩ := exists_irreducibleMatrix p hn
  let f := X.charpoly
  have hf : f.Monic := Matrix.charpoly_monic _
  have hd : f.natDegree = n := by simp [f]
  let r := irreducibleCoefficientNeighborhood_nonarchimedean f hf hX
  have hind : IsInducing (algebraMap F F) := by
    rw [Algebra.algebraMap_self]
    exact IsInducing.id
  let U := matrixCoefficientNeighborhood hind f hf hd r.val r.property.1
  let u := π.toLinearMap.comp (B.baseChange F).equivFun.symm.toLinearMap
  let O := u ⁻¹' U.val
  refine ⟨⟨O, U.property.1.preimage u.continuous_of_finiteDimensional, ?_, ?_⟩⟩
  · let z := s.equiv.symm (1, 0)
    let y := T.symm (X, 0)
    have hz₁ : T (localCenterMap E K A p z) = (1, 0) := by
      rw [hT, s.equiv.apply_symm_apply]
      simp
    have hz₂ : T (localCenterMap E K A p (localConjugation E K p z)) = (0, 1) := by
      rw [hT, s.conjugation_eq, s.equiv.apply_symm_apply]
      simp
    have hy : localCenterMap E K A p z * y = y := by
      apply T.injective
      rw [map_mul, hz₁, show T y = (X, 0) from T.apply_symm_apply _]
      simp
    have hσy := congrArg σ hy
    rw [AlgebraInvolution.apply_mul, localInvolution_center] at hσy
    have hσ₁ : π (σ y) = 0 := by
      have h := congrArg (fun x : V => (T x).1) hσy
      rw [map_mul, hz₂, Prod.fst_mul, mul_zero] at h
      exact h.symm
    have hyX : π y = X := congrArg Prod.fst (T.apply_symm_apply (X, 0))
    refine ⟨y + σ y, ?_, ?_⟩
    · change σ (y + σ y) = y + σ y
      rw [(σ).apply_add, (σ).apply_apply, add_comm]
    · change u ((B.baseChange F).equivFun (y + σ y)) ∈ U.val
      change π ((B.baseChange F).equivFun.symm ((B.baseChange F).equivFun (y + σ y))) ∈ U.val
      rw [LinearEquiv.symm_apply_apply, map_add, hyX, hσ₁, add_zero]
      apply U.property.2.1
      rw [Algebra.algebraMap_self, Polynomial.map_id]
  · intro a _ ha
    change π ((B.baseChange F).equivFun.symm ((B.baseChange F).equivFun (1 ⊗ₜ[E] a))) ∈ U.val at ha
    rw [LinearEquiv.symm_apply_apply] at ha
    let g := (reducedCharpoly K A a).map φ
    have hg : g.Monic := (reducedCharpoly_monic K A a).map _
    have hgdeg : g.natDegree = n := by
      rw [(reducedCharpoly_monic K A a).natDegree_map, reducedCharpoly_natDegree]
      change Nat.sqrt (Module.finrank K A) = n
      rw [D.dimension, pow_two, Nat.sqrt_eq]
    have hpol : (π (1 ⊗ₜ[E] a)).charpoly = g :=
      (reducedCharpoly_eq_of_centerCompatibleChart D.dimension π hπ hcen a).symm
    have hr := U.property.2.2 _ ha g hg hgdeg (by rwa [Algebra.algebraMap_self, Polynomial.map_id])
    have hgi : Irreducible g := r.property.2 g hg (hgdeg.trans hd.symm) hr
    have : IsLocalHom (Polynomial.mapRingHom φ) := ⟨fun q hq => by
      change IsUnit (q.map φ) at hq
      apply Polynomial.isUnit_iff_degree_eq_zero.mpr
      rw [← Polynomial.degree_map_eq_of_injective φ.injective q]
      exact Polynomial.isUnit_iff_degree_eq_zero.mp hq⟩
    exact Irreducible.of_map (f := Polynomial.mapRingHom φ) hgi

/-- At a split finite place with zero invariant, an open symmetric condition
forces irreducibility of the global reduced characteristic polynomial. -/
def splitIrreducibleCoordinateCondition :
    SymmetricCoordinateCondition D.involution B F (fun a => Irreducible (reducedCharpoly K A a)) :=
  Classical.choice (exists_splitIrreducibleCoordinateCondition D B p s hz)

end Split

end Langlands.Shimura.FiniteUnitary
