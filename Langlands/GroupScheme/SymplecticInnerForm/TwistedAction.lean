import Langlands.GroupScheme.SymplecticInnerForm.StandardInvolution
import Langlands.GroupScheme.SymplecticInnerForm.GaloisInvolution
import Langlands.GroupScheme.SymplecticInnerForm.InvolutionModel
import Langlands.GroupScheme.SimplyConnected.SpecialLinearInnerFormNormOneProof

/-! # Twisted symplectic Galois actions and descended involutions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticInnerForm

open Langlands.CentralSimple Quaternionic
open SpecialLinearInnerForm (galoisValue galoisValue_one galoisValue_mul extendMatrix
  extendMatrix_map chartAlong chartAlong_tmul)

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  (d : QuasiSplitInnerForm G)

variable {n : Type} [Fintype n] [DecidableEq n]
  (i : d.model ≅ SymplecticMatrix.groupScheme n (CommRingCat.of K))

/-- The matrix algebra endomorphism by which the Galois value at `σ` acts. -/
abbrev galoisMatrixHom (σ : d.carrier ≃ₐ[K] d.carrier) :
    Matrix (n ⊕ n) (n ⊕ n) d.carrier →ₐ[d.carrier] Matrix (n ⊕ n) (n ⊕ n) d.carrier :=
  adjointMatrixHom d.isAdjointQuotient i (galoisValue d σ)

/-- The twisted Galois action on `M_m(L)`: apply `σ` to the entries, then act by the
Galois value `ξ(1, σ)` of the adjoint discrepancy cocycle. -/
def twistedAction : SemilinearGaloisAction K d.carrier (Matrix (n ⊕ n) (n ⊕ n) d.carrier) where
  act σ := (galoisMatrixHom d i σ).toRingHom.comp
    (σ : d.carrier →+* d.carrier).mapMatrix
  act_algebraMap σ l := by
    have h : (σ : d.carrier →+* d.carrier).mapMatrix
        (algebraMap d.carrier (Matrix (n ⊕ n) (n ⊕ n) d.carrier) l) =
          algebraMap d.carrier (Matrix (n ⊕ n) (n ⊕ n) d.carrier) (σ l) := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
    rw [RingHom.comp_apply, h]
    exact (galoisMatrixHom d i σ).commutes (σ l)
  act_one x := by
    change galoisMatrixHom d i 1 (x.map ((1 : d.carrier ≃ₐ[K] d.carrier) :
      d.carrier →+* d.carrier)) = x
    rw [galoisMatrixHom, galoisValue_one, adjointMatrixHom_one]
    rfl
  act_mul σ τ x := by
    change galoisMatrixHom d i (σ * τ) (x.map ((σ * τ : d.carrier ≃ₐ[K] d.carrier) :
        d.carrier →+* d.carrier)) =
      galoisMatrixHom d i σ ((galoisMatrixHom d i τ
        (x.map (τ : d.carrier →+* d.carrier))).map (σ : d.carrier →+* d.carrier))
    rw [galoisMatrixHom, galoisValue_mul, adjointMatrixHom_mul]
    congr 1
    have hn := adjointMatrixHom_naturality d.isAdjointQuotient i σ.toAlgHom
      (galoisValue d τ) (x.map (τ : d.carrier →+* d.carrier))
    refine Eq.trans ?_ hn.symm
    rw [Matrix.map_map]
    rfl

theorem twistedAction_act (σ : d.carrier ≃ₐ[K] d.carrier) (x : Matrix (n ⊕ n) (n ⊕ n) d.carrier) :
    (twistedAction d i).act σ x =
      galoisMatrixHom d i σ (x.map (σ : d.carrier →+* d.carrier)) :=
  rfl

instance : FiniteDimensional K (twistedAction d i).fixed :=
  (twistedAction d i).finiteDimensional_fixed

instance [Nonempty n] : Algebra.IsCentral K (twistedAction d i).fixed :=
  (twistedAction d i).isCentral_fixed

instance [Nonempty n] : IsSimpleRing (twistedAction d i).fixed :=
  (twistedAction d i).isSimpleRing_fixed

/-- Along any coefficient map `f`, the matrix action of `ξ(1, σ)` carries the chart along
`f ∘ σ` to the chart along `f`. -/
theorem extendMatrix_chartAlong_galois {R : Type u} [CommRing R] [Algebra K R]
    (f : d.carrier →+* R) (hf : f.comp (algebraMap K d.carrier) = algebraMap K R)
    (σ : d.carrier ≃ₐ[K] d.carrier)
    (hf' : (f.comp (σ : d.carrier →+* d.carrier)).comp (algebraMap K d.carrier) =
      algebraMap K R)
    (x : R ⊗[K] (twistedAction d i).fixed) :
    extendMatrix f (galoisMatrixHom d i σ).toLinearMap
        (chartAlong (twistedAction d i).descentEquiv (f.comp (σ : d.carrier →+* d.carrier))
          hf' x) =
      chartAlong (twistedAction d i).descentEquiv f hf x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [chartAlong_tmul, chartAlong_tmul, map_smul, SemilinearGaloisAction.descentEquiv_one_tmul]
    congr 1
    rw [RingHom.coe_comp, ← Matrix.map_map, extendMatrix_map]
    congr 1
    exact (twistedAction d i).act_fixed σ a
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]


/-- The twisted action commutes with the standard symplectic involution. -/
theorem twistedAction_standardInvolution (σ : d.carrier ≃ₐ[K] d.carrier)
    (x : Matrix (n ⊕ n) (n ⊕ n) d.carrier) :
    (twistedAction d i).act σ (standardInvolution d.carrier n x) =
      standardInvolution d.carrier n ((twistedAction d i).act σ x) := by
  rw [twistedAction_act, standardInvolution_map, galoisMatrixHom,
    adjointMatrixHom_standardInvolution]
  rfl

/-- The first-kind involution on the fixed algebra of the twisted action. -/
def descendedInvolution : FirstKindInvolution K (twistedAction d i).fixed :=
  (twistedAction d i).fixedInvolution (standardInvolution d.carrier n)
    (twistedAction_standardInvolution d i)

@[simp]
theorem coe_descendedInvolution (a : (twistedAction d i).fixed) :
    (descendedInvolution d i a : Matrix (n ⊕ n) (n ⊕ n) d.carrier) =
      standardInvolution d.carrier n a := rfl

/-- The descent equivalence identifies the descended and standard involutions. -/
theorem descentEquiv_descendedInvolution
    (x : d.carrier ⊗[K] (twistedAction d i).fixed) :
    (twistedAction d i).descentEquiv ((descendedInvolution d i).baseChange d.carrier x) =
      standardInvolution d.carrier n ((twistedAction d i).descentEquiv x) :=
  (twistedAction d i).descentEquiv_fixedInvolution _ _ x

/-- The descended algebra has the degree of the split symplectic matrix algebra. -/
theorem reducedDegree_twistedAction :
    reducedDegree K (twistedAction d i).fixed = 2 * Fintype.card n := by
  simpa [two_mul] using
    (card_eq_reducedDegree K (twistedAction d i).fixed
      (twistedAction d i).descentEquiv).symm

/-- The descended involution has an actual finite Galois standard symplectic chart. -/
theorem hasStandardSymplecticSplitting (r : ℕ)
    (j : d.model ≅ SymplecticMatrix.groupScheme (Fin r) (CommRingCat.of K)) :
    HasStandardSymplecticSplitting (descendedInvolution d j) r := by
  refine ⟨d.carrier, inferInstance, inferInstance, inferInstance, inferInstance,
    (twistedAction d j).descentEquiv, ?_⟩
  intro x
  rw [descentEquiv_descendedInvolution, standardInvolution_mul_J]

end Langlands.GroupScheme.SymplecticInnerForm
