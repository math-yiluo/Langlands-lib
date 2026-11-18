import Langlands.Algebra.BrauerCorestriction.Independence
import Langlands.Algebra.BrauerCorestriction.Split

/-!
# The corestriction of Brauer classes

The tensor descent is multiplicative, `Cor(A) ⊗ Cor(B) ≃ Cor(A ⊗ B)`, and sends `M_n(A)` to a
matrix algebra over `Cor(A)`. Hence it respects the matrix-stable Brauer equivalence and defines
the corestriction map `BrauerGroup L → BrauerGroup K`, computed on actual representatives by the
descended algebra over the canonical closure, or over any finite Galois closure admitting
`[L : K]` embeddings of `L`.
-/

universe u u₁ u₂ u₃ u₄ u₅

open TensorProduct PiTensorProduct Module

namespace Langlands.BrauerCorestriction

section Multiplicative

variable (K : Type u₁) (L : Type u₂) (N : Type u₃) [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable (A : Type u₄) [Ring A] [Algebra L A] (B : Type u₅) [Ring B] [Algebra L B]
variable [FiniteDimensional K L] [FiniteDimensional K N] [IsGalois K N]
  [FiniteDimensional L A] [Algebra.IsCentral L A] [IsSimpleRing A]
  [FiniteDimensional L B] [Algebra.IsCentral L B] [IsSimpleRing B]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem corMul_bijective : Function.Bijective (corMul K L N A B) := by
  have : FiniteDimensional K (corAlg K L N A) := finiteDimensional_corAlg K L N A
  have : FiniteDimensional K (corAlg K L N B) := finiteDimensional_corAlg K L N B
  have : Algebra.IsCentral K (corAlg K L N A) := isCentral_corAlg K L N A
  have : Algebra.IsCentral K (corAlg K L N B) := isCentral_corAlg K L N B
  have : IsSimpleRing (corAlg K L N A) := isSimpleRing_corAlg K L N A
  have : IsSimpleRing (corAlg K L N B) := isSimpleRing_corAlg K L N B
  have : Module.Free K (corAlg K L N A) :=
    @Module.Free.of_divisionRing K (corAlg K L N A) _ inferInstance inferInstance
  have : Module.Free K (corAlg K L N B) :=
    @Module.Free.of_divisionRing K (corAlg K L N B) _ inferInstance inferInstance
  let instR : Ring (corAlg K L N A ⊗[K] corAlg K L N B) :=
    Algebra.TensorProduct.instRing (R := K) (A := corAlg K L N A) (B := corAlg K L N B)
  have hs : IsSimpleRing (corAlg K L N A ⊗[K] corAlg K L N B) :=
    @Langlands.CentralSimple.isSimpleRing_tensor K _ (corAlg K L N A) inferInstance
      inferInstance (corAlg K L N B) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
  have : FiniteDimensional K (corAlg K L N (A ⊗[L] B)) :=
    finiteDimensional_corAlg K L N (A ⊗[L] B)
  have hpos : 0 < finrank K (corAlg K L N (A ⊗[L] B)) := by
    rw [finrank_corAlg_eq_pow]
    exact pow_pos Module.finrank_pos _
  have : Nontrivial (corAlg K L N (A ⊗[L] B)) := Module.nontrivial_of_finrank_pos hpos
  have hinj : Function.Injective (corMul K L N A B) := by
    rcases @IsSimpleRing.injective_ringHom_or_subsingleton_codomain
      (corAlg K L N A ⊗[K] corAlg K L N B) (corAlg K L N (A ⊗[L] B)) inferInstance hs
      inferInstance (corMul K L N A B).toRingHom with h | h
    · exact h
    · exact absurd h (not_subsingleton _)
  refine ⟨hinj, ?_⟩
  have hd : finrank K (corAlg K L N A ⊗[K] corAlg K L N B) =
      finrank K (corAlg K L N (A ⊗[L] B)) := by
    rw [Module.finrank_tensorProduct, finrank_corAlg_eq_pow, finrank_corAlg_eq_pow,
      finrank_corAlg_eq_pow, Module.finrank_tensorProduct, mul_pow]
  have : FiniteDimensional K (corAlg K L N A ⊗[K] corAlg K L N B) :=
    @Module.Finite.tensorProduct K (corAlg K L N A) (corAlg K L N B) _ _ _ _ _ _ _
  have key := @LinearMap.injective_iff_surjective_of_finrank_eq_finrank K
    (corAlg K L N A ⊗[K] corAlg K L N B) _ inferInstance inferInstance
    (corAlg K L N (A ⊗[L] B)) inferInstance inferInstance inferInstance inferInstance hd
    { toFun := corMul K L N A B
      map_add' := map_add _
      map_smul' := fun c x => map_smul (corMul K L N A B) c x }
  exact key.mp hinj

/-- Multiplicativity of the tensor descent: `Cor(A) ⊗[K] Cor(B) ≃ Cor(A ⊗[L] B)`. -/
noncomputable def corMulEquiv : corAlg K L N A ⊗[K] corAlg K L N B ≃ₐ[K] corAlg K L N (A ⊗[L] B) :=
  AlgEquiv.ofBijective (corMul K L N A B) (corMul_bijective K L N A B)

/-- Matrix stabilization: `Cor(M_n(A)) ≃ M_{n^e}(Cor(A))` with `e = #(L →ₐ[K] N)`. -/
noncomputable def corAlgMatrixStab (n : ℕ) [NeZero n] :
    corAlg K L N (Matrix (Fin n) (Fin n) A) ≃ₐ[K]
      Matrix (Fin (n ^ Nat.card (L →ₐ[K] N))) (Fin (n ^ Nat.card (L →ₐ[K] N)))
        (corAlg K L N A) :=
  (corEquiv K L N (matrixEquivTensor (Fin n) L A)).trans <|
    (corMulEquiv K L N A (Matrix (Fin n) (Fin n) L)).symm.trans <|
      (Algebra.TensorProduct.congr AlgEquiv.refl (corAlgMatrixEquiv K L N n)).trans
        (matrixEquivTensor (Fin (n ^ Nat.card (L →ₐ[K] N))) K (corAlg K L N A)).symm

end Multiplicative

/-- `1 × 1` matrices over an algebra `X` are isomorphic to `X`. -/
def matrixFinOneAlgEquiv (R : Type*) (X : Type*) [CommSemiring R] [Semiring X] [Algebra R X] :
    Matrix (Fin 1) (Fin 1) X ≃ₐ[R] X where
  toFun M := M 0 0
  invFun x := Matrix.of fun _ _ => x
  left_inv M := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  right_inv x := rfl
  map_mul' M M' := by simp [Matrix.mul_apply]
  map_add' M M' := rfl
  commutes' r := by simp [Matrix.algebraMap_matrix_apply]

section Brauer

variable (K : Type u) (L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The tensor descent over a finite Galois `N` of an actual central simple `L`-algebra, as an
actual central simple `K`-algebra. -/
noncomputable def corCSAOf (N : Type u) [Field N] [Algebra K N] [FiniteDimensional K N]
    [IsGalois K N] (A : CSA.{u, u} L) : CSA.{u, u} K where
  toAlgCat := AlgCat.of K (corAlg K L N A)
  isCentral := isCentral_corAlg K L N A
  isSimple := isSimpleRing_corAlg K L N A
  fin_dim := finiteDimensional_corAlg K L N A

/-- The corestriction representative: the tensor descent over the canonical closure. -/
noncomputable abbrev corCSA (A : CSA.{u, u} L) : CSA.{u, u} K :=
  corCSAOf K L (canonicalClosure K L) A

variable {K L}

/-- The tensor descent respects the matrix-stable Brauer equivalence. -/
theorem corCSAOf_isBrauerEquivalent (N : Type u) [Field N] [Algebra K N] [FiniteDimensional K N]
    [IsGalois K N] {A B : CSA.{u, u} L} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (corCSAOf K L N A) (corCSAOf K L N B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  have : NeZero n := ⟨hn⟩
  have : NeZero m := ⟨hm⟩
  refine ⟨n ^ Nat.card (L →ₐ[K] N), m ^ Nat.card (L →ₐ[K] N), pow_ne_zero _ hn,
    pow_ne_zero _ hm, ⟨?_⟩⟩
  exact (corAlgMatrixStab K L N A n).symm.trans
    ((corEquiv K L N e).trans (corAlgMatrixStab K L N B m))

/-- Isomorphic descended algebras give the same Brauer class. -/
theorem isBrauerEquivalent_of_algEquiv {A B : CSA.{u, u} K} (e : A ≃ₐ[K] B) :
    IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

variable (K L)

/-- Corestriction of Brauer classes for a finite separable extension `L/K`, represented by the
tensor descent over the canonical closure. -/
@[nolint unusedArguments]
noncomputable def cor [Algebra.IsSeparable K L] : BrauerGroup.{u, u} L → BrauerGroup.{u, u} K :=
  Quotient.lift (s := Brauer.CSA_Setoid L)
    (fun A => Quotient.mk (Brauer.CSA_Setoid K) (corCSA K L A))
    (fun _ _ h => Quotient.sound (s := Brauer.CSA_Setoid K)
      (corCSAOf_isBrauerEquivalent (canonicalClosure K L) h))

/-- Class computation: the corestriction of the class of `A` is the class of its tensor
descent. -/
theorem cor_mk [Algebra.IsSeparable K L] (A : CSA.{u, u} L) :
    cor K L (Quotient.mk (Brauer.CSA_Setoid L) A) =
      Quotient.mk (Brauer.CSA_Setoid K) (corCSA K L A) := rfl

/-- Independence of the closure: over any finite Galois `N` admitting `[L : K]` embeddings of
`L`, the tensor descent represents the corestriction. -/
theorem cor_mk_eq_of_closure [Algebra.IsSeparable K L] (N : Type u) [Field N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] (hN : Nat.card (L →ₐ[K] N) = finrank K L)
    (A : CSA.{u, u} L) :
    cor K L (Quotient.mk (Brauer.CSA_Setoid L) A) =
      Quotient.mk (Brauer.CSA_Setoid K) (corCSAOf K L N A) := by
  rw [cor_mk]
  apply Quotient.sound (s := Brauer.CSA_Setoid K)
  obtain ⟨e⟩ := nonempty_corAlgEquiv_canonical K L A hN
  exact isBrauerEquivalent_of_algEquiv e

/-- The corestriction of a matrix algebra over `L` is split: the descended algebra of
`M_n(L)` is a matrix algebra over `K`. -/
theorem corCSAOf_matrix_split (N : Type u) [Field N] [Algebra K N] [FiniteDimensional K N]
    [IsGalois K N] (n : ℕ) [NeZero n] (A : CSA.{u, u} L)
    (e : A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Nonempty (corCSAOf K L N A ≃ₐ[K]
      Matrix (Fin (n ^ Nat.card (L →ₐ[K] N))) (Fin (n ^ Nat.card (L →ₐ[K] N))) K) :=
  ⟨(corEquiv K L N e).trans (corAlgMatrixEquiv K L N n)⟩

/-- Split classes go to split classes. -/
theorem cor_groundField [Algebra.IsSeparable K L] :
    cor K L (Quotient.mk (Brauer.CSA_Setoid L) (Langlands.Brauer.groundField L)) =
      Quotient.mk (Brauer.CSA_Setoid K) (Langlands.Brauer.groundField K) := by
  rw [cor_mk]
  apply Quotient.sound (s := Brauer.CSA_Setoid K)
  obtain ⟨e⟩ := corCSAOf_matrix_split (K := K) (L := L) (canonicalClosure K L) 1
    (Langlands.Brauer.groundField L)
    (matrixFinOneAlgEquiv L L).symm
  refine ⟨1, 1 ^ Nat.card (L →ₐ[K] canonicalClosure K L), one_ne_zero, by simp, ⟨?_⟩⟩
  exact (matrixFinOneAlgEquiv K _).trans e

end Brauer

end Langlands.BrauerCorestriction
