import Langlands.LocalFactor.WeilDelignePair
import Langlands.WeilDeligne.DirectSum
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Euler factors of finite direct sums of Weil–Deligne pairs

The Euler polynomial of a componentwise operator on a finite product is the
product of the Euler polynomials. The inertia-fixed monodromy kernel of a
finite direct sum of pairs is the product of the kernels, so rational L-factors
of direct sums are products. Tensor products distribute over finite direct sums
as genuine pair equivalences, which gives the double-product formula for pair
L-factors of two direct sums.
-/

noncomputable section

universe uK uG uV uW uι

open Polynomial

namespace Langlands.LocalFactor

section LinearAlgebra

variable {K : Type uK} [Field K]

/-- The Euler polynomial of a block-diagonal operator on a binary product. -/
theorem eulerPolynomial_prodMap {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : Module.End K V) (g : Module.End K W) :
    eulerPolynomial (f.prodMap g) = eulerPolynomial f * eulerPolynomial g := by
  rw [eulerPolynomial, LinearMap.charpoly_prodMap, reverse_mul_of_domain]
  rfl

/-- On a zero-dimensional space the Euler polynomial is `1`. -/
theorem eulerPolynomial_of_subsingleton {V : Type uV}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Subsingleton V]
    (f : Module.End K V) : eulerPolynomial f = 1 := by
  have h : f.charpoly = 1 := by
    apply Polynomial.eq_one_of_monic_natDegree_zero f.charpoly_monic
    rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton]
  rw [eulerPolynomial, h, ← C_1, reverse_C]

private theorem eulerPolynomial_pi_fin (r : ℕ) :
    ∀ (V : Fin r → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
      [∀ i, FiniteDimensional K (V i)] (f : ∀ i, Module.End K (V i)),
      eulerPolynomial (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
        ∏ i, eulerPolynomial (f i) := by
  induction r with
  | zero =>
    intro V _ _ _ f
    rw [eulerPolynomial_of_subsingleton, Finset.univ_eq_empty, Finset.prod_empty]
  | succ r ih =>
    intro V _ _ _ f
    let e := (Fin.consLinearEquiv K V).symm
    have hconj : e.conj (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
        (f 0).prodMap (LinearMap.pi fun i : Fin r => f i.succ ∘ₗ LinearMap.proj i) := by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · simp [e, LinearEquiv.conj_apply]
      · funext i
        simp [e, LinearEquiv.conj_apply, Fin.tail]
    rw [← eulerPolynomial_conj e, hconj, eulerPolynomial_prodMap, ih, Fin.prod_univ_succ]

/-- The Euler polynomial of a componentwise operator on a finite product. -/
theorem eulerPolynomial_pi {r : ℕ} {V : Fin r → Type uV} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] [∀ i, FiniteDimensional K (V i)] (f : ∀ i, Module.End K (V i)) :
    eulerPolynomial (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
      ∏ i, eulerPolynomial (f i) :=
  eulerPolynomial_pi_fin r V f

section Distributivity

variable {ι : Type uι} [DecidableEq ι] {M : ι → Type uV} [∀ i, AddCommGroup (M i)]
  [∀ i, Module K (M i)] {N : Type uW} [AddCommGroup N] [Module K N]

/-- Left distributivity of tensor products over direct sums carries a tensor of
operators, the first componentwise, to the componentwise tensor. -/
theorem directSumLeft_comp_map (f : ∀ i, Module.End K (M i)) (h : Module.End K N) :
    (TensorProduct.directSumLeft K K M N).toLinearMap ∘ₗ
        TensorProduct.map (DirectSum.lmap f) h =
      DirectSum.lmap (fun i => TensorProduct.map (f i) h) ∘ₗ
        (TensorProduct.directSumLeft K K M N).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  apply DirectSum.ext
  intro i
  simp [TensorProduct.directSumLeft_tmul]

/-- Left distributivity carries the monodromy `N ⊗ 1 + 1 ⊗ N'` of a tensor to
the componentwise one. -/
theorem directSumLeft_comp_monodromy (f : ∀ i, Module.End K (M i)) (h : Module.End K N) :
    (TensorProduct.directSumLeft K K M N).toLinearMap ∘ₗ
        (TensorProduct.map (DirectSum.lmap f) 1 + TensorProduct.map 1 h) =
      DirectSum.lmap (fun i => TensorProduct.map (f i) 1 + TensorProduct.map 1 h) ∘ₗ
        (TensorProduct.directSumLeft K K M N).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  apply DirectSum.ext
  intro i
  simp [TensorProduct.directSumLeft_tmul]

/-- Right distributivity of tensor products over direct sums carries a tensor of
operators, the second componentwise, to the componentwise tensor. -/
theorem directSumRight_comp_map (h : Module.End K N) (f : ∀ i, Module.End K (M i)) :
    (TensorProduct.directSumRight K K N M).toLinearMap ∘ₗ
        TensorProduct.map h (DirectSum.lmap f) =
      DirectSum.lmap (fun i => TensorProduct.map h (f i)) ∘ₗ
        (TensorProduct.directSumRight K K N M).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  apply DirectSum.ext
  intro i
  simp [TensorProduct.directSumRight_tmul]

/-- Right distributivity carries the monodromy `N ⊗ 1 + 1 ⊗ N'` of a tensor to
the componentwise one. -/
theorem directSumRight_comp_monodromy (h : Module.End K N) (f : ∀ i, Module.End K (M i)) :
    (TensorProduct.directSumRight K K N M).toLinearMap ∘ₗ
        (TensorProduct.map h 1 + TensorProduct.map 1 (DirectSum.lmap f)) =
      DirectSum.lmap (fun i => TensorProduct.map h 1 + TensorProduct.map 1 (f i)) ∘ₗ
        (TensorProduct.directSumRight K K N M).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  apply DirectSum.ext
  intro i
  simp [TensorProduct.directSumRight_tmul]

end Distributivity

/-- Rational factors are reciprocals of Euler polynomials. -/
theorem rationalFactor_eq_inv {V : Type uV} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    rationalFactor f = (algebraMap K[X] (RatFunc K) (eulerPolynomial f))⁻¹ := rfl

/-- The rational factor of a componentwise operator on a finite product. -/
theorem rationalFactor_pi {r : ℕ} {V : Fin r → Type uV} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] [∀ i, FiniteDimensional K (V i)] (f : ∀ i, Module.End K (V i)) :
    rationalFactor (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
      ∏ i, rationalFactor (f i) := by
  simp only [rationalFactor_eq_inv, eulerPolynomial_pi, map_prod, Finset.prod_inv_distrib]

end LinearAlgebra

namespace WeilDeligne

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

section Embedding

variable (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) (I : Subgroup G) [I.Normal]
  {W : Type uW} [AddCommGroup W] [Module K W]

/-- The inclusion of the inertia-fixed monodromy kernel into the carrier. -/
def kernelSubtype : A.inertiaKernelRepresentation I →ₗ[K] A :=
  A.monodromy.ker.subtype ∘ₗ
    (FiniteRepresentation.invariantSubspace A.kernelRepresentation I).subtype

@[simp]
theorem kernelSubtype_apply (x : A.inertiaKernelRepresentation I) :
    kernelSubtype A I x = x.val.val := rfl

theorem kernelSubtype_injective : Function.Injective (kernelSubtype A I) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem monodromy_kernelSubtype (x : A.inertiaKernelRepresentation I) :
    A.monodromy (kernelSubtype A I x) = 0 := x.val.property

theorem representation_kernelSubtype (x : A.inertiaKernelRepresentation I) (i : I) :
    A.representation i (kernelSubtype A I x) = kernelSubtype A I x :=
  congrArg Subtype.val (x.property i)

theorem representation_kernelSubtype_of (x : A.inertiaKernelRepresentation I) (g : G) :
    A.representation g (kernelSubtype A I x) = kernelSubtype A I (kernelOperator A I g x) := rfl

/-- A vector killed by monodromy and fixed by inertia, as an element of the kernel. -/
def kernelMk (v : A) (hN : A.monodromy v = 0) (hI : ∀ i : I, A.representation i v = v) :
    A.inertiaKernelRepresentation I :=
  ⟨⟨v, hN⟩, fun i => Subtype.ext (hI i)⟩

@[simp]
theorem kernelSubtype_kernelMk (v : A) (hN : A.monodromy v = 0)
    (hI : ∀ i : I, A.representation i v = v) :
    kernelSubtype A I (kernelMk A I v hN hI) = v := rfl

variable {A I}

/-- An injective linear map whose image is exactly the inertia-fixed monodromy kernel. -/
def kernelEquivOfEmbedding (φ : W →ₗ[K] A) (hinj : Function.Injective φ)
    (hmem : ∀ w, A.monodromy (φ w) = 0 ∧ ∀ i : I, A.representation i (φ w) = φ w)
    (hsurj : ∀ v : A, A.monodromy v = 0 → (∀ i : I, A.representation i v = v) →
      ∃ w, φ w = v) :
    W ≃ₗ[K] A.inertiaKernelRepresentation I :=
  LinearEquiv.ofBijective
    { toFun := fun w => kernelMk A I (φ w) (hmem w).1 (hmem w).2
      map_add' := fun w w' => kernelSubtype_injective A I (map_add φ w w')
      map_smul' := fun c w => kernelSubtype_injective A I (by
        simp only [RingHom.id_apply, map_smul, kernelSubtype_kernelMk]) }
    ⟨fun w w' h => hinj (congrArg (kernelSubtype A I) h), fun x => by
      obtain ⟨w, hw⟩ := hsurj (kernelSubtype A I x) (monodromy_kernelSubtype A I x)
        (representation_kernelSubtype A I x)
      exact ⟨w, kernelSubtype_injective A I hw⟩⟩

@[simp]
theorem kernelSubtype_kernelEquivOfEmbedding (φ : W →ₗ[K] A) (hinj : Function.Injective φ)
    (hmem : ∀ w, A.monodromy (φ w) = 0 ∧ ∀ i : I, A.representation i (φ w) = φ w)
    (hsurj : ∀ v : A, A.monodromy v = 0 → (∀ i : I, A.representation i v = v) →
      ∃ w, φ w = v) (w : W) :
    kernelSubtype A I (kernelEquivOfEmbedding φ hinj hmem hsurj w) = φ w := rfl

/-- If an embedding identifies `W` with the inertia-fixed monodromy kernel and
intertwines `T` with the action of `g`, the Euler polynomial is that of `T`. -/
theorem eulerPolynomial_eq_of_embedding [FiniteDimensional K W] (g : G)
    (T : Module.End K W) (φ : W →ₗ[K] A) (hinj : Function.Injective φ)
    (hmem : ∀ w, A.monodromy (φ w) = 0 ∧ ∀ i : I, A.representation i (φ w) = φ w)
    (hsurj : ∀ v : A, A.monodromy v = 0 → (∀ i : I, A.representation i v = v) →
      ∃ w, φ w = v)
    (hcomm : ∀ w, A.representation g (φ w) = φ (T w)) :
    eulerPolynomial A I g = LocalFactor.eulerPolynomial T := by
  let e := kernelEquivOfEmbedding φ hinj hmem hsurj
  have hconj : e.conj T = kernelOperator A I g := by
    apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    apply kernelSubtype_injective A I
    rw [← representation_kernelSubtype_of]
    exact (hcomm w).symm
  rw [eulerPolynomial, ← hconj, eulerPolynomial_conj]

/-- The rational version of `eulerPolynomial_eq_of_embedding`. -/
theorem rationalLFactor_eq_of_embedding [FiniteDimensional K W] (g : G)
    (T : Module.End K W) (φ : W →ₗ[K] A) (hinj : Function.Injective φ)
    (hmem : ∀ w, A.monodromy (φ w) = 0 ∧ ∀ i : I, A.representation i (φ w) = φ w)
    (hsurj : ∀ v : A, A.monodromy v = 0 → (∀ i : I, A.representation i v = v) →
      ∃ w, φ w = v)
    (hcomm : ∀ w, A.representation g (φ w) = φ (T w)) :
    rationalLFactor A I g = LocalFactor.rationalFactor T := by
  change (algebraMap K[X] (RatFunc K) (eulerPolynomial A I g))⁻¹ = _
  rw [eulerPolynomial_eq_of_embedding g T φ hinj hmem hsurj hcomm]
  rfl

end Embedding

section DirectSum

variable {r : ℕ} (A : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν)
  (I : Subgroup G) [I.Normal]

/-- The coordinates of a vector in a finite direct sum of pairs. -/
def directSumCoord : WeilDeligneRepresentation.directSum A ≃ₗ[K] ∀ i, A i :=
  DirectSum.linearEquivFunOnFintype K (Fin r) fun i => A i

theorem directSumCoord_monodromy (v : WeilDeligneRepresentation.directSum A) (i : Fin r) :
    directSumCoord A ((WeilDeligneRepresentation.directSum A).monodromy v) i =
      (A i).monodromy (directSumCoord A v i) := rfl

theorem directSumCoord_representation (g : G) (v : WeilDeligneRepresentation.directSum A)
    (i : Fin r) :
    directSumCoord A ((WeilDeligneRepresentation.directSum A).representation g v) i =
      (A i).representation g (directSumCoord A v i) := rfl

/-- The family of inertia-fixed monodromy kernels, assembled in the direct sum. -/
def directSumKernelEmbedding :
    (∀ i, (A i).inertiaKernelRepresentation I) →ₗ[K]
      WeilDeligneRepresentation.directSum A :=
  (directSumCoord A).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => kernelSubtype (A i) I ∘ₗ LinearMap.proj i

theorem directSumCoord_kernelEmbedding (y : ∀ i, (A i).inertiaKernelRepresentation I)
    (i : Fin r) :
    directSumCoord A (directSumKernelEmbedding A I y) i = kernelSubtype (A i) I (y i) := by
  change directSumCoord A ((directSumCoord A).symm fun i => kernelSubtype (A i) I (y i)) i = _
  rw [LinearEquiv.apply_symm_apply]

/-- The inertia-fixed monodromy kernel of a finite direct sum is the product of
the kernels, and the action of every element is componentwise. -/
theorem eulerPolynomial_directSum (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.directSum A) I g =
      ∏ i, eulerPolynomial (A i) I g := by
  rw [eulerPolynomial_eq_of_embedding g
    (LinearMap.pi fun i => kernelOperator (A i) I g ∘ₗ LinearMap.proj i)
    (directSumKernelEmbedding A I)]
  · exact LocalFactor.eulerPolynomial_pi _
  · intro y y' h
    funext i
    apply kernelSubtype_injective (A i) I
    rw [← directSumCoord_kernelEmbedding, ← directSumCoord_kernelEmbedding, h]
  · intro y
    constructor
    · apply (directSumCoord A).injective
      funext i
      rw [directSumCoord_monodromy, directSumCoord_kernelEmbedding, monodromy_kernelSubtype,
        map_zero, Pi.zero_apply]
    · intro i'
      apply (directSumCoord A).injective
      funext i
      rw [directSumCoord_representation, directSumCoord_kernelEmbedding,
        representation_kernelSubtype]
  · intro v hN hI
    refine ⟨fun i => kernelMk (A i) I (directSumCoord A v i) ?_ ?_, ?_⟩
    · rw [← directSumCoord_monodromy, hN, map_zero, Pi.zero_apply]
    · intro i'
      rw [← directSumCoord_representation, hI i']
    · apply (directSumCoord A).injective
      funext i
      rw [directSumCoord_kernelEmbedding, kernelSubtype_kernelMk]
  · intro y
    apply (directSumCoord A).injective
    funext i
    rw [directSumCoord_representation, directSumCoord_kernelEmbedding,
      directSumCoord_kernelEmbedding]
    rfl

/-- Rational L-factors of finite direct sums are products. -/
theorem rationalLFactor_directSum (g : G) :
    rationalLFactor (WeilDeligneRepresentation.directSum A) I g =
      ∏ i, rationalLFactor (A i) I g := by
  change (algebraMap K[X] (RatFunc K)
      (eulerPolynomial (WeilDeligneRepresentation.directSum A) I g))⁻¹ =
    ∏ i, (algebraMap K[X] (RatFunc K) (eulerPolynomial (A i) I g))⁻¹
  rw [eulerPolynomial_directSum, map_prod, Finset.prod_inv_distrib]

end DirectSum

section Tensor

variable {r : ℕ}

/-- Tensor products of pairs distribute over finite direct sums on the left. -/
def tensorDirectSumLeft (B : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (C : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.directSum B) C)
      (WeilDeligneRepresentation.directSum fun i => WeilDeligneRepresentation.tensor (B i) C) where
  representationEquiv :=
    Representation.Equiv.mk (TensorProduct.directSumLeft K K (fun i => B i) C) fun g =>
      LocalFactor.directSumLeft_comp_map (fun i => (B i).representation g) (C.representation g)
  comm_monodromy :=
    LocalFactor.directSumLeft_comp_monodromy (fun i => (B i).monodromy) C.monodromy

/-- Tensor products of pairs distribute over finite direct sums on the right. -/
def tensorDirectSumRight (C : WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (B : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor C (WeilDeligneRepresentation.directSum B))
      (WeilDeligneRepresentation.directSum fun i => WeilDeligneRepresentation.tensor C (B i)) where
  representationEquiv :=
    Representation.Equiv.mk (TensorProduct.directSumRight K K C fun i => B i) fun g =>
      LocalFactor.directSumRight_comp_map (C.representation g) fun i => (B i).representation g
  comm_monodromy :=
    LocalFactor.directSumRight_comp_monodromy C.monodromy fun i => (B i).monodromy

variable (I : Subgroup G) [I.Normal] (g : G)

/-- Pair L-factors are multiplicative in finite direct sums of the first argument. -/
theorem pairLFactor_directSum_left (B : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (C : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    pairLFactor (WeilDeligneRepresentation.directSum B) C I g = ∏ i, pairLFactor (B i) C I g := by
  rw [pairLFactor, rationalLFactor_eq_of_equiv I (tensorDirectSumLeft B C) g,
    rationalLFactor_directSum]
  rfl

/-- Pair L-factors are multiplicative in finite direct sums of the second argument. -/
theorem pairLFactor_directSum_right (C : WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (B : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    pairLFactor C (WeilDeligneRepresentation.directSum B) I g = ∏ i, pairLFactor C (B i) I g := by
  rw [pairLFactor, rationalLFactor_eq_of_equiv I (tensorDirectSumRight C B) g,
    rationalLFactor_directSum]
  rfl

/-- The pair L-factor of two finite direct sums is the product over all pairs of
summands. -/
theorem pairLFactor_directSum_directSum {t : ℕ}
    (B : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B' : Fin t → WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    pairLFactor (WeilDeligneRepresentation.directSum B) (WeilDeligneRepresentation.directSum B')
        I g =
      ∏ i, ∏ j, pairLFactor (B i) (B' j) I g := by
  rw [pairLFactor_directSum_left]
  exact Finset.prod_congr rfl fun i _ => pairLFactor_directSum_right I g (B i) B'

/-- The double-product formula for pairs equivalent to finite direct sums. -/
theorem pairLFactor_eq_prod_of_equiv_directSum {t : ℕ}
    (B : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B' : Fin t → WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (A' : WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (e : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B) A)
    (e' : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B') A') :
    pairLFactor A A' I g = ∏ i, ∏ j, pairLFactor (B i) (B' j) I g := by
  rw [← pairLFactor_eq_of_equiv I g e e', pairLFactor_directSum_directSum]

end Tensor

end WeilDeligne

end Langlands.LocalFactor
