import Langlands.Algebra.KroneckerInduction
import Langlands.Algebra.BrauerCorestriction.BrauerClass
import Langlands.Algebra.BrauerCorestriction.PiMatrixKronecker
import Langlands.Algebra.GaloisTwistedMatrix
import Langlands.Algebra.BrauerGroup
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.FieldTheory.Normal.Defs

/-! # The corestriction of a descended matrix algebra is a descended matrix algebra -/

noncomputable section

universe u

open scoped Matrix TensorProduct
open TensorProduct PiTensorProduct

namespace Langlands.Algebra.CorestrictionTwistedFixed

open Langlands.BrauerCorestriction Langlands.Algebra.KroneckerInduction
  Langlands.Algebra.GaloisTwistedMatrix Langlands.PiTensorSemilinear

section MapLemmas

variable {R K : Type*} [CommSemiring R] [Field K] [Algebra R K] {n : Type*}

theorem map_mul_algEquiv [Fintype n] (τ : K ≃ₐ[R] K) (M M' : Matrix n n K) :
    (M * M').map τ = M.map τ * M'.map τ :=
  Matrix.map_mul (f := (τ : K →+* K))

theorem map_add_algEquiv (τ : K ≃ₐ[R] K) (M M' : Matrix n n K) :
    (M + M').map τ = M.map τ + M'.map τ :=
  Matrix.map_add τ (map_add τ) M M'

theorem map_smul_algEquiv (τ : K ≃ₐ[R] K) (c : K) (M : Matrix n n K) :
    (c • M).map τ = τ c • M.map τ :=
  Matrix.map_smul' τ c M (map_mul τ)

theorem piKronecker_map_algEquiv {D : Type*} [Fintype D] (τ : K ≃ₐ[R] K)
    (Z : D → Matrix n n K) :
    (piKronecker Z).map τ = piKronecker (fun σ => (Z σ).map τ) :=
  piKronecker_map (τ : K →+* K) Z

end MapLemmas

section LibraryKronecker

/-- The Library's Kronecker product `kroneckerMultilinear` of a family of `m × m` matrices over a
field is `piKronecker`. -/
theorem kroneckerMultilinear_eq_piKronecker {F : Type*} [Field F] {D : Type*} [Fintype D]
    [DecidableEq D] {m : ℕ} (Z : D → Matrix (Fin m) (Fin m) F) :
    kroneckerMultilinear F D m Z = piKronecker Z :=
  rfl

end LibraryKronecker

section Factor

variable {k E N K : Type u} [Field k] [Field E] [Field N] [Field K]
  [Algebra k E] [Algebra k N] [Algebra k K] [Algebra E K] [Algebra N K]
  [IsScalarTower k E K] [IsScalarTower k N K]
  {n : Type} [Fintype n] [DecidableEq n]
  {A : Type u} [Ring A] [Algebra E A] (j : A →ₐ[E] Matrix n n K)

/-- The identity map of `N`, from the twisted copy `Twist σ = N` to `N`, as a ring
homomorphism. It makes the coercion explicit for rewriting. -/
def twistVal (σ : E →ₐ[k] N) : Twist σ →+* N := RingHom.id N

omit [Algebra k K] [Algebra E K] [Algebra N K] [IsScalarTower k E K] [IsScalarTower k N K] in
theorem twistVal_smul (σ : E →ₐ[k] N) (r : E) (x : Twist σ) :
    twistVal σ (r • x) = σ r * twistVal σ x := rfl

omit [Algebra k K] [Algebra E K] [Algebra N K] [IsScalarTower k E K] [IsScalarTower k N K] in
theorem twistVal_algebraMap (σ : E →ₐ[k] N) (c : N) :
    twistVal σ (algebraMap N (Twist σ) c) = c := rfl

/-- The additive map `x ⊗ a ↦ x • s(j a)` on the conjugate `A^σ = N ⊗_{σ,E} A`, for an
automorphism `s` of `K` extending `σ`. -/
def factorAddHom (σ : E →ₐ[k] N) (s : K ≃ₐ[k] K)
    (hs : ∀ x : E, s (algebraMap E K x) = algebraMap N K (σ x)) :
    Conj A σ →+ Matrix n n K :=
  TensorProduct.liftAddHom
    { toFun := fun x : Twist σ =>
        { toFun := fun a : A => algebraMap N K (twistVal σ x) • (j a).map s
          map_zero' := by
            rw [map_zero j, Matrix.map_zero s (map_zero s), smul_zero]
          map_add' := fun a b => by
            rw [map_add j, map_add_algEquiv, smul_add] }
      map_zero' := by
        ext a : 1
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        rw [map_zero (twistVal σ), map_zero, zero_smul]
      map_add' := fun x y => by
        ext a : 1
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
        rw [map_add (twistVal σ), map_add, add_smul] }
    (fun r x a => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [twistVal_smul, map_smul j r a,
        Matrix.map_smulₛₗ s (fun r : E => s (algebraMap E K r)) r
          (fun c => by rw [Algebra.smul_def, map_mul, smul_eq_mul]),
        hs, smul_smul, map_mul, mul_comm (algebraMap N K (σ r))])

/-- The factor homomorphism `A^σ → M_n(K)`, `x ⊗ a ↦ x • s(j a)`. -/
def factor (σ : E →ₐ[k] N) (s : K ≃ₐ[k] K)
    (hs : ∀ x : E, s (algebraMap E K x) = algebraMap N K (σ x)) :
    Conj A σ →ₐ[N] Matrix n n K :=
  { factorAddHom j σ s hs with
    map_one' := by
      change algebraMap N K (twistVal σ 1) • (j 1).map s = 1
      rw [map_one (twistVal σ), map_one, one_smul, map_one j,
        Matrix.map_one s (map_zero s) (map_one s)]
    map_mul' := fun x y => by
      change factorAddHom j σ s hs (x * y) =
        factorAddHom j σ s hs x * factorAddHom j σ s hs y
      induction x using TensorProduct.inductionOn with
      | tmul x a =>
        induction y using TensorProduct.inductionOn with
        | tmul y b =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          change algebraMap N K (twistVal σ (x * y)) • (j (a * b)).map s =
            (algebraMap N K (twistVal σ x) • (j a).map s) *
              (algebraMap N K (twistVal σ y) • (j b).map s)
          rw [map_mul (twistVal σ), map_mul (algebraMap N K), map_mul j,
            map_mul_algEquiv, smul_mul_smul_comm]
        | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
      | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
    commutes' := fun c => by
      change algebraMap N K (twistVal σ (algebraMap N (Twist σ) c)) • (j 1).map s = _
      rw [twistVal_algebraMap, map_one j, Matrix.map_one s (map_zero s) (map_one s),
        Algebra.algebraMap_eq_smul_one (A := Matrix n n K) c, algebraMap_smul] }

omit [IsScalarTower k E K] [IsScalarTower k N K] in
@[simp]
theorem factor_tmul (σ : E →ₐ[k] N) (s : K ≃ₐ[k] K)
    (hs : ∀ x : E, s (algebraMap E K x) = algebraMap N K (σ x)) (x : Twist σ) (a : A) :
    factor j σ s hs (x ⊗ₜ a) = algebraMap N K (twistVal σ x) • (j a).map s :=
  rfl

variable [Normal k N]

/-- **Factorwise Galois intertwining.** Let `τ ∈ Gal(K/k)` restrict to `g` on `N`, with
`g ∘ σ = σ'`, and let `h₀ ∈ Gal(K/E)` satisfy `τ ∘ s = s' ∘ h₀`, where `s`, `s'` extend `σ`,
`σ'`. If `Q h₀ * j a = (j a).map h₀ * Q h₀` for all `a`, then
`s'(Q h₀) * factor σ' (g y) = τ(factor σ y) * s'(Q h₀)` for every `y ∈ A^σ`. -/
theorem factor_conjMap (Q : (K ≃ₐ[E] K) → Matrix n n K) (τ : K ≃ₐ[k] K)
    (σ σ' : E →ₐ[k] N) (s s' : K ≃ₐ[k] K)
    (hs : ∀ x : E, s (algebraMap E K x) = algebraMap N K (σ x))
    (hs' : ∀ x : E, s' (algebraMap E K x) = algebraMap N K (σ' x))
    (hσ : ∀ l, τ.restrictNormal N (σ l) = σ' l) (h₀ : K ≃ₐ[E] K)
    (hrel : τ * s = s' * h₀.restrictScalars k)
    (hj : ∀ a, Q h₀ * j a = (j a).map h₀ * Q h₀) (y : Conj A σ) :
    (Q h₀).map s' * factor j σ' s' hs' (conjMap A (τ.restrictNormal N) σ σ' hσ y) =
      (factor j σ s hs y).map τ * (Q h₀).map s' := by
  induction y using TensorProduct.inductionOn with
  | tmul x a =>
    rw [conjMap_tmul, factor_tmul, factor_tmul, map_smul_algEquiv]
    rw [show twistVal σ' (twistHom (τ.restrictNormal N) σ σ' hσ x) =
        τ.restrictNormal N (twistVal σ x) from rfl,
      ← AlgEquiv.restrictNormal_commutes τ N (twistVal σ x), mul_smul_comm, smul_mul_assoc]
    congr 1
    have hcomp : ∀ c : K, s' (h₀ c) = τ (s c) := fun c => by
      have := congrArg (fun f : K ≃ₐ[k] K => f c) hrel
      simpa [AlgEquiv.mul_apply] using this.symm
    have h := congrArg (fun M => M.map s') (hj a)
    simp only [map_mul_algEquiv, Matrix.map_map] at h
    rw [h, Matrix.map_map]
    congr 2
    funext c
    exact hcomp c
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, map_add, mul_add, h₁, h₂, map_add, map_add_algEquiv, add_mul]

end Factor

section Corestriction

variable {k E N K : Type u} [Field k] [Field E] [Field N] [Field K]
  [Algebra k E] [Algebra k N] [Algebra k K] [Algebra E K] [Algebra N K]
  [IsScalarTower k E K] [IsScalarTower k N K]
  {n : Type} [Fintype n] [DecidableEq n]
  {A : Type u} [Ring A] [Algebra E A] (j : A →ₐ[E] Matrix n n K)
  {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin m) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
  (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))

/-- The multilinear map `(y_i)_i ↦ ⨂_i factor_{σ_i}(y_i)`, indexing the embeddings by
`Fin m`. -/
def corMatrixMultilinear :
    MultilinearMap N (fun i : Fin m => Conj A (e.symm i))
      (Matrix (Fin m → n) (Fin m → n) K) :=
  (piKroneckerMultilinear N).compLinearMap fun i =>
    (factor j (e.symm i) (ε (e.symm i)) (hε (e.symm i))).toLinearMap

omit [IsScalarTower k E K] [IsScalarTower k N K] in
theorem corMatrixMultilinear_apply (y : ∀ i : Fin m, Conj A (e.symm i)) :
    corMatrixMultilinear j e ε hε y =
      piKronecker fun i => factor j (e.symm i) (ε (e.symm i)) (hε (e.symm i)) (y i) :=
  rfl

/-- Reindexing the tensor product of the conjugates along `e`, as an algebra map. -/
def reindexAlgHom :
    ConjTensor k E N A →ₐ[N] ⨂[N] i : Fin m, Conj A (e.symm i) :=
  AlgHom.ofLinearMap (reindex N (fun σ => Conj A σ) e).toLinearMap (reindex_one N e)
    (fun x y => reindex_mul N e x y)

/-- The matrix realization `⨂_σ A^σ → M_{n^m}(K)` of the tensor product of the conjugates. -/
def corMatrixHom : ConjTensor k E N A →ₐ[N] Matrix (Fin m → n) (Fin m → n) K :=
  (PiTensorProduct.liftAlgHom (corMatrixMultilinear j e ε hε)
      (by
        rw [corMatrixMultilinear_apply]
        simp only [Pi.one_apply, map_one]
        exact piKronecker_one)
      (fun x y => by
        rw [corMatrixMultilinear_apply, corMatrixMultilinear_apply,
          corMatrixMultilinear_apply]
        simp only [Pi.mul_apply, map_mul]
        exact piKronecker_mul _ _)).comp
    (reindexAlgHom e)

omit [IsScalarTower k E K] [IsScalarTower k N K] in
theorem corMatrixHom_tprod (z : ∀ σ : E →ₐ[k] N, Conj A σ) :
    corMatrixHom j e ε hε (tprod N z) =
      piKronecker fun i => factor j (e.symm i) (ε (e.symm i)) (hε (e.symm i)) (z (e.symm i)) := by
  simp only [corMatrixHom, reindexAlgHom, AlgHom.comp_apply, AlgHom.ofLinearMap_apply,
    LinearEquiv.coe_toLinearMap, reindex_tprod, liftAlgHom_apply, lift.tprod]
  rfl

variable [Normal k N]

/-- The stabilizer correction `ε(gσ)⁻¹ τ ε(σ) ∈ Gal(K/E)`. -/
def stabCorrection (τ : K ≃ₐ[k] K) (σ : E →ₐ[k] N) : K ≃ₐ[E] K :=
  AlgEquiv.ofRingEquiv (f := ((ε (galPerm (τ.restrictNormal N) σ))⁻¹ * τ * ε σ).toRingEquiv)
    (fun x => by
      change (ε (galPerm (τ.restrictNormal N) σ)).symm (τ (ε σ (algebraMap E K x))) =
        algebraMap E K x
      rw [hε, ← AlgEquiv.restrictNormal_commutes, AlgEquiv.symm_apply_eq, hε,
        galPerm_apply_apply])

theorem stabCorrection_restrictScalars (τ : K ≃ₐ[k] K) (σ : E →ₐ[k] N) :
    τ * ε σ = ε (galPerm (τ.restrictNormal N) σ) *
      (stabCorrection ε hε τ σ).restrictScalars k := by
  ext x
  change τ (ε σ x) = ε (galPerm (τ.restrictNormal N) σ)
    ((ε (galPerm (τ.restrictNormal N) σ)).symm (τ (ε σ x)))
  rw [AlgEquiv.apply_symm_apply]

/-- The induction data on `Fin m`: lifts `ε (e.symm i)`, the permutation induced by
`τ|_N` on the embeddings, and the stabilizer corrections. -/
def inductionData : InductionData k E K (Fin m) where
  ext i := ε (e.symm i)
  perm τ := (e.symm.trans (galPerm (τ.restrictNormal N))).trans e
  stab τ i := stabCorrection ε hε τ (e.symm i)
  mul_ext τ i := by
    rw [stabCorrection_restrictScalars ε hε τ (e.symm i)]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

theorem inductionData_perm_symm_apply (τ : K ≃ₐ[k] K) (i : Fin m) :
    e.symm (((inductionData e ε hε).perm τ).symm i) =
      (galPerm (τ.restrictNormal N)).symm (e.symm i) := by
  simp [inductionData]

/-- **Galois intertwining of the matrix realization.** The induced matrix of `τ` intertwines
the realization of `τ|_N(v)` with the image under `τ` of the realization of `v`. -/
theorem inducedMatrix_mul_corMatrixHom (Q : (K ≃ₐ[E] K) → Matrix n n K)
    (hj : ∀ h a, Q h * j a = (j a).map h * Q h) (τ : K ≃ₐ[k] K) (v : ConjTensor k E N A) :
    inducedMatrix (inductionData e ε hε) Q τ *
        corMatrixHom j e ε hε (actMap A (τ.restrictNormal N) v) =
      (corMatrixHom j e ε hε v).map τ * inducedMatrix (inductionData e ε hε) Q τ := by
  set g := τ.restrictNormal N
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r z =>
    rw [map_smulₛₗ (actMap A g), actMap_tprod, map_smul, map_smul, corMatrixHom_tprod,
      corMatrixHom_tprod, ← algebraMap_smul K, ← algebraMap_smul K r, map_smul_algEquiv,
      mul_smul_comm, smul_mul_assoc]
    congr 1
    · exact AlgEquiv.restrictNormal_commutes τ N r
    set I := inductionData e ε hε
    set π := I.perm τ
    let Ψ : (E →ₐ[k] N) → Matrix n n K := fun σ => (factor j σ (ε σ) (hε σ) (z σ)).map τ
    rw [piKronecker_map_algEquiv]
    have key := piKronecker_intertwine π (inducedFactor I Q τ)
      (fun i => Ψ (e.symm i))
      (fun i => factor j (e.symm i) (ε (e.symm i)) (hε (e.symm i))
        (conjMap A g ((galPerm g).symm (e.symm i)) (e.symm i) (apply_galPerm_symm g _)
          (z ((galPerm g).symm (e.symm i)))))
      (fun i => by
        have hX : Ψ (e.symm (π.symm i)) = Ψ ((galPerm g).symm (e.symm i)) :=
          congrArg Ψ (inductionData_perm_symm_apply e ε hε τ i)
        rw [hX]
        have hrel := I.mul_ext τ (π.symm i)
        have hext1 : I.ext (π.symm i) = ε ((galPerm g).symm (e.symm i)) :=
          congrArg ε (inductionData_perm_symm_apply e ε hε τ i)
        have hext2 : I.ext (I.perm τ (π.symm i)) = ε (e.symm i) := by
          simp only [π, Equiv.apply_symm_apply]
          rfl
        rw [hext1, hext2] at hrel
        exact factor_conjMap j Q τ ((galPerm g).symm (e.symm i)) (e.symm i)
          (ε ((galPerm g).symm (e.symm i))) (ε (e.symm i)) (hε _) (hε _)
          (apply_galPerm_symm g _) (I.stab τ (π.symm i)) hrel (hj _) _)
    exact key
  | add x y hx hy =>
    rw [map_add, map_add, mul_add, hx, hy, map_add, map_add_algEquiv, add_mul]

/-- The realization of a Galois-fixed tensor lies in the algebra fixed by the induced twisting
matrices. -/
theorem corMatrixHom_mem_twistedFixed (Q : (K ≃ₐ[E] K) → Matrix n n K)
    (hj : ∀ h a, Q h * j a = (j a).map h * Q h) {v : ConjTensor k E N A}
    (hv : v ∈ corAlg k E N A) :
    corMatrixHom j e ε hε v ∈ twistedFixed (inducedMatrix (inductionData e ε hε) Q) := by
  intro τ
  have h := inducedMatrix_mul_corMatrixHom j e ε hε Q hj τ v
  rwa [(mem_corAlg k E N A v).mp hv (τ.restrictNormal N)] at h

end Corestriction

section Dimension

variable {k E N K : Type u} [Field k] [Field E] [Field N] [Field K]
  [Algebra k E] [Algebra k N] [Algebra k K] [Algebra E K] [Algebra N K]
  [IsScalarTower k E K] [IsScalarTower k N K] [FiniteDimensional k N] [IsGalois k N]
  {n : Type} [Fintype n] [DecidableEq n]
  {A : Type u} [Ring A] [Algebra E A] (j : A →ₐ[E] Matrix n n K)
  {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin m) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
  (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))

/-- The matrix realization on the descended algebra `corAlg k E N A`, as a `k`-algebra
homomorphism. -/
def corAlgHom : corAlg k E N A →ₐ[k] Matrix (Fin m → n) (Fin m → n) K :=
  ((corMatrixHom j e ε hε).restrictScalars k).comp (corAlg k E N A).val

omit [FiniteDimensional k N] [IsScalarTower k E K] [IsGalois k N] in
theorem corAlgHom_apply (v : corAlg k E N A) :
    corAlgHom j e ε hε v = corMatrixHom j e ε hε (v : ConjTensor k E N A) :=
  rfl

variable (Q : (K ≃ₐ[E] K) → Matrix n n K) (hj : ∀ h a, Q h * j a = (j a).map h * Q h)

omit [FiniteDimensional k N] in
include hj in
/-- The realization of the descended algebra lies in the twisted-fixed algebra of the induced
matrices. -/
theorem corAlgHom_range_le :
    (corAlgHom j e ε hε).range ≤ twistedFixed (inducedMatrix (inductionData e ε hε) Q) := by
  rintro _ ⟨v, rfl⟩
  exact corMatrixHom_mem_twistedFixed j e ε hε Q hj v.2

variable [FiniteDimensional k E] [FiniteDimensional E A] [Algebra.IsCentral E A] [IsSimpleRing A]
  [Nonempty n]

omit [IsScalarTower k E K] in
/-- The realization of the descended algebra is injective, since the descended algebra is
simple. -/
theorem corAlgHom_injective : Function.Injective (corAlgHom j e ε hε) := by
  have := isSimpleRing_corAlg k E N A
  exact RingHom.injective (R := corAlg k E N A) (S := Matrix (Fin m → n) (Fin m → n) K)
    (corAlgHom j e ε hε).toRingHom

omit [Algebra.IsCentral E A] [IsSimpleRing A] [Nonempty n] [DecidableEq n] in
include e in
/-- If `dim_E A = n²`, the descended algebra has dimension `(n^m)²`. -/
theorem finrank_corAlg_eq_card (hA : Module.finrank E A = Fintype.card n * Fintype.card n) :
    Module.finrank k (corAlg k E N A) =
      Fintype.card (Fin m → n) * Fintype.card (Fin m → n) := by
  rw [finrank_corAlg_eq_pow, hA, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin, mul_pow]

variable [IsGalois k K] (hQ : ∀ h, IsUnit (Q h))
  (hA : Module.finrank E A = Fintype.card n * Fintype.card n)

include hj hQ hA in
/-- The realization of the descended algebra spans the full matrix algebra over `K`. -/
theorem span_corAlgHom_range :
    Submodule.span K ((corAlgHom j e ε hε).range : Set (Matrix (Fin m → n) (Fin m → n) K)) =
      ⊤ := by
  set R := (corAlgHom j e ε hε).range with hR
  have hC := isUnit_inducedMatrix (inductionData e ε hε) Q hQ
  have hle : R ≤ twistedFixed (inducedMatrix (inductionData e ε hε) Q) :=
    corAlgHom_range_le j e ε hε Q hj
  have : FiniteDimensional k R := GaloisTwistedMatrix.finiteDimensional _ hC R hle
  have hfin : Module.finrank k R = Fintype.card (Fin m → n) * Fintype.card (Fin m → n) := by
    rw [← (AlgEquiv.ofInjective _ (corAlgHom_injective j e ε hε)).toLinearEquiv.finrank_eq,
      finrank_corAlg_eq_card e hA]
  let b := Module.finBasis k R
  have hli : LinearIndependent K (fun i => ((b i : R) : Matrix (Fin m → n) (Fin m → n) K)) :=
    linearIndependent_of_le_twistedFixed _ hC _ (fun i => hle (b i).2)
      (b.linearIndependent.map' R.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
  have hcard : Fintype.card (Fin (Module.finrank k R)) =
      Module.finrank K (Matrix (Fin m → n) (Fin m → n) K) := by
    rw [Fintype.card_fin, hfin, Module.finrank_matrix, Module.finrank_self, mul_one]
  refine eq_top_iff.mpr ((hli.span_eq_top_of_card_eq_finrank' hcard).ge.trans
    (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact (b i).2

include hj hQ hA in
/-- The twisted-fixed algebra of the induced matrices spans the full matrix algebra over `K`. -/
theorem span_twistedFixed_inducedMatrix :
    Submodule.span K (twistedFixed (inducedMatrix (inductionData e ε hε) Q) :
      Set (Matrix (Fin m → n) (Fin m → n) K)) = ⊤ :=
  eq_top_iff.mpr ((span_corAlgHom_range j e ε hε Q hj hQ hA).ge.trans
    (Submodule.span_mono (corAlgHom_range_le j e ε hε Q hj)))

include hj hQ hA in
/-- The realization of the descended algebra is the whole twisted-fixed algebra of the induced
matrices. -/
theorem corAlgHom_range_eq :
    (corAlgHom j e ε hε).range = twistedFixed (inducedMatrix (inductionData e ε hε) Q) := by
  have hC := isUnit_inducedMatrix (inductionData e ε hε) Q hQ
  have hspan := span_twistedFixed_inducedMatrix j e ε hε Q hj hQ hA
  have := GaloisTwistedMatrix.finiteDimensional _ hC _ le_rfl
  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_eq (corAlgHom_range_le j e ε hε Q hj)
  change Module.finrank k (corAlgHom j e ε hε).range =
    Module.finrank k (twistedFixed (inducedMatrix (inductionData e ε hε) Q))
  rw [GaloisTwistedMatrix.finrank_eq _ hC _ le_rfl hspan,
    ← (AlgEquiv.ofInjective _ (corAlgHom_injective j e ε hε)).toLinearEquiv.finrank_eq,
    finrank_corAlg_eq_card e hA]

/-- **The descended algebra as a twisted-fixed algebra.** The tensor descent of the conjugates
of `A` is isomorphic to the twisted-fixed algebra of the induced matrices. -/
def corAlgEquivTwistedFixed :
    corAlg k E N A ≃ₐ[k] twistedFixed (inducedMatrix (inductionData e ε hε) Q) :=
  (AlgEquiv.ofInjective _ (corAlgHom_injective j e ε hε)).trans
    (Subalgebra.equivOfEq _ _ (corAlgHom_range_eq j e ε hε Q hj hQ hA))

end Dimension

section Brauer

variable {k E N K : Type u} [Field k] [Field E] [Field N] [Field K]
  [Algebra k E] [Algebra k N] [Algebra k K] [Algebra E K] [Algebra N K]
  [IsScalarTower k E K] [IsScalarTower k N K] [FiniteDimensional k N] [IsGalois k N]
  [FiniteDimensional k E] [IsGalois k K]
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  (A : CSA.{u, u} E) (j : A →ₐ[E] Matrix n n K)
  {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin m) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
  (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))
  (Q : (K ≃ₐ[E] K) → Matrix n n K) (hj : ∀ h a, Q h * j a = (j a).map h * Q h)
  (hQ : ∀ h, IsUnit (Q h)) (hA : Module.finrank E A = Fintype.card n * Fintype.card n)

/-- **Brauer class of the descended algebra.** The class of the tensor descent of `A` over `N`
is the class of the twisted-fixed algebra of the induced matrices. -/
theorem classOf_corCSAOf_eq :
    Brauer.classOf (corCSAOf k E N A) =
      Brauer.classOf (toCSA (inducedMatrix (inductionData e ε hε) Q)
        (isUnit_inducedMatrix (inductionData e ε hε) Q hQ) _ le_rfl
        (span_twistedFixed_inducedMatrix j e ε hε Q hj hQ hA)) :=
  Brauer.classOf_eq_of_algEquiv (corAlgEquivTwistedFixed j e ε hε Q hj hQ hA)

end Brauer

end Langlands.Algebra.CorestrictionTwistedFixed
