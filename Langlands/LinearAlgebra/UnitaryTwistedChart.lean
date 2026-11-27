import Langlands.LinearAlgebra.UnitaryTwistedDescent
import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart
import Langlands.GroupScheme.Examples.HermitianMatrixSplitting
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Charts of the special unitary group of a twisted matrix algebra

Let `M/K` be a finite Galois extension, `F` an intermediate field quadratic over `K`, and `x` a
twisted unitary projective cocycle with values in `GL_m(M)` relative to `H = Gal(M/F)`. The
twisted Galois descent of `M_m(M)` along `M/F` (`UnitaryTwistedDescent.galoisAction`) is a
central simple `F`-algebra `B`, and an automorphism `r ∉ H` induces a unitary involution `τ`
of `B`. This module makes this structure explicit and identifies, for every commutative
`K`-algebra `S` and every `K`-algebra map `ψ : M → S`, the special unitary points `SU(B, τ)(S)`
with `SL_m(S)` through the chart `s ⊗ b ↦ s • ψ(b)`. It also computes how the chart changes when
`ψ` is translated by an automorphism of `M`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.LinearAlgebra.UnitaryTwistedChart

open Matrix UnitaryTwistedDescent Langlands.GroupScheme Langlands.GroupScheme.Quaternionic
open Langlands.CentralSimple.UnitaryPoints

variable {K M : Type u} [Field K] [Field M] [Algebra K M]

/-- A twisted unitary projective cocycle relative to the index-two subgroup fixing the
intermediate field `F`, together with a chosen automorphism `r` outside that subgroup. -/
structure Cocycle (F : IntermediateField K M) (m : Type) [Fintype m] [DecidableEq m] where
  /-- The matrices of the cocycle. -/
  x : (M ≃ₐ[K] M) → GL m M
  /-- The fixing subgroup of `F` has index two. -/
  index_eq : F.fixingSubgroup.index = 2
  /-- The projective cocycle law for automorphisms fixing `F`. -/
  inner : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ)
  /-- The twisted projective cocycle law for automorphisms moving `F`. -/
  outer : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ)
  /-- The chosen automorphism outside the fixing subgroup of `F`. -/
  r : M ≃ₐ[K] M
  /-- The chosen automorphism moves `F`. -/
  r_not_mem : r ∉ F.fixingSubgroup

namespace Cocycle

variable {F : IntermediateField K M} {m : Type} [Fintype m] [DecidableEq m] (c : Cocycle F m)

/-- The twisted Galois action of `Gal(M/F)` on matrices. -/
abbrev action : Langlands.CentralSimple.SemilinearGaloisAction F M (Matrix m m M) :=
  galoisAction F c.index_eq c.inner c.outer

/-- The descended algebra: the matrices fixed by the twisted action of `Gal(M/F)`. -/
abbrev Alg : Subalgebra F (Matrix m m M) := c.action.fixed

/-- Elements of the descended algebra are fixed by the twisted action of every automorphism
fixing `F`. -/
theorem twistedAct_alg_of_mem {σ : M ≃ₐ[K] M} (hσ : σ ∈ F.fixingSubgroup) (b : c.Alg) :
    twistedAct F.fixingSubgroup c.x σ b = b :=
  twistedAct_of_mem_fixed F c.index_eq c.inner c.outer hσ b.2

/-- All automorphisms outside the fixing subgroup act in the same way on the descended
algebra. -/
theorem twistedAct_of_not_mem_eq {σ : M ≃ₐ[K] M} (hσ : σ ∉ F.fixingSubgroup) (b : c.Alg) :
    twistedAct F.fixingSubgroup c.x σ b = twistedAct F.fixingSubgroup c.x c.r b := by
  have hmem : c.r⁻¹ * σ ∈ F.fixingSubgroup :=
    (Subgroup.mul_mem_iff_of_index_two c.index_eq).mpr
      (iff_of_false (fun h => c.r_not_mem (by simpa using F.fixingSubgroup.inv_mem h)) hσ)
  have h := twistedAct_mul c.index_eq c.inner c.outer c.r (c.r⁻¹ * σ) b
  rw [mul_inv_cancel_left, c.twistedAct_alg_of_mem hmem] at h
  exact h

section Involution

variable [Normal K F]

/-- The twisted action of `r` is a unitary involution of the descended algebra. -/
theorem isUnitary : IsUnitaryInvolution (⇑(c.r.restrictNormal F))
    (outerInvolution F c.index_eq c.inner c.outer c.r) :=
  isUnitaryInvolution_outerInvolution F c.index_eq c.inner c.outer c.r_not_mem

/-- The involution fixes the scalars from `K`. -/
theorem outerInvolution_algebraMap (k : K) :
    outerInvolution F c.index_eq c.inner c.outer c.r (algebraMap K c.Alg k) =
      algebraMap K c.Alg k := by
  rw [IsScalarTower.algebraMap_apply K F c.Alg, c.isUnitary.2.2.2, AlgEquiv.commutes]

/-- The involution of the descended algebra induced by the outer automorphism `r`. -/
def involution : FirstKindInvolution K c.Alg where
  toLinearMap :=
    { toFun := outerInvolution F c.index_eq c.inner c.outer c.r
      map_add' := c.isUnitary.1
      map_smul' := fun k b => by
        rw [Algebra.smul_def, c.isUnitary.2.1, c.outerInvolution_algebraMap, RingHom.id_apply,
          ← Algebra.commutes, ← Algebra.smul_def] }
  map_one' := by
    have h := c.isUnitary.2.2.2 1
    rwa [map_one, map_one] at h
  map_mul' := c.isUnitary.2.1
  involutive' := c.isUnitary.2.2.1

/-- The involution is `b ↦ x(r) r(b)ᵀ x(r)⁻¹`. -/
theorem involution_val (b : c.Alg) :
    (c.involution b : Matrix m m M) =
      (c.x c.r : Matrix m m M) * ((b : Matrix m m M).map c.r)ᵀ *
        ((c.x c.r)⁻¹ : GL m M) :=
  twistedAct_of_not_mem c.r_not_mem _

/-- The automorphism `r` restricts to a nontrivial automorphism of `F`. -/
theorem restrictNormal_ne_one : c.r.restrictNormal F ≠ 1 := by
  intro h1
  apply c.r_not_mem
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have h2 := AlgEquiv.restrictNormal_commutes c.r F ⟨y, hy⟩
  rw [h1] at h2
  simpa using h2.symm

variable [Algebra.IsQuadraticExtension K F] [Algebra.IsSeparable K F]

/-- The restriction of `r` to `F` is the conjugation of `F/K`. -/
theorem restrictNormal_eq : c.r.restrictNormal F = SU3Root.conjugation K F :=
  SU3Root.conjugation_unique K F _ c.restrictNormal_ne_one

/-- The automorphism `r` acts on `F` by the conjugation of `F/K`. -/
theorem r_algebraMap (l : F) :
    c.r (algebraMap F M l) = algebraMap F M (SU3Root.conjugation K F l) := by
  rw [← c.restrictNormal_eq, AlgEquiv.restrictNormal_commutes]

/-- The involution is of the second kind: it acts on the centre `F` by the conjugation. -/
theorem involution_algebraMap (l : F) :
    c.involution (algebraMap F c.Alg l) = algebraMap F c.Alg (SU3Root.conjugation K F l) := by
  rw [← c.restrictNormal_eq]
  exact c.isUnitary.2.2.2 l

end Involution

section Chart

variable {S : Type u} [CommRing S] [Algebra K S]

/-- The entrywise image of the descended algebra under `ψ : M → S`. -/
def entryHom (ψ : M →ₐ[K] S) : c.Alg →ₐ[K] Matrix m m S :=
  ψ.mapMatrix.comp (c.Alg.val.restrictScalars K)

/-- The chart `S ⊗_K B → M_m(S)`, `s ⊗ b ↦ s • ψ(b)`, attached to `ψ : M → S`. -/
def chart (ψ : M →ₐ[K] S) : S ⊗[K] c.Alg →ₐ[S] Matrix m m S :=
  Algebra.TensorProduct.lift (Algebra.ofId S (Matrix m m S)) (c.entryHom ψ)
    (by intro s y; exact Algebra.commute_algebraMap_left s _)

/-- The chart on pure tensors. -/
theorem chart_tmul (ψ : M →ₐ[K] S) (s : S) (b : c.Alg) :
    c.chart ψ (s ⊗ₜ[K] b) = s • (b : Matrix m m M).map ψ := by
  rw [Algebra.smul_def]
  rfl

/-- The chart is natural in the coefficient algebra. -/
theorem chart_naturality {S' : Type u} [CommRing S'] [Algebra K S'] (ψ : M →ₐ[K] S)
    (g : S →ₐ[K] S') (y : S ⊗[K] c.Alg) :
    c.chart (g.comp ψ) (Algebra.TensorProduct.map g (AlgHom.id K c.Alg) y) =
      (c.chart ψ y).map g := by
  induction y using TensorProduct.inductionOn with
  | tmul s b =>
    rw [Algebra.TensorProduct.map_tmul, chart_tmul, chart_tmul]
    ext i j
    simp
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add, Matrix.map_add _ (map_add g)]

/-- The image of the matrix `x r` under `ψ`. -/
abbrev outerMatrix (ψ : M →ₐ[K] S) : GL m S :=
  GeneralLinearGroup.map (ψ : M →+* S) (c.x c.r)

/-- The entrywise image of an invertible matrix. -/
theorem coe_glMap {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (X : GL m R) :
    ((GeneralLinearGroup.map f X : GL m R') : Matrix m m R') = (X : Matrix m m R).map f := rfl

/-- A matrix identity: `ψ` applied to a conjugated transpose. -/
theorem map_conj_transpose (ψ : M →ₐ[K] S) (X : GL m M) (N : Matrix m m M) :
    ((X : Matrix m m M) * Nᵀ * ((X⁻¹ : GL m M) : Matrix m m M)).map ψ =
      (GeneralLinearGroup.map (ψ : M →+* S) X : Matrix m m S) * (N.map ψ)ᵀ *
        ((GeneralLinearGroup.map (ψ : M →+* S) X)⁻¹ : GL m S) := by
  rw [← map_inv, coe_glMap, coe_glMap, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rfl

/-- A matrix identity: `ψ` applied to a conjugation. -/
theorem map_conj (ψ : M →ₐ[K] S) (X : GL m M) (N : Matrix m m M) :
    (((X⁻¹ : GL m M) : Matrix m m M) * N * (X : Matrix m m M)).map ψ =
      (((GeneralLinearGroup.map (ψ : M →+* S) X)⁻¹ : GL m S) : Matrix m m S) * N.map ψ *
        (GeneralLinearGroup.map (ψ : M →+* S) X : Matrix m m S) := by
  rw [← map_inv, coe_glMap, coe_glMap, Matrix.map_mul, Matrix.map_mul]
  rfl

section Involution

variable [Normal K F]

/-- The chart turns the involution into the conjugated transpose of the chart along `ψ ∘ r`. -/
theorem chart_involution (ψ : M →ₐ[K] S) (y : S ⊗[K] c.Alg) :
    c.chart ψ (c.involution.baseChange S y) =
      (c.outerMatrix ψ : Matrix m m S) * (c.chart (ψ.comp c.r.toAlgHom) y)ᵀ *
        ((c.outerMatrix ψ)⁻¹ : GL m S) := by
  induction y using TensorProduct.inductionOn with
  | tmul s b =>
    rw [FirstKindInvolution.baseChange_tmul, chart_tmul, chart_tmul, c.involution_val,
      map_conj_transpose, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.map_map]
    rfl
  | add y y' hy hy' =>
    rw [FirstKindInvolution.map_add, map_add, map_add, hy, hy', Matrix.transpose_add,
      Matrix.mul_add, Matrix.add_mul]

omit [Normal K F] in
/-- `X X⁻¹ = 1` for the image `X` of `x r`. -/
theorem outerMatrix_mul_inv (ψ : M →ₐ[K] S) :
    (c.outerMatrix ψ : Matrix m m S) * ((c.outerMatrix ψ)⁻¹ : GL m S) = 1 := Units.mul_inv _

omit [Normal K F] in
/-- `X⁻¹ X = 1` for the image `X` of `x r`. -/
theorem outerMatrix_inv_mul (ψ : M →ₐ[K] S) :
    (((c.outerMatrix ψ)⁻¹ : GL m S) : Matrix m m S) * (c.outerMatrix ψ : Matrix m m S) = 1 :=
  Units.inv_mul _

/-- The chart along `ψ ∘ r` of the involution, by involutivity. -/
theorem chart_comp_involution (ψ : M →ₐ[K] S) (y : S ⊗[K] c.Alg) :
    c.chart (ψ.comp c.r.toAlgHom) (c.involution.baseChange S y) =
      ((((c.outerMatrix ψ)⁻¹ : GL m S) : Matrix m m S) * c.chart ψ y *
        (c.outerMatrix ψ : Matrix m m S))ᵀ := by
  have h := c.chart_involution ψ (c.involution.baseChange S y)
  rw [FirstKindInvolution.apply_apply] at h
  rw [h]
  simp only [← Matrix.mul_assoc, c.outerMatrix_inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, c.outerMatrix_inv_mul, Matrix.mul_one, Matrix.transpose_transpose]

end Involution

end Chart
section Translate

variable {S : Type u} [CommRing S] [Algebra K S]

/-- The image of the matrix `x σ` under `ψ`. -/
abbrev cocycleMatrix (ψ : M →ₐ[K] S) (σ : M ≃ₐ[K] M) : GL m S :=
  GeneralLinearGroup.map (ψ : M →+* S) (c.x σ)

omit [DecidableEq m] in
/-- Undoing a conjugation by an invertible matrix. -/
theorem eq_conj_of_conj_eq {R : Type*} [CommRing R] [DecidableEq m] (X : GL m R)
    {A B : Matrix m m R} (h : (X : Matrix m m R) * A * ((X⁻¹ : GL m R) : Matrix m m R) = B) :
    A = ((X⁻¹ : GL m R) : Matrix m m R) * B * (X : Matrix m m R) := by
  rw [← h]
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

omit [Fintype m] [DecidableEq m] in
/-- Mapping along `ψ ∘ σ` is mapping along `σ`, then along `ψ`. -/
theorem map_comp_eq (ψ : M →ₐ[K] S) (σ : M ≃ₐ[K] M) (N : Matrix m m M) :
    N.map (ψ.comp σ.toAlgHom) = (N.map σ).map ψ := by
  rw [Matrix.map_map]
  rfl

/-- An automorphism fixing `F` acts on the descended algebra by conjugation by `x σ`. -/
theorem map_of_mem {σ : M ≃ₐ[K] M} (hσ : σ ∈ F.fixingSubgroup) (b : c.Alg) :
    (b : Matrix m m M).map σ =
      ((c.x σ)⁻¹ : GL m M) * (b : Matrix m m M) * (c.x σ : Matrix m m M) := by
  have h := c.twistedAct_alg_of_mem hσ b
  rw [UnitaryTwistedDescent.twistedAct_of_mem hσ] at h
  exact eq_conj_of_conj_eq _ h

/-- The chart along a translate by an automorphism fixing `F`. -/
theorem chart_comp_of_mem (ψ : M →ₐ[K] S) {σ : M ≃ₐ[K] M} (hσ : σ ∈ F.fixingSubgroup)
    (y : S ⊗[K] c.Alg) :
    c.chart (ψ.comp σ.toAlgHom) y =
      (((c.cocycleMatrix ψ σ)⁻¹ : GL m S) : Matrix m m S) * c.chart ψ y *
        (c.cocycleMatrix ψ σ : Matrix m m S) := by
  induction y using TensorProduct.inductionOn with
  | tmul s b =>
    rw [chart_tmul, chart_tmul, map_comp_eq, c.map_of_mem hσ, map_conj, Matrix.mul_smul,
      Matrix.smul_mul]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', Matrix.mul_add, Matrix.add_mul]

section Involution

variable [Normal K F]

/-- An automorphism moving `F` acts on the descended algebra through the involution. -/
theorem map_of_not_mem {σ : M ≃ₐ[K] M} (hσ : σ ∉ F.fixingSubgroup) (b : c.Alg) :
    (b : Matrix m m M).map σ =
      ((((c.x σ)⁻¹ : GL m M) : Matrix m m M) * (c.involution b : Matrix m m M) *
        (c.x σ : Matrix m m M))ᵀ := by
  have h := c.twistedAct_of_not_mem_eq hσ b
  rw [twistedAct_of_not_mem hσ] at h
  change _ = (c.involution b : Matrix m m M) at h
  rw [← eq_conj_of_conj_eq _ h, Matrix.transpose_transpose]

/-- The chart along a translate by an automorphism moving `F`. -/
theorem chart_comp_of_not_mem (ψ : M →ₐ[K] S) {σ : M ≃ₐ[K] M} (hσ : σ ∉ F.fixingSubgroup)
    (y : S ⊗[K] c.Alg) :
    c.chart (ψ.comp σ.toAlgHom) y =
      ((((c.cocycleMatrix ψ σ)⁻¹ : GL m S) : Matrix m m S) *
        c.chart ψ (c.involution.baseChange S y) * (c.cocycleMatrix ψ σ : Matrix m m S))ᵀ := by
  induction y using TensorProduct.inductionOn with
  | tmul s b =>
    rw [chart_tmul, FirstKindInvolution.baseChange_tmul, chart_tmul, map_comp_eq,
      c.map_of_not_mem hσ, Matrix.transpose_map, map_conj, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.transpose_smul]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.transpose_add]

end Involution

end Translate

section Descent

variable [FiniteDimensional K M] [IsGalois K M]

instance : FiniteDimensional F c.Alg := c.action.finiteDimensional_fixed

instance [Nonempty m] : Algebra.IsCentral F c.Alg := c.action.isCentral_fixed

instance [Nonempty m] : IsSimpleRing c.Alg := c.action.isSimpleRing_fixed

instance : FiniteDimensional K c.Alg := Module.Finite.trans F c.Alg

/-- The descended algebra has dimension `m²` over `F`. -/
theorem finrank_alg : Module.finrank F c.Alg = Fintype.card m * Fintype.card m := by
  have h1 := c.action.descentEquiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_matrix, Module.finrank_self, mul_one] at h1
  exact h1

variable {S : Type u} [CommRing S] [Algebra K S]

omit [FiniteDimensional K M] [IsGalois K M] in
/-- Mapping a scalar matrix entrywise. -/
theorem map_algebraMap_matrix (ψ : M →ₐ[K] S) (l : M) :
    (algebraMap M (Matrix m m M) l).map ψ = algebraMap S (Matrix m m S) (ψ l) := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_map (map_zero ψ)]
  rfl

/-- Every image of the descent isomorphism, mapped along `ψ`, is a value of the chart. -/
theorem exists_chart_eq (ψ : M →ₐ[K] S) (z : M ⊗[F] c.Alg) :
    ∃ y, c.chart ψ y = (c.action.descentEquiv z).map ψ := by
  induction z using TensorProduct.inductionOn with
  | tmul l b =>
    refine ⟨ψ l ⊗ₜ[K] b, ?_⟩
    rw [chart_tmul, Langlands.CentralSimple.SemilinearGaloisAction.descentEquiv_tmul,
      Matrix.map_mul, map_algebraMap_matrix, Algebra.smul_def]
  | add z z' hz hz' =>
    obtain ⟨y, hy⟩ := hz
    obtain ⟨y', hy'⟩ := hz'
    exact ⟨y + y', by rw [map_add, map_add, hy, hy', Matrix.map_add _ (map_add ψ)]⟩

/-- The chart is surjective. -/
theorem chart_surjective (ψ : M →ₐ[K] S) : Function.Surjective (c.chart ψ) := by
  intro N
  have hsingle : ∀ i j, ∃ y, c.chart ψ y = single i j (1 : S) := by
    intro i j
    obtain ⟨z, hz⟩ := c.action.descentEquiv.surjective (single i j 1)
    obtain ⟨y, hy⟩ := c.exists_chart_eq ψ z
    exact ⟨y, by rw [hy, hz, Matrix.map_single, map_one]⟩
  choose y hy using hsingle
  refine ⟨∑ i, ∑ j, N i j • y i j, ?_⟩
  simp only [map_sum, map_smul, hy, Matrix.smul_single, smul_eq_mul, mul_one]
  exact (Matrix.matrix_eq_sum_single N).symm

/-- The restriction of `ψ : M → S` to `F`. -/
abbrev fieldPoint (ψ : M →ₐ[K] S) : F →ₐ[K] S := ψ.comp (IsScalarTower.toAlgHom K F M)

/-- The scalars `F ⊗_K S → S ⊗_K B`. -/
def scalarMap : F ⊗[K] S →ₐ[K] S ⊗[K] c.Alg :=
  (Algebra.TensorProduct.map (AlgHom.id K S) (IsScalarTower.toAlgHom K F c.Alg)).comp
    (Algebra.TensorProduct.comm K F S).toAlgHom

section Quadratic

variable [Algebra.IsQuadraticExtension K F] [Algebra.IsSeparable K F]

omit [FiniteDimensional K M] [IsGalois K M] [Algebra.IsQuadraticExtension K F]
  [Algebra.IsSeparable K F] in
/-- On scalars the chart is the projection `ℓ ⊗ s ↦ ψ(ℓ) s`. -/
theorem chart_scalarMap (ψ : M →ₐ[K] S) (z : F ⊗[K] S) :
    c.chart ψ (c.scalarMap z) =
      algebraMap S (Matrix m m S) (HermitianMatrix.tensorProj K F (fieldPoint ψ) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul l s =>
    have h1 : c.scalarMap (l ⊗ₜ[K] s) = s ⊗ₜ[K] algebraMap F c.Alg l := rfl
    rw [h1, chart_tmul, HermitianMatrix.tensorProj_tmul, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply F M (Matrix m m M), map_algebraMap_matrix,
      Algebra.smul_def, ← map_mul, mul_comm]
    rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

variable [Normal K F]

omit [FiniteDimensional K M] [IsGalois K M] in
/-- Translating `ψ` by `r` composes its restriction to `F` with the conjugation. -/
theorem fieldPoint_comp_r (ψ : M →ₐ[K] S) :
    fieldPoint (F := F) (ψ.comp c.r.toAlgHom) =
      (fieldPoint ψ).comp (SU3Root.conjugation K F).toAlgHom := by
  ext l
  change ψ (c.r (algebraMap F M l)) = ψ (algebraMap F M (SU3Root.conjugation K F l))
  rw [c.r_algebraMap]

omit [FiniteDimensional K M] [IsGalois K M] in
/-- Every pair of scalar matrices is the pair of charts along `ψ` and `ψ ∘ r` of a scalar
of `S ⊗_K F`. -/
theorem exists_scalar (ψ : M →ₐ[K] S) (a b : S) :
    ∃ e : S ⊗[K] c.Alg, c.chart ψ e = algebraMap S (Matrix m m S) a ∧
      c.chart (ψ.comp c.r.toAlgHom) e = algebraMap S (Matrix m m S) b := by
  obtain ⟨z, hz1, hz2⟩ := HermitianMatrix.tensorProj_surjective₂ K F (fieldPoint ψ) a b
  refine ⟨c.scalarMap z, ?_, ?_⟩
  · rw [chart_scalarMap, hz1]
  · rw [chart_scalarMap, fieldPoint_comp_r, hz2]

/-- The charts along `ψ` and `ψ ∘ r` are jointly surjective. -/
theorem chart_pair_surjective (ψ : M →ₐ[K] S) (g h : Matrix m m S) :
    ∃ y, c.chart ψ y = g ∧ c.chart (ψ.comp c.r.toAlgHom) y = h := by
  obtain ⟨e₁, he₁, he₁'⟩ := c.exists_scalar ψ 1 0
  obtain ⟨e₂, he₂, he₂'⟩ := c.exists_scalar ψ 0 1
  obtain ⟨y₁, hy₁⟩ := c.chart_surjective ψ g
  obtain ⟨y₂, hy₂⟩ := c.chart_surjective (ψ.comp c.r.toAlgHom) h
  refine ⟨e₁ * y₁ + e₂ * y₂, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, he₁, he₂, hy₁, map_one, map_zero, one_mul, zero_mul,
      add_zero]
  · rw [map_add, map_mul, map_mul, he₁', he₂', hy₂, map_one, map_zero, one_mul, zero_mul,
      zero_add]

omit [Algebra.IsSeparable K F] [Normal K F] in
/-- The descended algebra has dimension `2 m²` over `K`. -/
theorem finrank_alg_base :
    Module.finrank K c.Alg = 2 * (Fintype.card m * Fintype.card m) := by
  rw [← Module.finrank_mul_finrank K F c.Alg, Algebra.IsQuadraticExtension.finrank_eq_two,
    c.finrank_alg]

/-- The charts along `ψ` and `ψ ∘ r` are jointly injective. -/
theorem chart_pair_injective (ψ : M →ₐ[K] S) {y y' : S ⊗[K] c.Alg}
    (h1 : c.chart ψ y = c.chart ψ y')
    (h2 : c.chart (ψ.comp c.r.toAlgHom) y = c.chart (ψ.comp c.r.toAlgHom) y') : y = y' := by
  have : FiniteDimensional K c.Alg := Module.Finite.trans F c.Alg
  have : Module.Free K c.Alg := Module.Free.of_divisionRing K c.Alg
  let Θ : S ⊗[K] c.Alg →ₗ[S] Matrix m m S × Matrix m m S :=
    (c.chart ψ).toLinearMap.prod (c.chart (ψ.comp c.r.toAlgHom)).toLinearMap
  have hsurj : Function.Surjective Θ := by
    rintro ⟨g, h⟩
    obtain ⟨y, hy1, hy2⟩ := c.chart_pair_surjective ψ g h
    exact ⟨y, Prod.ext hy1 hy2⟩
  let b₁ := Algebra.TensorProduct.basis S (Module.finBasis K c.Alg)
  let b₂ := (Matrix.stdBasis S m m).prod (Matrix.stdBasis S m m)
  have hcard : Fintype.card (Fin (Module.finrank K c.Alg)) =
      Fintype.card ((m × m) ⊕ (m × m)) := by
    rw [Fintype.card_fin, c.finrank_alg_base, Fintype.card_sum, Fintype.card_prod]
    ring
  have hinj := OrzechProperty.injective_of_surjective_of_injective
    (b₁.equiv b₂ (Fintype.equivOfCardEq hcard)).toLinearMap Θ
    (b₁.equiv b₂ (Fintype.equivOfCardEq hcard)).injective hsurj
  exact hinj (Prod.ext h1 h2)

omit [DecidableEq m] in
/-- Products of conjugates by the same invertible matrix. -/
theorem conj_mul_conj {R : Type*} [CommRing R] [DecidableEq m] (X : GL m R)
    (A B : Matrix m m R) :
    (((X⁻¹ : GL m R) : Matrix m m R) * A * (X : Matrix m m R)) *
        (((X⁻¹ : GL m R) : Matrix m m R) * B * (X : Matrix m m R)) =
      ((X⁻¹ : GL m R) : Matrix m m R) * (A * B) * (X : Matrix m m R) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (X : Matrix m m R) ((X⁻¹ : GL m R) : Matrix m m R), Units.mul_inv,
    Matrix.one_mul]

omit [DecidableEq m] in
/-- Transposed conjugates of mutually inverse matrices multiply to `1`. -/
theorem transpose_conj_mul {R : Type*} [CommRing R] [DecidableEq m] (X : GL m R)
    {A B : Matrix m m R} (h : A * B = 1) :
    (((X⁻¹ : GL m R) : Matrix m m R) * B * (X : Matrix m m R))ᵀ *
        (((X⁻¹ : GL m R) : Matrix m m R) * A * (X : Matrix m m R))ᵀ = 1 := by
  rw [← Matrix.transpose_mul, conj_mul_conj, h, Matrix.mul_one, Units.inv_mul,
    Matrix.transpose_one]

/-- A unitary element of chart `1` along `ψ` is `1`. -/
theorem eq_one_of_chart_eq_one (ψ : M →ₐ[K] S) {y : S ⊗[K] c.Alg}
    (hy : y * c.involution.baseChange S y = 1) (h1 : c.chart ψ y = 1) : y = 1 := by
  have hτ : c.chart ψ (c.involution.baseChange S y) = 1 := by
    have h := congrArg (c.chart ψ) hy
    rwa [map_mul, h1, Matrix.one_mul, map_one] at h
  rw [c.chart_involution] at hτ
  have h2 : c.chart (ψ.comp c.r.toAlgHom) y = 1 := by
    have h := eq_conj_of_conj_eq _ hτ
    rw [Matrix.mul_one, c.outerMatrix_inv_mul] at h
    rw [← Matrix.transpose_transpose (c.chart _ y), h, Matrix.transpose_one]
  exact c.chart_pair_injective ψ (h1.trans (map_one _).symm) (h2.trans (map_one _).symm)

variable [Nonempty m]

omit [Algebra.IsQuadraticExtension K F] [Algebra.IsSeparable K F] [Normal K F] in
set_option synthInstance.maxHeartbeats 200000 in
/-- The projection of the relative reduced norm along `ψ` is the determinant of the chart. -/
theorem tensorProj_relativeNorm (ψ : M →ₐ[K] S) (u : (S ⊗[K] c.Alg)ˣ) :
    HermitianMatrix.tensorProj K F (fieldPoint ψ)
        (relativeNorm K F c.Alg S u : F ⊗[K] S) =
      (c.chart ψ (u : S ⊗[K] c.Alg)).det := by
  let _ : Algebra F S := ((ψ : M →+* S).comp (algebraMap F M)).toAlgebra
  have : IsScalarTower K F S := IsScalarTower.of_algebraMap_eq (fun k => by
    change algebraMap K S k = ψ (algebraMap F M (algebraMap K F k))
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes])
  let π : F ⊗[K] S →ₐ[F] S :=
    Algebra.TensorProduct.lift (Algebra.ofId F S) (AlgHom.id K S)
      (by intro _ _; exact Commute.all _ _)
  have hπ : ∀ z, HermitianMatrix.tensorProj K F (fieldPoint ψ) z = π z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul l s =>
      rw [HermitianMatrix.tensorProj_tmul]
      rfl
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  have hchart : ∀ y : S ⊗[K] c.Alg,
      SpecialLinearInnerForm.chartAlong c.action.descentEquiv (ψ : M →+* S) rfl
        (Algebra.TensorProduct.map π (AlgHom.id F c.Alg) (tensorEquiv K F c.Alg S y)) =
        c.chart ψ y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul s b =>
      rw [tensorEquiv_tmul, Algebra.TensorProduct.map_tmul,
        SpecialLinearInnerForm.chartAlong_tmul,
        Langlands.CentralSimple.SemilinearGaloisAction.descentEquiv_one_tmul, chart_tmul]
      congr 1
      change algebraMap F S 1 * s = s
      rw [map_one, one_mul]
    | add y y' hy hy' =>
      have e : tensorEquiv K F c.Alg S (y + y') =
          tensorEquiv K F c.Alg S y + tensorEquiv K F c.Alg S y' :=
        (tensorEquiv K F c.Alg S).toLinearEquiv.map_add y y'
      rw [e, map_add, map_add, hy, hy', map_add]
  have key := Langlands.CentralSimple.reducedNorm_naturality (↥F) (↥c.Alg) π
    (tensorEquiv K F c.Alg S (u : S ⊗[K] c.Alg))
  rw [hπ, relativeNorm_val, ← key,
    SpecialLinearInnerForm.reducedNorm_eq_det_chartAlong c.action.descentEquiv
      (ψ : M →+* S) rfl, hchart]

/-- The chart of a special unitary point along `ψ`, as a determinant-one matrix. -/
def suChartHom (ψ : M →ₐ[K] S) :
    specialUnitaryPoints F c.involution S →* SpecialLinearGroup m S where
  toFun u := ⟨c.chart ψ ((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg), by
    rw [← c.tensorProj_relativeNorm, ((mem_specialUnitaryPoints _ _).mp u.2).2, Units.val_one,
      map_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp; rfl)

omit [Algebra.IsQuadraticExtension K F] [Algebra.IsSeparable K F] in
/-- The underlying matrix of the chart of a special unitary point. -/
theorem suChartHom_val (ψ : M →ₐ[K] S) (u : specialUnitaryPoints F c.involution S) :
    ((c.suChartHom ψ u : SpecialLinearGroup m S) : Matrix m m S) =
      c.chart ψ ((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg) := rfl

/-- The chart of special unitary points is injective. -/
theorem suChartHom_injective (ψ : M →ₐ[K] S) : Function.Injective (c.suChartHom ψ) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 : c.chart ψ ((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg) = 1 :=
    congrArg Subtype.val hu
  apply Subtype.ext
  apply Units.ext
  exact c.eq_one_of_chart_eq_one ψ ((mem_specialUnitaryPoints _ _).mp u.2).1 h1

/-- The chart of special unitary points is surjective onto `SL_m(S)`. -/
theorem suChartHom_surjective (ψ : M →ₐ[K] S) : Function.Surjective (c.suChartHom ψ) := by
  intro g
  set X := c.outerMatrix ψ with hX
  let ψr := ψ.comp c.r.toAlgHom
  set gm : Matrix m m S := (g : Matrix m m S) with hgm
  set gi : Matrix m m S := ((g⁻¹ : SpecialLinearGroup m S) : Matrix m m S) with hgi
  have hggi : gm * gi = 1 := by
    rw [hgm, hgi, ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  have hgig : gi * gm = 1 := by
    rw [hgm, hgi, ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  obtain ⟨y, hy1, hy2⟩ := c.chart_pair_surjective ψ gm
    (((X⁻¹ : GL m S) : Matrix m m S) * gi * (X : Matrix m m S))ᵀ
  obtain ⟨y', hy1', hy2'⟩ := c.chart_pair_surjective ψ gi
    (((X⁻¹ : GL m S) : Matrix m m S) * gm * (X : Matrix m m S))ᵀ
  have hyy' : y * y' = 1 := by
    apply c.chart_pair_injective ψ
    · rw [map_mul, hy1, hy1', hggi, map_one]
    · rw [map_mul, hy2, hy2', transpose_conj_mul X hggi, map_one]
  have hy'y : y' * y = 1 := by
    apply c.chart_pair_injective ψ
    · rw [map_mul, hy1, hy1', hgig, map_one]
    · rw [map_mul, hy2, hy2', transpose_conj_mul X hgig, map_one]
  let w : (S ⊗[K] c.Alg)ˣ := ⟨y, y', hyy', hy'y⟩
  have hunit : y * c.involution.baseChange S y = 1 := by
    apply c.chart_pair_injective ψ
    · rw [map_mul, c.chart_involution, hy1, map_one, ← hX, hy2, Matrix.transpose_transpose]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc gm, Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc,
        Units.mul_inv, Matrix.mul_one, hggi]
    · rw [map_mul, c.chart_comp_involution, hy1, hy2, ← hX, transpose_conj_mul X hggi,
        map_one]
  have hnorm : relativeNorm K F c.Alg S w = 1 := by
    apply Units.ext
    apply HermitianMatrix.tensorProj_injective₂ K F (fieldPoint ψ)
    · rw [c.tensorProj_relativeNorm, Units.val_one, map_one]
      change (c.chart ψ y).det = 1
      rw [hy1, hgm]
      exact g.2
    · rw [← c.fieldPoint_comp_r, c.tensorProj_relativeNorm, Units.val_one, map_one]
      change (c.chart (ψ.comp c.r.toAlgHom) y).det = 1
      rw [hy2, Matrix.det_transpose, Matrix.det_units_conj', hgi]
      exact (g⁻¹).2
  refine ⟨⟨w, (mem_specialUnitaryPoints _ _).mpr ⟨hunit, hnorm⟩⟩, ?_⟩
  apply Subtype.ext
  exact hy1

/-- The chart of special unitary points along `ψ`, a group isomorphism onto `SL_m(S)`. -/
def suChart (ψ : M →ₐ[K] S) :
    specialUnitaryPoints F c.involution S ≃* SpecialLinearGroup m S :=
  MulEquiv.ofBijective (c.suChartHom ψ) ⟨c.suChartHom_injective ψ, c.suChartHom_surjective ψ⟩

/-- The underlying matrix of the chart of a special unitary point. -/
theorem suChart_val (ψ : M →ₐ[K] S) (u : specialUnitaryPoints F c.involution S) :
    ((c.suChart ψ u : SpecialLinearGroup m S) : Matrix m m S) =
      c.chart ψ ((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg) := rfl

/-- The chart of special unitary points is natural in the coefficient algebra. -/
theorem suChart_naturality {S' : Type u} [CommRing S'] [Algebra K S'] (ψ : M →ₐ[K] S)
    (g : S →ₐ[K] S') (u : specialUnitaryPoints F c.involution S) :
    ((c.suChart (g.comp ψ) (specialUnitaryMap F c.involution g u) :
        SpecialLinearGroup m S') : Matrix m m S') =
      ((c.suChart ψ u : SpecialLinearGroup m S) : Matrix m m S).map g := by
  rw [suChart_val, suChart_val, specialUnitaryMap_val, chart_naturality]

/-- Translating `ψ` by an automorphism fixing `F` conjugates the chart. -/
theorem suChart_comp_of_mem (ψ : M →ₐ[K] S) {σ : M ≃ₐ[K] M} (hσ : σ ∈ F.fixingSubgroup)
    (u : specialUnitaryPoints F c.involution S) :
    ((c.suChart (ψ.comp σ.toAlgHom) u : SpecialLinearGroup m S) : Matrix m m S) =
      (((c.cocycleMatrix ψ σ)⁻¹ : GL m S) : Matrix m m S) *
        ((c.suChart ψ u : SpecialLinearGroup m S) : Matrix m m S) *
        (c.cocycleMatrix ψ σ : Matrix m m S) := by
  rw [suChart_val, suChart_val, c.chart_comp_of_mem ψ hσ]

omit [Algebra.IsQuadraticExtension K F] [Algebra.IsSeparable K F] in
/-- The involution of a unitary unit is its inverse. -/
theorem involution_eq_inv (u : specialUnitaryPoints F c.involution S) :
    c.involution.baseChange S ((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg) =
      (((u : (S ⊗[K] c.Alg)ˣ)⁻¹ : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg) := by
  have h := ((mem_specialUnitaryPoints _ _).mp u.2).1
  calc c.involution.baseChange S ((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg)
      = (((u : (S ⊗[K] c.Alg)ˣ)⁻¹ : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg) *
          (((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg) *
            c.involution.baseChange S ((u : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]

/-- Translating `ψ` by an automorphism moving `F` gives the conjugated inverse transpose. -/
theorem suChart_comp_of_not_mem (ψ : M →ₐ[K] S) {σ : M ≃ₐ[K] M}
    (hσ : σ ∉ F.fixingSubgroup) (u : specialUnitaryPoints F c.involution S) :
    ((c.suChart (ψ.comp σ.toAlgHom) u : SpecialLinearGroup m S) : Matrix m m S) =
      ((((c.cocycleMatrix ψ σ)⁻¹ : GL m S) : Matrix m m S) *
        (((c.suChart ψ u)⁻¹ : SpecialLinearGroup m S) : Matrix m m S) *
        (c.cocycleMatrix ψ σ : Matrix m m S))ᵀ := by
  have h : c.chart ψ ((((u : (S ⊗[K] c.Alg)ˣ)⁻¹ : (S ⊗[K] c.Alg)ˣ) : S ⊗[K] c.Alg)) =
      (((c.suChart ψ u)⁻¹ : SpecialLinearGroup m S) : Matrix m m S) := by
    rw [← map_inv, suChart_val]
    rfl
  rw [suChart_val, c.chart_comp_of_not_mem ψ hσ, c.involution_eq_inv, h]

end Quadratic

end Descent

end Cocycle

end Langlands.LinearAlgebra.UnitaryTwistedChart
