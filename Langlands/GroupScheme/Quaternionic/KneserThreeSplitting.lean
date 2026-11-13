import Langlands.GroupScheme.Quaternionic.KneserThreeField
import Langlands.GroupScheme.Quaternionic.KneserThreePresentation
import Langlands.GroupScheme.Examples.SU3RootParametersUnitaryComparison

/-!
# A quaternion-type algebra split as `L ⊕ jL`, and its base change as a `Presentation`

`QuatData K D` records elements `x, j` of a `K`-algebra `D` with `x² = c`, `j² = δ`,
`jx = -xj`, and a basis `1, x, j, jx` of `D`, where `X² - c` is irreducible and
`L = K[X]/(X² - c)` is separable over `K`. Let `ι : L → D` send the root to `x`. Every element of
`D` is uniquely `ι a + j ι a'`, and `j ι a = ι ā j`, where `ā` is the Library's conjugation of
`L`. For every commutative `K`-algebra `R`, base change gives a
`Presentation (L ⊗[K] R) (R ⊗[K] D)` for the Library's tensor conjugation of `L ⊗[K] R`, and
these presentations are compatible with every `K`-algebra map `R → R'`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree

open QuadField

/-- Data splitting `D` as `L ⊕ jL` with `L = K[X]/(X² - c)`. -/
structure QuatData (K D : Type u) [Field K] [Ring D] [Algebra K D] where
  c : K
  δ : K
  x : D
  j : D
  x_mul_x : x * x = algebraMap K D c
  j_mul_j : j * j = algebraMap K D δ
  j_mul_x : j * x = -(x * j)
  basis : Module.Basis (Fin 4) K D
  basis_eq : ⇑basis = ![1, x, j, j * x]
  irreducible : Irreducible (poly c)
  separable : Algebra.IsSeparable K (field c)

namespace QuatData

variable {K D : Type u} [Field K] [Ring D] [Algebra K D] (Q : QuatData K D)

instance : Fact (Irreducible (poly Q.c)) := ⟨Q.irreducible⟩

instance : Algebra.IsSeparable K (field Q.c) := Q.separable

/-- The embedding `L → D`, `root ↦ x`. -/
abbrev ι : field Q.c →ₐ[K] D := embed Q.x Q.x_mul_x

theorem ι_root : Q.ι root = Q.x := embed_root _ _

theorem ι_linear (a₀ a₁ : K) :
    Q.ι (a₀ • (1 : field Q.c) + a₁ • root) = a₀ • (1 : D) + a₁ • Q.x := by
  rw [map_add, map_smul, map_smul, map_one, ι_root]

/-- The first coordinate `a`. -/
def fst : D →ₗ[K] field Q.c :=
  (LinearMap.smulRight (Q.basis.coord 0) (1 : field Q.c)) +
    LinearMap.smulRight (Q.basis.coord 1) root

/-- The second coordinate `a'`. -/
def snd : D →ₗ[K] field Q.c :=
  (LinearMap.smulRight (Q.basis.coord 2) (1 : field Q.c)) +
    LinearMap.smulRight (Q.basis.coord 3) root

theorem decompose (d : D) : Q.ι (Q.fst d) + Q.j * Q.ι (Q.snd d) = d := by
  have h := Q.basis.sum_repr d
  rw [Fin.sum_univ_four, Q.basis_eq] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h
  simp only [fst, snd, LinearMap.add_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    map_add, map_smul, map_one, ι_root]
  conv_rhs => rw [← h]
  simp only [mul_add, mul_smul_comm, mul_one]
  abel

theorem repr_linear (a₀ a₁ a₂ a₃ : K) :
    Q.basis.repr (a₀ • (1 : D) + a₁ • Q.x + Q.j * (a₂ • (1 : D) + a₃ • Q.x)) =
      Finsupp.equivFunOnFinite.symm ![a₀, a₁, a₂, a₃] := by
  have h := Q.basis.repr_sum_self ![a₀, a₁, a₂, a₃]
  rw [Fin.sum_univ_four, Q.basis_eq] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h
  have e : a₀ • (1 : D) + a₁ • Q.x + Q.j * (a₂ • (1 : D) + a₃ • Q.x) =
      a₀ • (1 : D) + a₁ • Q.x + a₂ • Q.j + a₃ • (Q.j * Q.x) := by
    simp only [mul_add, mul_smul_comm, mul_one]
    abel
  rw [e]
  apply Finsupp.ext
  intro i
  rw [Finsupp.equivFunOnFinite_symm_apply_apply, ← h]
  rfl

theorem fst_mk (a a' : field Q.c) : Q.fst (Q.ι a + Q.j * Q.ι a') = a := by
  obtain ⟨a₀, a₁, rfl⟩ := QuadField.exists_eq a
  obtain ⟨a₂, a₃, rfl⟩ := QuadField.exists_eq a'
  rw [ι_linear, ι_linear]
  simp [fst, Module.Basis.coord_apply, repr_linear]

theorem snd_mk (a a' : field Q.c) : Q.snd (Q.ι a + Q.j * Q.ι a') = a' := by
  obtain ⟨a₀, a₁, rfl⟩ := QuadField.exists_eq a
  obtain ⟨a₂, a₃, rfl⟩ := QuadField.exists_eq a'
  rw [ι_linear, ι_linear]
  simp [snd, Module.Basis.coord_apply, repr_linear]

theorem fst_ι (a : field Q.c) : Q.fst (Q.ι a) = a := by
  simpa using Q.fst_mk a 0

theorem snd_ι (a : field Q.c) : Q.snd (Q.ι a) = 0 := by
  simpa using Q.snd_mk a 0

theorem fst_j_mul (a : field Q.c) : Q.fst (Q.j * Q.ι a) = 0 := by
  simpa using Q.fst_mk 0 a

theorem snd_j_mul (a : field Q.c) : Q.snd (Q.j * Q.ι a) = a := by
  simpa using Q.snd_mk 0 a

/-- `j ι a = ι ā j`. -/
theorem j_mul_ι (a : field Q.c) :
    Q.j * Q.ι a = Q.ι (SU3Root.conjugation K (field Q.c) a) * Q.j := by
  obtain ⟨a₀, a₁, rfl⟩ := QuadField.exists_eq a
  have hc : SU3Root.conjugation K (field Q.c) (a₀ • (1 : field Q.c) + a₁ • root) =
      a₀ • (1 : field Q.c) + (-a₁) • root := by
    rw [map_add, map_smul, map_smul, map_one, conjugation_root, smul_neg, neg_smul]
  rw [hc, ι_linear, ι_linear]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, Q.j_mul_x,
    neg_smul, smul_neg, neg_mul]

section BaseChange

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The Library's tensor conjugation of `L ⊗[K] R`. -/
abbrev tensorInvolution : SU3Root.RingInvolution (field Q.c ⊗[K] R) :=
  SU3Root.unitaryTensorInvolution K (field Q.c) R

theorem tensorInvolution_tmul (a : field Q.c) (r : R) :
    (Q.tensorInvolution R).bar (a ⊗ₜ[K] r) = SU3Root.conjugation K (field Q.c) a ⊗ₜ[K] r := rfl

/-- The base-changed embedding `L ⊗[K] R → R ⊗[K] D`, `a ⊗ r ↦ r ⊗ ι a`. -/
def ιR : field Q.c ⊗[K] R →ₐ[K] R ⊗[K] D :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight.comp Q.ι)
    Algebra.TensorProduct.includeLeft (fun a r => by
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply]
      change _ * _ = _ * _
      simp [Algebra.TensorProduct.tmul_mul_tmul])

@[simp] theorem ιR_tmul (a : field Q.c) (r : R) : Q.ιR R (a ⊗ₜ[K] r) = r ⊗ₜ[K] Q.ι a := by
  simp [ιR, Algebra.TensorProduct.tmul_mul_tmul]

/-- The base-changed element `1 ⊗ j`. -/
def jR : R ⊗[K] D := (1 : R) ⊗ₜ[K] Q.j

/-- The base-changed scalar `δ`. -/
def δR : field Q.c ⊗[K] R := algebraMap K (field Q.c ⊗[K] R) Q.δ

theorem bar_δR : (Q.tensorInvolution R).bar (Q.δR R) = Q.δR R := by
  change (Q.tensorInvolution R).bar (algebraMap K (field Q.c) Q.δ ⊗ₜ[K] (1 : R)) =
    algebraMap K (field Q.c) Q.δ ⊗ₜ[K] (1 : R)
  rw [tensorInvolution_tmul, AlgEquiv.commutes]

theorem jR_mul (a : field Q.c ⊗[K] R) :
    Q.jR R * Q.ιR R a = Q.ιR R ((Q.tensorInvolution R).bar a) * Q.jR R := by
  induction a using TensorProduct.inductionOn with
  | tmul a r =>
    rw [tensorInvolution_tmul, ιR_tmul, ιR_tmul, jR, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, j_mul_ι, one_mul, mul_one]
  | add a b ha hb => simp only [map_add, mul_add, add_mul, ha, hb]

theorem jR_mul_self : Q.jR R * Q.jR R = Q.ιR R (Q.δR R) := by
  rw [jR, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Q.j_mul_j, δR, AlgHom.commutes]
  exact (Algebra.TensorProduct.includeRight.commutes Q.δ)

/-- The first base-changed coordinate. -/
def fstR : R ⊗[K] D →ₗ[K] field Q.c ⊗[K] R :=
  (TensorProduct.comm K R (field Q.c)).toLinearMap ∘ₗ LinearMap.lTensor R Q.fst

/-- The second base-changed coordinate. -/
def sndR : R ⊗[K] D →ₗ[K] field Q.c ⊗[K] R :=
  (TensorProduct.comm K R (field Q.c)).toLinearMap ∘ₗ LinearMap.lTensor R Q.snd

@[simp] theorem fstR_tmul (r : R) (d : D) : Q.fstR R (r ⊗ₜ[K] d) = Q.fst d ⊗ₜ[K] r := rfl

@[simp] theorem sndR_tmul (r : R) (d : D) : Q.sndR R (r ⊗ₜ[K] d) = Q.snd d ⊗ₜ[K] r := rfl

theorem decomposeR (b : R ⊗[K] D) :
    Q.ιR R (Q.fstR R b) + Q.jR R * Q.ιR R (Q.sndR R b) = b := by
  induction b using TensorProduct.inductionOn with
  | tmul r d =>
    rw [fstR_tmul, sndR_tmul, ιR_tmul, ιR_tmul, jR, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      ← TensorProduct.tmul_add, Q.decompose]
  | add a b ha hb =>
    simp only [map_add, mul_add]
    rw [add_add_add_comm, ha, hb]

theorem fstR_ιR (a : field Q.c ⊗[K] R) : Q.fstR R (Q.ιR R a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul a r => rw [ιR_tmul, fstR_tmul, fst_ι]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem sndR_ιR (a : field Q.c ⊗[K] R) : Q.sndR R (Q.ιR R a) = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul a r => rw [ιR_tmul, sndR_tmul, snd_ι, TensorProduct.zero_tmul]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

theorem fstR_jR_mul (a : field Q.c ⊗[K] R) : Q.fstR R (Q.jR R * Q.ιR R a) = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul a r =>
    rw [ιR_tmul, jR, Algebra.TensorProduct.tmul_mul_tmul, one_mul, fstR_tmul, fst_j_mul,
      TensorProduct.zero_tmul]
  | add a b ha hb => simp only [map_add, mul_add, ha, hb, add_zero]

theorem sndR_jR_mul (a : field Q.c ⊗[K] R) : Q.sndR R (Q.jR R * Q.ιR R a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul a r =>
    rw [ιR_tmul, jR, Algebra.TensorProduct.tmul_mul_tmul, one_mul, sndR_tmul, snd_j_mul]
  | add a b ha hb => simp only [map_add, mul_add, ha, hb]

/-- The presentation `R ⊗[K] D = ι(L ⊗ R) ⊕ j ι(L ⊗ R)`. -/
def presentation : Presentation (field Q.c ⊗[K] R) (R ⊗[K] D) where
  c := Q.tensorInvolution R
  ι := (Q.ιR R).toRingHom
  j := Q.jR R
  δ := Q.δR R
  bar_δ := Q.bar_δR R
  j_mul := Q.jR_mul R
  j_mul_self := Q.jR_mul_self R
  fst := (Q.fstR R).toAddMonoidHom
  snd := (Q.sndR R).toAddMonoidHom
  decompose := Q.decomposeR R
  fst_mk a a' := by
    change Q.fstR R (Q.ιR R a + Q.jR R * Q.ιR R a') = a
    rw [map_add, fstR_ιR, fstR_jR_mul, add_zero]
  snd_mk a a' := by
    change Q.sndR R (Q.ιR R a + Q.jR R * Q.ιR R a') = a'
    rw [map_add, sndR_ιR, sndR_jR_mul, zero_add]

@[simp] theorem presentation_ι (a : field Q.c ⊗[K] R) : (Q.presentation R).ι a = Q.ιR R a := rfl

@[simp] theorem presentation_j : (Q.presentation R).j = Q.jR R := rfl

@[simp] theorem presentation_c : (Q.presentation R).c = Q.tensorInvolution R := rfl

end BaseChange

section Naturality

variable {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
  (φ : R →ₐ[K] R')

/-- The coefficient map `L ⊗ R → L ⊗ R'`. -/
abbrev mapA : field Q.c ⊗[K] R →ₐ[K] field Q.c ⊗[K] R' :=
  Algebra.TensorProduct.map (AlgHom.id K (field Q.c)) φ

/-- The coefficient map `R ⊗ D → R' ⊗ D`. -/
abbrev mapB : R ⊗[K] D →ₐ[K] R' ⊗[K] D :=
  Algebra.TensorProduct.map φ (AlgHom.id K D)

theorem mapB_ιR (a : field Q.c ⊗[K] R) :
    mapB φ (Q.ιR R a) = Q.ιR R' (Q.mapA φ a) := by
  induction a using TensorProduct.inductionOn with
  | tmul a r => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem mapB_jR : mapB (D := D) φ (Q.jR R) = Q.jR R' := by
  simp [jR]

theorem mapA_bar (a : field Q.c ⊗[K] R) :
    Q.mapA φ ((Q.tensorInvolution R).bar a) = (Q.tensorInvolution R').bar (Q.mapA φ a) := by
  induction a using TensorProduct.inductionOn with
  | tmul a r => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem mapA_δR : Q.mapA φ (Q.δR R) = Q.δR R' := by
  simp [δR]

end Naturality

end QuatData

end Langlands.GroupScheme.KneserThree
