import Langlands.Group.GL.Basic
import Langlands.JacquetLanglands.RegularElliptic

/-!
# The norm map of cyclic base change for `GL_n`

For a commutative ring `F`, a commutative `F`-algebra `E` and `σ : E ≃ₐ[F] E`: the
entrywise action `δ ↦ δ^σ` on `GL_n(E)`, the map `GL_n(F) → GL_n(E)` induced by
`algebraMap F E`, the norm `N(δ) = δ δ^σ ⋯ δ^{σ^{l-1}}`, association of elements of
`GL_n(E)` and `GL_n(F)`, norms, σ-regular and σ-elliptic elements, cyclic algebras and the
statement of the norm lemma, after Henniart–Lemaire (2011), §I.1.2 and §§I.2.1–I.2.3. For fields,
the elementary facts on rational points used throughout: an entrywise fixed matrix is rational when
the fixed scalars are, base change keeps regular semisimplicity, and regular semisimplicity is
invariant under conjugation. See the paired Markdown.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u v

section Ring

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]

/-- The automorphism `δ ↦ δ^σ` of `GL_n(E)`: `σ` applied to every entry. -/
def entrywiseAut (σ : E ≃ₐ[F] E) (n : ℕ) : GeneralLinear n E ≃* GeneralLinear n E where
  toFun := Matrix.GeneralLinearGroup.map (σ : E →+* E)
  invFun := Matrix.GeneralLinearGroup.map (σ.symm : E →+* E)
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' g h := map_mul _ g h

/-- The underlying homomorphism of `entrywiseAut σ n` is Mathlib's change of coefficients
along `σ`. -/
theorem entrywiseAut_toMonoidHom (σ : E ≃ₐ[F] E) (n : ℕ) :
    (entrywiseAut σ n).toMonoidHom = Matrix.GeneralLinearGroup.map (σ : E →+* E) :=
  rfl

@[simp]
theorem entrywiseAut_apply_apply (σ : E ≃ₐ[F] E) {n : ℕ} (g : GeneralLinear n E)
    (i j : Fin n) : entrywiseAut σ n g i j = σ (g i j) :=
  rfl

theorem entrywiseAut_one_apply {n : ℕ} (g : GeneralLinear n E) :
    entrywiseAut (1 : E ≃ₐ[F] E) n g = g := by
  ext i j
  simp

theorem entrywiseAut_mul_apply (σ τ : E ≃ₐ[F] E) {n : ℕ} (g : GeneralLinear n E) :
    entrywiseAut (σ * τ) n g = entrywiseAut σ n (entrywiseAut τ n g) := by
  ext i j
  simp [AlgEquiv.mul_apply]

variable (F E) in
/-- The homomorphism `GL_n(F) → GL_n(E)` induced by `algebraMap F E` (an inclusion when
`algebraMap F E` is injective). -/
def baseChange (n : ℕ) : GeneralLinear n F →* GeneralLinear n E :=
  Matrix.GeneralLinearGroup.map (algebraMap F E)

@[simp]
theorem baseChange_apply_apply {n : ℕ} (γ : GeneralLinear n F) (i j : Fin n) :
    baseChange F E n γ i j = algebraMap F E (γ i j) :=
  rfl

/-- The norm `N(δ) = δ · δ^σ · δ^{σ²} ⋯ δ^{σ^{l-1}}`, a product of `l` factors in this order
(the empty product `1` for `l = 0`). -/
def cyclicNorm (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (δ : GeneralLinear n E) : GeneralLinear n E :=
  ((List.range l).map fun i => entrywiseAut (σ ^ i) n δ).prod

@[simp]
theorem cyclicNorm_zero (σ : E ≃ₐ[F] E) {n : ℕ} (δ : GeneralLinear n E) :
    cyclicNorm σ 0 δ = 1 :=
  rfl

theorem cyclicNorm_succ (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (δ : GeneralLinear n E) :
    cyclicNorm σ (l + 1) δ = cyclicNorm σ l δ * entrywiseAut (σ ^ l) n δ := by
  simp [cyclicNorm, List.range_succ]

/-- Twisted conjugation by `x` changes the norm by `x⁻¹ * _ * x^{σ^l}`. -/
theorem cyclicNorm_twistedConj (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (x δ : GeneralLinear n E) :
    cyclicNorm σ l (x⁻¹ * δ * entrywiseAut σ n x) =
      x⁻¹ * cyclicNorm σ l δ * entrywiseAut (σ ^ l) n x := by
  induction l with
  | zero => simp [entrywiseAut_one_apply]
  | succ l ih =>
    rw [cyclicNorm_succ, cyclicNorm_succ, ih, map_mul, map_mul, map_inv,
      ← entrywiseAut_mul_apply, ← pow_succ]
    group

/-- The entrywise action commutes with the norm. -/
theorem entrywiseAut_cyclicNorm_eq (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (δ : GeneralLinear n E) :
    entrywiseAut σ n (cyclicNorm σ l δ) = cyclicNorm σ l (entrywiseAut σ n δ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [cyclicNorm_succ, cyclicNorm_succ, map_mul, ih, ← entrywiseAut_mul_apply,
      ← entrywiseAut_mul_apply, ← pow_succ, ← pow_succ']

/-- `N(δ)^σ = δ⁻¹ · N(δ) · δ^{σ^l}`. -/
theorem entrywiseAut_cyclicNorm (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (δ : GeneralLinear n E) :
    entrywiseAut σ n (cyclicNorm σ l δ) =
      δ⁻¹ * cyclicNorm σ l δ * entrywiseAut (σ ^ l) n δ := by
  rw [entrywiseAut_cyclicNorm_eq, ← cyclicNorm_twistedConj, inv_mul_cancel, one_mul]

/-- Elements of `GL_n(F)` are fixed by the entrywise action of `σ`. -/
theorem entrywiseAut_baseChange (σ : E ≃ₐ[F] E) {n : ℕ} (γ : GeneralLinear n F) :
    entrywiseAut σ n (baseChange F E n γ) = baseChange F E n γ := by
  ext i j
  simp

/-- The norm of `δ b` for `b` rational and commuting with `δ` is `N(δ) b^l`. -/
theorem cyclicNorm_mul_baseChange (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ}
    (δ : GeneralLinear n E) (s : GeneralLinear n F)
    (hs : Commute δ (baseChange F E n s)) :
    cyclicNorm σ l (δ * baseChange F E n s) =
      cyclicNorm σ l δ * baseChange F E n s ^ l := by
  let b := baseChange F E n s
  change cyclicNorm σ l (δ * b) = cyclicNorm σ l δ * b ^ l
  induction l with
  | zero => simp
  | succ l ih =>
    have hcomm : Commute (entrywiseAut (σ ^ l) n δ) b := by
      simpa only [b, entrywiseAut_baseChange] using hs.map (entrywiseAut (σ ^ l) n)
    calc
      cyclicNorm σ (l + 1) (δ * b) =
          cyclicNorm σ l δ * b ^ l * (entrywiseAut (σ ^ l) n δ * b) := by
        rw [cyclicNorm_succ, ih, map_mul]
        rw [show entrywiseAut (σ ^ l) n b = b from entrywiseAut_baseChange _ s]
      _ = cyclicNorm σ l δ * entrywiseAut (σ ^ l) n δ * (b ^ l * b) :=
        (hcomm.symm.pow_left l).mul_mul_mul_comm _ _
      _ = cyclicNorm σ (l + 1) δ * b ^ (l + 1) := by rw [cyclicNorm_succ, pow_succ]

/-- `δ ∈ GL_n(E)` and `γ ∈ GL_n(F)` are associated when `N(δ)` is conjugate in `GL_n(E)`
to `γ` (Henniart–Lemaire, I.1.2). -/
def IsNormAssociated (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (δ : GeneralLinear n E)
    (γ : GeneralLinear n F) : Prop :=
  ∃ g : GeneralLinear n E, g⁻¹ * cyclicNorm σ l δ * g = baseChange F E n γ

/-- `γ ∈ GL_n(F)` is a norm from `GL_n(E)`: it is associated with some `δ ∈ GL_n(E)`. -/
def IsNorm (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (γ : GeneralLinear n F) : Prop :=
  ∃ δ : GeneralLinear n E, IsNormAssociated σ l δ γ

/-- When `σ ^ l = 1`, association is invariant under σ-conjugation of `δ` and conjugation
of `γ`. -/
theorem IsNormAssociated.twistedConj {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : σ ^ l = 1) {n : ℕ}
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (h : IsNormAssociated σ l δ γ)
    (x : GeneralLinear n E) (y : GeneralLinear n F) :
    IsNormAssociated σ l (x⁻¹ * δ * entrywiseAut σ n x) (y⁻¹ * γ * y) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨x⁻¹ * g * baseChange F E n y, ?_⟩
  rw [cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, map_mul, map_mul, map_inv, ← hg]
  group

end Ring

section Field

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]

/-- `δ ∈ GL_n(E)` is σ-regular when it is associated with a regular semisimple element of
`GL_n(F)`. -/
def IsSigmaRegular (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (δ : GeneralLinear n E) : Prop :=
  ∃ γ : GeneralLinear n F, IsNormAssociated σ l δ γ ∧ IsRegularSemisimple γ

/-- `δ ∈ GL_n(E)` is σ-elliptic when it is associated with a regular elliptic element of
`GL_n(F)`. -/
def IsSigmaElliptic (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (δ : GeneralLinear n E) : Prop :=
  ∃ γ : GeneralLinear n F, IsNormAssociated σ l δ γ ∧ IsRegularElliptic γ

/-- `E` is a cyclic `F`-algebra of group `⟨σ⟩` of order `l` (Henniart–Lemaire, I.2.1): `E` is
a finite reduced `F`-algebra of dimension `l`, `σ` has order `l`, and the elements of `E` fixed
by `σ` are those of `F`. -/
def IsCyclicAlgebra (σ : E ≃ₐ[F] E) (l : ℕ) : Prop :=
  Module.Finite F E ∧ Module.finrank F E = l ∧ IsReduced E ∧ orderOf σ = l ∧
    ∀ x : E, σ x = x → x ∈ (algebraMap F E).range

/-- For a cyclic algebra of degree `l`, `σ ^ l = 1`, the hypothesis of
`IsNormAssociated.twistedConj`. -/
theorem IsCyclicAlgebra.pow_eq_one {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) :
    σ ^ l = 1 := by
  rw [← h.2.2.2.1]
  exact pow_orderOf_eq_one σ

/-- The degree of a cyclic algebra is positive. -/
theorem IsCyclicAlgebra.pos {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) : 0 < l := by
  obtain ⟨_, hrank, -, hord, -⟩ := h
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have : Subsingleton E := Module.finrank_zero_iff.mp hrank
    have hσ : σ = 1 := AlgEquiv.ext fun _ => Subsingleton.elim _ _
    rw [hσ, orderOf_one] at hord
    exact absurd hord one_ne_zero
  · exact hl

/-- Nonvacuity check: `F` is a cyclic algebra over itself of degree `1`. -/
theorem isCyclicAlgebra_one : IsCyclicAlgebra (1 : F ≃ₐ[F] F) 1 := by
  refine ⟨inferInstance, Module.finrank_self F, inferInstance, orderOf_one, ?_⟩
  intro x _
  exact ⟨x, rfl⟩

end Field

section Descent

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- An entrywise fixed invertible matrix descends when the fixed scalars lie in
 the image of the base field. -/
theorem exists_baseChange_eq_of_entrywiseAut_eq {σ : L ≃ₐ[K] L}
    (hfix : ∀ a : L, σ a = a → a ∈ (algebraMap K L).range)
    {n : ℕ} {x : GeneralLinear n L} (hx : entrywiseAut σ n x = x) :
    ∃ y : GeneralLinear n K, baseChange K L n y = x := by
  classical
  have hentry (i j : Fin n) : x i j ∈ (algebraMap K L).range :=
    hfix _ (congrArg (fun g : GeneralLinear n L => g i j) hx)
  choose a ha using hentry
  let A : Matrix (Fin n) (Fin n) K := a
  have hmap : A.map (algebraMap K L) = x.val := Matrix.ext ha
  have hdet : A.det ≠ 0 := by
    intro h
    apply x.det_ne_zero
    rw [← hmap]
    change ((RingHom.mapMatrix (algebraMap K L)) A).det = 0
    rw [← RingHom.map_det, h, map_zero]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, Matrix.GeneralLinearGroup.ext ha⟩

end Descent

section FieldExtension

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {n : ℕ}

/-- For a cyclic algebra that is a field, an element of `GL_n(E)` fixed by `σ` is rational. -/
theorem IsCyclicAlgebra.exists_baseChange_eq_of_entrywiseAut_eq {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) {g : GeneralLinear n E} (hg : entrywiseAut σ n g = g) :
    ∃ x : GeneralLinear n F, baseChange F E n x = g :=
  Langlands.BaseChange.exists_baseChange_eq_of_entrywiseAut_eq hσ.2.2.2.2 hg

/-- Entrywise extension of scalars preserves separability of the characteristic polynomial. -/
theorem isRegularSemisimple_baseChange {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) :
    IsRegularSemisimple (baseChange F E n γ) := by
  change (γ.val.map (algebraMap F E)).charpoly.Separable
  rw [Matrix.charpoly_map]
  exact Polynomial.Separable.map hγ

/-- Separability of the characteristic polynomial is kept by scalar extension (the form of
`isRegularSemisimple_baseChange` for dot notation). -/
theorem _root_.Langlands.JacquetLanglands.IsRegularSemisimple.baseChange {γ : GeneralLinear n F}
    (hγ : IsRegularSemisimple γ) :
    IsRegularSemisimple (baseChange F E n γ) :=
  isRegularSemisimple_baseChange hγ

/-- Regular semisimplicity is invariant under conjugation. -/
theorem isRegularSemisimple_conj_iff (y γ : GeneralLinear n F) :
    IsRegularSemisimple (y⁻¹ * γ * y) ↔ IsRegularSemisimple γ := by
  have e : y⁻¹ * γ * y = y⁻¹ * γ * (y⁻¹)⁻¹ := by rw [inv_inv]
  change (((y⁻¹ * γ * y : GeneralLinear n F)) : Matrix (Fin n) (Fin n) F).charpoly.Separable ↔
    (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable
  rw [e, Units.val_mul, Units.val_mul, Matrix.coe_units_inv (y⁻¹), Matrix.charpoly_units_conj]

end FieldExtension

/-- The norm lemma of Henniart–Lemaire (2011), I.2.2, Lemme: for a cyclic `F`-algebra `E`
of group `⟨σ⟩` of order `l`,
(1a) every `δ ∈ GL_n(E)` is associated with some `γ ∈ GL_n(F)`;
(1b) two elements of `GL_n(F)` associated with the same `δ` are conjugate in `GL_n(F)`;
(2) if `N(δ)` and `N(δ')` are conjugate in `GL_n(E)`, then `δ` and `δ'` are σ-conjugate. -/
def CyclicNormLemmaStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [CommRing E] [Algebra F E] (σ : E ≃ₐ[F] E)
    (l n : ℕ), IsCyclicAlgebra σ l →
    (∀ δ : GeneralLinear n E, ∃ γ : GeneralLinear n F, IsNormAssociated σ l δ γ) ∧
    (∀ (δ : GeneralLinear n E) (γ γ' : GeneralLinear n F),
      IsNormAssociated σ l δ γ → IsNormAssociated σ l δ γ' →
        ∃ y : GeneralLinear n F, y⁻¹ * γ * y = γ') ∧
    (∀ δ δ' : GeneralLinear n E,
      (∃ g : GeneralLinear n E, g⁻¹ * cyclicNorm σ l δ * g = cyclicNorm σ l δ') →
        ∃ x : GeneralLinear n E, x⁻¹ * δ * entrywiseAut σ n x = δ')

end Langlands.BaseChange
