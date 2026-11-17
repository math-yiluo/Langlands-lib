import Langlands.Algebra.SeparatelyPolynomialQuadraticLine
import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.AbelianScheme.FieldAmpleExistenceProof
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AbelianScheme.FieldMultiplicationPullbackOfCube
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Picard.FiniteFlatEulerPolynomialCoefficientProof
import Langlands.AlgebraicGeometry.Picard.SmoothProperLineBundleEulerPolynomialProof
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # An Euler-coefficient degree on the endomorphisms of an abelian variety

For an abelian scheme `A` of relative dimension `g` over a field, fix an ample line bundle `L`.
The Euler-coefficient degree of an endomorphism `α` is the quotient of the `g`-th coefficients of
the Euler polynomials of `α^* L` and of `L`. It equals the degree on isogenies, and along every
line `n ↦ n • φ + ψ` it is a polynomial of degree at most `2 * g`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Order
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.EndomorphismEulerDegree

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
  Langlands.CategoryTheory

section Picard

variable {X Y : Scheme.{u}}

/-- The explicit tensor product of tensor-invertible modules is tensor-invertible. -/
theorem tensorObj_invertible {M N : X.Modules} (hM : TensorInvertible M)
    (hN : TensorInvertible N) : TensorInvertible (tensorObj M N) :=
  TensorInvertible.of_iso (localizedTensorIso X M N) (hM.tensor hN)

/-- The pullback of a line bundle is tensor-invertible. -/
theorem lineBundle_pullback_invertible (f : X ⟶ Y) (L : LineBundle Y) :
    TensorInvertible ((Scheme.Modules.pullback f).obj L.obj) :=
  (locallyFreeRankOneIffTensorInvertible X _).mpr (L.property.pullback f)

/-- Explicit tensor powers of a tensor-invertible module are tensor-invertible. -/
theorem tensorPow_invertible (M : X.Modules) (hM : TensorInvertible M) (n : ℕ) :
    TensorInvertible (tensorPow M n) := by
  induction n with
  | zero => exact TensorInvertible.unit
  | succ n ih => exact tensorObj_invertible hM ih

/-- The Picard class of an explicit tensor product is the sum of the classes. -/
theorem picard_tensorObj (M N : X.Modules) (hM : TensorInvertible M) (hN : TensorInvertible N)
    (hMN : TensorInvertible (tensorObj M N)) :
    PicardGroup.ofObject (tensorObj M N) hMN =
      PicardGroup.ofObject M hM + PicardGroup.ofObject N hN := by
  rw [← PicardGroup.ofObject_tensor M N hM hN]
  exact (PicardGroup.ofObject_eq_iff _ _ _ _).mpr ⟨(localizedTensorIso X M N).symm⟩

/-- The Picard class of an explicit tensor power is the corresponding multiple. -/
theorem picard_tensorPow (M : X.Modules) (hM : TensorInvertible M) (n : ℕ) :
    PicardGroup.ofObject (tensorPow M n) (tensorPow_invertible M hM n) =
      n • PicardGroup.ofObject M hM := by
  induction n with
  | zero => exact PicardGroup.ofObject_unit
  | succ n ih =>
    refine (picard_tensorObj M _ hM (tensorPow_invertible M hM n) _).trans ?_
    rw [ih]
    exact (succ_nsmul' _ _).symm

/-- The chosen representative of a Picard class, as a line bundle. -/
def lineOf (x : PicardGroup X.Modules) : LineBundle X :=
  ⟨PicardGroup.representative x,
    (locallyFreeRankOneIffTensorInvertible X _).mp (PicardGroup.representative_invertible x)⟩

/-- A line bundle on a proper scheme over a field has finite cohomology. -/
theorem lineBundle_hasFiniteCohomology {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] (L : LineBundle X) :
    HasFiniteCohomology f L.obj := by
  have := L.property.isQuasicoherent
  exact hasFiniteCohomology_of_coherent f L.obj (hasFiniteAffineSections_lineBundle L)

/-- The Euler characteristic of a Picard class on a proper scheme over a field, computed on its
chosen representative. -/
def eulerClass {K : Type u} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (x : PicardGroup X.Modules) : ℚ :=
  (eulerCharacteristic f (lineOf x).obj (lineBundle_hasFiniteCohomology f (lineOf x)) : ℚ)

/-- The Euler characteristic of a Picard class is that of any tensor-invertible module in it. -/
theorem eulerClass_ofObject {K : Type u} [Field K] (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] (M : X.Modules) (hM : TensorInvertible M) (h : HasFiniteCohomology f M) :
    eulerClass f (PicardGroup.ofObject M hM) = (eulerCharacteristic f M h : ℚ) := by
  obtain ⟨e⟩ := (PicardGroup.ofObject_eq_iff _ _ (PicardGroup.representative_invertible _)
    hM).mp (PicardGroup.ofObject_representative _)
  exact congrArg (Int.cast : ℤ → ℚ) (eulerCharacteristic_eq_of_iso f _ _ e)

/-- Under a dimension bound `g`, the Euler characteristic of `x • a + c` is a polynomial in
`x` of natural degree at most `g`. -/
theorem exists_eulerClass_nsmul_add {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsNoetherian X] [X.IsSeparated]
    {g : ℕ} (hX : topologicalKrullDim X ≤ g) (a c : PicardGroup X.Modules) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ g ∧
      ∀ x : ℕ, eulerClass f (x • a + c) = p.eval (x : ℚ) := by
  have := (lineOf c).property.isQuasicoherent
  refine ⟨coherentEulerPolynomial f (lineOf c).obj (hasFiniteAffineSections_lineBundle (lineOf c))
    (lineOf a) g, coherentEulerPolynomial_natDegree_le f _ _ _ g, fun x => ?_⟩
  rw [coherentEulerPolynomial_eval f _ _ _ g
    (HasSupportDimensionLT.of_topologicalKrullDim_le hX _) x]
  have hc := PicardGroup.representative_invertible c
  have ha := PicardGroup.representative_invertible a
  have hinv : TensorInvertible (tensorObj (lineOf c).obj (tensorPow (lineOf a).obj x)) :=
    tensorObj_invertible hc (tensorPow_invertible _ ha x)
  have hcl : PicardGroup.ofObject _ hinv = x • a + c := by
    erw [picard_tensorObj _ _ hc (tensorPow_invertible _ ha x)]
    erw [picard_tensorPow _ ha x]
    rw [PicardGroup.ofObject_representative, PicardGroup.ofObject_representative, add_comm]
  rw [← hcl]
  exact eulerClass_ofObject f _ hinv _

end Picard

/-- A sequence in an additive commutative group with constant second difference `P` is
quadratic: `q n = q 0 + n • (q 1 - q 0) + C(n, 2) • P`. -/
theorem eq_of_second_difference {M : Type*} [AddCommGroup M] (q : ℕ → M) (P : M)
    (hrec : ∀ n, q (n + 2) + q n = q (n + 1) + q (n + 1) + P) (n : ℕ) :
    q n = q 0 + n • (q 1 - q 0) + n.choose 2 • P := by
  have h : ∀ n, q n = q 0 + n • (q 1 - q 0) + n.choose 2 • P ∧
      q (n + 1) = q 0 + (n + 1) • (q 1 - q 0) + (n + 1).choose 2 • P := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp, ?_⟩
      simp only [zero_add, one_nsmul, Nat.choose_eq_zero_of_lt (show 1 < 2 by norm_num),
        zero_nsmul, add_zero]
      abel
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hc1 : (n + 1).choose 2 = n + n.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have hc2 : (n + 1 + 1).choose 2 = (n + 1) + (n + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have h2 := hrec n
      rw [ih.1, ih.2, hc1] at h2
      show q (n + 2) = _
      rw [eq_sub_of_add_eq h2, hc2, hc1]
      generalize q 1 - q 0 = D
      generalize n.choose 2 = C
      simp only [add_nsmul, one_nsmul]
      abel
  exact (h n).1

/-- Expanding a multiple of a quadratic expression in an additive commutative group. -/
theorem nsmul_quadratic {M : Type*} [AddCommGroup M] (a b c : M) (m n C : ℕ) :
    m • (a + n • b + C • c) = (m * C) • c + (m * n) • b + m • a := by
  rw [smul_add, smul_add, smul_smul, smul_smul]
  abel

variable {k : Type u} [Field k] (A : AbelianScheme (Spec (CommRingCat.of k)))

/-- A chosen ample line bundle on an abelian scheme over a field. -/
def ampleLineBundle : LineBundle A.X.left :=
  (Langlands.GroupScheme.fieldAmpleExistence k A.toGrp inferInstance inferInstance
    inferInstance).choose

theorem ampleLineBundle_isAmple : (ampleLineBundle A).IsAmple :=
  (Langlands.GroupScheme.fieldAmpleExistence k A.toGrp inferInstance inferInstance
    inferInstance).choose_spec

/-- The Euler polynomial, truncated in degree `g`, of the pullback of the chosen ample line
bundle along an endomorphism. -/
def eulerPolynomial (g : ℕ) (α : A ⟶ A) : Polynomial ℚ :=
  lineBundleEulerPolynomial A.X.hom
    ((LineBundle.pullback (AbelianScheme.hom α)).obj (ampleLineBundle A)) g

/-- The Euler-coefficient degree of an endomorphism `α`: the `g`-th coefficient of the Euler
polynomial of `α^* L` divided by that of `L`, for the chosen ample line bundle `L`. -/
def endomorphismEulerDegree (g : ℕ) (α : A ⟶ A) : ℚ :=
  (eulerPolynomial A g α).coeff g /
    (lineBundleEulerPolynomial A.X.hom (ampleLineBundle A) g).coeff g

/-- The Euler characteristic does not depend on how the structure morphism is written. -/
theorem eulerCharacteristic_congr {X : Scheme.{u}} {K : Type u} [Field K]
    {s s' : X ⟶ Spec (CommRingCat.of K)} (e : s = s') (M : X.Modules)
    (h : HasFiniteCohomology s M) (h' : HasFiniteCohomology s' M) :
    eulerCharacteristic s M h = eulerCharacteristic s' M h' := by
  subst e
  rfl

variable {A}

/-- The `g`-th coefficient of the Euler polynomial of the chosen ample line bundle is nonzero. -/
theorem coeff_lineBundleEulerPolynomial_ne_zero {g : ℕ} (hg : A.HasRelativeDimension g) :
    (lineBundleEulerPolynomial A.X.hom (ampleLineBundle A) g).coeff g ≠ 0 := by
  have := field_isNoetherian A
  have := field_isSeparated A
  have hX : topologicalKrullDim A.X.left ≤ g := (field_topologicalKrullDim hg).le
  obtain ⟨h, P, hP, -, hamp⟩ := smoothProperLineBundleEulerPolynomial k A.X g hg
    inferInstance inferInstance (ampleLineBundle A)
  obtain ⟨hdeg, hlc⟩ := hamp (ampleLineBundle_isAmple A)
  have heq : lineBundleEulerPolynomial A.X.hom (ampleLineBundle A) g = P := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [lineBundleEulerPolynomial_eval A.X.hom _ g hX n (h n), hP n]
  rw [heq, ← hdeg]
  exact hlc.ne'

/-- On isogenies the Euler-coefficient degree is the rank of the finite flat underlying
morphism at any point. -/
theorem endomorphismEulerDegree_isogeny {g : ℕ} (hg : A.HasRelativeDimension g) (β : A ⟶ A)
    (hβ : IsIsogeny β) (y : A.X.left) :
    endomorphismEulerDegree A g β = ((AbelianScheme.hom β).finrank y : ℚ) := by
  have := field_isNoetherian A
  have := field_isSeparated A
  have := field_isIntegral A
  obtain ⟨hfin, hflat, -⟩ := (isIsogeny_iff β).mp hβ
  have hX : topologicalKrullDim A.X.left ≤ g := (field_topologicalKrullDim hg).le
  have hw : AbelianScheme.hom β ≫ A.X.hom = A.X.hom := Over.w (groupHom β).hom.hom
  let L := ampleLineBundle A
  have hF : ∀ n, HasFiniteCohomology (AbelianScheme.hom β ≫ A.X.hom)
      (tensorPow ((Scheme.Modules.pullback (AbelianScheme.hom β)).obj L.obj) n) := by
    intro n
    rw [hw]
    exact lineBundleTensorPow_hasFiniteCohomology A.X.hom
      ((LineBundle.pullback (AbelianScheme.hom β)).obj L) n
  have key := finiteFlatEulerPolynomialCoefficient k A.X.left A.X.left A.X.hom inferInstance
    inferInstance inferInstance inferInstance (AbelianScheme.hom β) hfin hflat g hX L
    (lineBundleTensorPow_hasFiniteCohomology A.X.hom L) hF
    (lineBundleEulerPolynomial A.X.hom L g) (eulerPolynomial A g β)
    (fun n => lineBundleEulerPolynomial_eval A.X.hom L g hX n _)
    (fun n => by
      rw [eulerPolynomial, lineBundleEulerPolynomial_eval A.X.hom _ g hX n
        (lineBundleTensorPow_hasFiniteCohomology A.X.hom _ n)]
      exact congrArg (Int.cast : ℤ → ℚ) (eulerCharacteristic_congr hw.symm _ _ _))
    y
  rw [endomorphismEulerDegree, key, mul_div_assoc, div_self
    (coeff_lineBundleEulerPolynomial_ne_zero hg), mul_one]

variable (A)

/-- The Picard class of the pullback of the chosen ample line bundle along an endomorphism. -/
def classOf (α : A ⟶ A) : PicardGroup A.X.left.Modules :=
  PicardGroup.ofObject ((Scheme.Modules.pullback (AbelianScheme.hom α)).obj (ampleLineBundle A).obj)
    (lineBundle_pullback_invertible _ _)

/-- The theorem of the cube for the pullback classes of endomorphisms. -/
theorem classOf_cube (a₁ a₂ a₃ : A ⟶ A) :
    classOf A (a₁ + a₂ + a₃) + (classOf A a₁ + (classOf A a₂ + classOf A a₃)) =
      classOf A (a₁ + a₂) + (classOf A (a₁ + a₃) + classOf A (a₂ + a₃)) := by
  let inv := fun (e : A ⟶ A) =>
    lineBundle_pullback_invertible (AbelianScheme.hom e) (ampleLineBundle A)
  have heq := (PicardGroup.ofObject_eq_iff _ _
    (tensorObj_invertible (inv (a₁ + a₂ + a₃))
      (tensorObj_invertible (inv a₁) (tensorObj_invertible (inv a₂) (inv a₃))))
    (tensorObj_invertible (inv (a₁ + a₂))
      (tensorObj_invertible (inv (a₁ + a₃)) (inv (a₂ + a₃))))).mpr
        (Langlands.GroupScheme.fieldCubePullback k A.toGrp inferInstance inferInstance
          inferInstance A.X (groupHom a₁).hom.hom (groupHom a₂).hom.hom (groupHom a₃).hom.hom
          (ampleLineBundle A))
  rw [picard_tensorObj _ _ (inv (a₁ + a₂ + a₃))
      (tensorObj_invertible (inv a₁) (tensorObj_invertible (inv a₂) (inv a₃))),
    picard_tensorObj _ _ (inv a₁) (tensorObj_invertible (inv a₂) (inv a₃)),
    picard_tensorObj _ _ (inv a₂) (inv a₃),
    picard_tensorObj _ _ (inv (a₁ + a₂)) (tensorObj_invertible (inv (a₁ + a₃)) (inv (a₂ + a₃))),
    picard_tensorObj _ _ (inv (a₁ + a₃)) (inv (a₂ + a₃))] at heq
  exact heq

/-- Along a line, the pullback classes are quadratic in the parameter. -/
theorem classOf_nsmul_add (φ ψ : A ⟶ A) (n : ℕ) :
    classOf A (n • φ + ψ) = classOf A ((0 : ℕ) • φ + ψ) +
      n • (classOf A ((1 : ℕ) • φ + ψ) - classOf A ((0 : ℕ) • φ + ψ)) +
      n.choose 2 • (classOf A (φ + φ) - classOf A φ - classOf A φ) := by
  refine eq_of_second_difference (fun n : ℕ => classOf A (n • φ + ψ)) _ (fun n => ?_) n
  have h := classOf_cube A (n • φ + ψ) φ φ
  have e2 : n • φ + ψ + φ + φ = (n + 2) • φ + ψ := by
    rw [add_nsmul, two_nsmul]
    abel
  have e1 : n • φ + ψ + φ = (n + 1) • φ + ψ := by
    rw [add_nsmul, one_nsmul]
    abel
  rw [e2, e1] at h
  apply add_right_cancel (b := classOf A φ + classOf A φ)
  rw [add_assoc, h]
  abel

variable {A}

/-- Along every line `n ↦ n • φ + ψ` the Euler-coefficient degree is a polynomial in `n` of
natural degree at most `2 * g`. -/
theorem exists_endomorphismEulerDegree_line {g : ℕ} (hg : A.HasRelativeDimension g)
    (φ ψ : A ⟶ A) :
    ∃ R : Polynomial ℚ, R.natDegree ≤ 2 * g ∧
      ∀ n : ℕ, endomorphismEulerDegree A g (n • φ + ψ) = R.eval (n : ℚ) := by
  have := field_isNoetherian A
  have := field_isSeparated A
  have hX : topologicalKrullDim A.X.left ≤ g := (field_topologicalKrullDim hg).le
  let q : ℕ → PicardGroup A.X.left.Modules := fun n => classOf A (n • φ + ψ)
  let P := classOf A (φ + φ) - classOf A φ - classOf A φ
  let D := q 1 - q 0
  let G : ℕ → ℕ → ℕ → ℚ := fun x y z => eulerClass A.X.hom (x • P + y • D + z • q 0)
  have hx : ∀ y z, ∃ p : Polynomial ℚ, p.natDegree ≤ g ∧
      ∀ x : ℕ, G x y z = p.eval (x : ℚ) := by
    intro y z
    obtain ⟨p, hp, hpe⟩ := exists_eulerClass_nsmul_add A.X.hom hX P (y • D + z • q 0)
    exact ⟨p, hp, fun x => (congrArg (eulerClass A.X.hom) (by abel)).trans (hpe x)⟩
  have hy : ∀ x z, ∃ p : Polynomial ℚ, p.natDegree ≤ g ∧
      ∀ y : ℕ, G x y z = p.eval (y : ℚ) := by
    intro x z
    obtain ⟨p, hp, hpe⟩ := exists_eulerClass_nsmul_add A.X.hom hX D (x • P + z • q 0)
    exact ⟨p, hp, fun y => (congrArg (eulerClass A.X.hom) (by abel)).trans (hpe y)⟩
  have hz : ∀ x y, ∃ p : Polynomial ℚ, p.natDegree ≤ g ∧
      ∀ z : ℕ, G x y z = p.eval (z : ℚ) := by
    intro x y
    obtain ⟨p, hp, hpe⟩ := exists_eulerClass_nsmul_add A.X.hom hX (q 0) (x • P + y • D)
    exact ⟨p, hp, fun z => (congrArg (eulerClass A.X.hom) (by abel)).trans (hpe z)⟩
  let E : ℕ → Polynomial ℚ := fun n => eulerPolynomial A g (n • φ + ψ)
  have hE : ∀ n m : ℕ, (E n).eval (m : ℚ) = G (m * n.choose 2) (m * n) m := by
    intro n m
    let M := (Scheme.Modules.pullback (AbelianScheme.hom (n • φ + ψ))).obj (ampleLineBundle A).obj
    have hM : TensorInvertible M := lineBundle_pullback_invertible _ _
    have hcl : PicardGroup.ofObject (tensorPow M m) (tensorPow_invertible M hM m) =
        (m * n.choose 2) • P + (m * n) • D + m • q 0 := by
      rw [picard_tensorPow M hM m]
      change m • classOf A (n • φ + ψ) = _
      rw [classOf_nsmul_add A φ ψ n]
      exact nsmul_quadratic _ _ _ m n _
    show (eulerPolynomial A g (n • φ + ψ)).eval (m : ℚ) =
      eulerClass A.X.hom ((m * n.choose 2) • P + (m * n) • D + m • q 0)
    rw [eulerPolynomial, lineBundleEulerPolynomial_eval A.X.hom _ g hX m
      (lineBundleTensorPow_hasFiniteCohomology _ _ m), ← hcl]
    exact (eulerClass_ofObject A.X.hom _ _ _).symm
  obtain ⟨R, hR, hRe⟩ := Langlands.Algebra.SeparatelyPolynomial.exists_coeff_eq_eval_of_quadraticLine G hx hy hz
    E hE g
  refine ⟨Polynomial.C ((lineBundleEulerPolynomial A.X.hom (ampleLineBundle A) g).coeff g)⁻¹ * R,
    (Polynomial.natDegree_C_mul_le _ _).trans hR, fun n => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_C, endomorphismEulerDegree, div_eq_inv_mul]
  exact congrArg _ (hRe n)

/-- For an abelian scheme of relative dimension `g` over a field, the Euler-coefficient degree
equals the degree on isogenies and is polynomial of natural degree at most `2 * g` along every
line. -/
theorem endomorphismEulerDegree_spec {g : ℕ} (hg : A.HasRelativeDimension g) :
    (∀ β : A ⟶ A, IsIsogeny β → ∀ y : A.X.left,
        endomorphismEulerDegree A g β = ((AbelianScheme.hom β).finrank y : ℚ)) ∧
      ∀ φ ψ : A ⟶ A, ∃ R : Polynomial ℚ, R.natDegree ≤ 2 * g ∧
        ∀ n : ℕ, endomorphismEulerDegree A g (n • φ + ψ) = R.eval (n : ℚ) :=
  ⟨fun β hβ y => endomorphismEulerDegree_isogeny hg β hβ y,
    fun φ ψ => exists_endomorphismEulerDegree_line hg φ ψ⟩

end Langlands.AbelianScheme.EndomorphismEulerDegree
