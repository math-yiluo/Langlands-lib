import Langlands.GroupScheme.Rational.CyclicWeightCoordinates

/-! # Conjugation by a torus-fixed point on cyclic weight subgroups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section Yoneda

/-- A natural endomorphism of the points of a corepresented functor acts on coordinates by
precomposition with the coordinates of the image of the universal point. -/
theorem coord_natural {c : ∀ A : CommAlgCat.{u} R, F.obj A → F.obj A}
    (hc : ∀ {A A' : CommAlgCat.{u} R} (f : A ⟶ A') (x : F.obj A),
      c A' (F.map f x) = F.map f (c A x))
    {A : CommAlgCat.{u} R} (x : F.obj A) :
    coord e (c A x) = (coord e x).comp (coord e (c B (univ e))) := by
  have h := hc (e.homEquiv.symm x) (univ e)
  rw [← eq_map_univ e x] at h
  rw [h, coord_map]

end Yoneda

section Torus

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- The coordinate endomorphism of a natural endomorphism commuting with the torus action
preserves homogeneous elements and their weights. -/
theorem isHomogeneous_coord_natural {c : ∀ A : CommAlgCat.{u} R, F.obj A → F.obj A}
    (hc : ∀ {A A' : CommAlgCat.{u} R} (f : A ⟶ A') (x : F.obj A),
      c A' (F.map f x) = F.map f (c A x))
    (hact : ∀ {A : CommAlgCat.{u} R} (t : I → Aˣ) (x : F.obj A),
      c A (σ.act t x) = σ.act t (c A x))
    {m : I → ℤ} {g : B} (hg : IsHomogeneous e σ m g) :
    IsHomogeneous e σ m (coord e (c B (univ e)) g) := by
  have hhat : c (laurent I B) (hat σ (univ e)) = hat σ (c B (univ e)) := by
    change c _ (σ.act (universalUnits I B) (F.map (constHom I B) (univ e))) =
      σ.act (universalUnits I B) (F.map (constHom I B) (c B (univ e)))
    rw [hact, hc]
  change rho e σ (coord e (c B (univ e)) g) = AddMonoidAlgebra.single m (coord e (c B (univ e)) g)
  rw [rho, ← AlgHom.comp_apply, ← coord_natural e hc (hat σ (univ e)), hhat, coord_hat,
    AlgHom.comp_apply, hg, AddMonoidAlgebra.mapAlgHom_single]

/-- The constants of the group algebra lie in every supported subalgebra. -/
def constSupported (A : CommAlgCat.{u} R) (M : AddSubmonoid (I → ℤ)) :
    A ⟶ CommAlgCat.of R (supportedSubalgebra I A M) :=
  CommAlgCat.ofHom ((AddMonoidAlgebra.singleZeroAlgHom).codRestrict _ fun c m hm => by
    change (AddMonoidAlgebra.single 0 c : AddMonoidAlgebra A (I → ℤ)).coeff m = 0
    rw [AddMonoidAlgebra.coeff_single]
    exact Finsupp.single_eq_of_ne fun h => hm (by rw [h]; exact M.zero_mem))

/-- Conjugation by a point whose twisted point is constant preserves every weight subgroup. -/
theorem conj_mem_weightSubgroup_of_hat_eq (P : AddSubsemigroup (I → ℤ))
    {A : CommAlgCat.{u} R} {z y : F.obj A} (hz : hat σ z = F.map (constHom I A) z)
    (hy : y ∈ weightSubgroup e σ P A) : z * y * z⁻¹ ∈ weightSubgroup e σ P A := by
  have hy' := hat_mem_kerSubgroup e σ (P : Set (I → ℤ)) (insertZero P) (Set.subset_insert _ _)
    (insertZero_add_mem P) hy
  refine (weightCondition_iff e σ _ _ (Set.subset_insert _ _) (insertZero_add_mem P) _).2 ?_
  rw [map_mul, map_mul, map_inv]
  refine conj_mem_kerSubgroup _ _ ?_ hy'
  rw [hz]
  refine ⟨F.map (constSupported A (insertZero P)) z, ?_⟩
  change (F.map (constSupported A (insertZero P)) ≫ F.map (subalgebraHom _)) z = _
  rw [← F.map_comp]
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The action of a family of units is a group homomorphism, so it commutes with inverses. -/
theorem TorusAction.act_inv {A : CommAlgCat.{u} R} (t : I → Aˣ) (x : F.obj A) :
    σ.act t x⁻¹ = (σ.act t x)⁻¹ := by
  have h1 : σ.act t (1 : F.obj A) = 1 := by
    have h := σ.act_map_mul t 1 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  apply eq_inv_of_mul_eq_one_left
  rw [← σ.act_map_mul, inv_mul_cancel, h1]

omit [Fintype I] in
/-- A natural family of torus-fixed points has constant twisted points. -/
theorem hat_eq_of_fixed {z : ∀ A : CommAlgCat.{u} R, F.obj A}
    (hzn : ∀ {A A' : CommAlgCat.{u} R} (f : A ⟶ A'), F.map f (z A) = z A')
    (hzf : ∀ {A : CommAlgCat.{u} R} (t : I → Aˣ), σ.act t (z A) = z A) (A : CommAlgCat.{u} R) :
    hat σ (z A) = F.map (constHom I A) (z A) := by
  change σ.act (universalUnits I A) (F.map (constHom I A) (z A)) = _
  rw [hzn, hzf]

variable {z : ∀ A : CommAlgCat.{u} R, F.obj A}
  (hzn : ∀ {A A' : CommAlgCat.{u} R} (f : A ⟶ A'), F.map f (z A) = z A')
  (hzf : ∀ {A : CommAlgCat.{u} R} (t : I → Aˣ), σ.act t (z A) = z A)

/-- Conjugation by a natural family of torus-fixed points on the points of a weight
subgroup. -/
def cutConj (P : AddSubsemigroup (I → ℤ)) (A : CommAlgCat.{u} R)
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ P)).obj A) :
    (cutFunctor (isCutOutBy_weightIdeal e σ P)).obj A :=
  ⟨z A * u.1 * (z A)⁻¹, conj_mem_weightSubgroup_of_hat_eq e σ P (hat_eq_of_fixed σ hzn hzf A) u.2⟩

@[simp] theorem cutConj_val (P : AddSubsemigroup (I → ℤ)) (A : CommAlgCat.{u} R)
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ P)).obj A) :
    (cutConj e σ hzn hzf P A u).1 = z A * u.1 * (z A)⁻¹ := rfl

theorem cutConj_natural (P : AddSubsemigroup (I → ℤ)) {A A' : CommAlgCat.{u} R} (f : A ⟶ A')
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ P)).obj A) :
    cutConj e σ hzn hzf P A' ((cutFunctor (isCutOutBy_weightIdeal e σ P)).map f u) =
      (cutFunctor (isCutOutBy_weightIdeal e σ P)).map f (cutConj e σ hzn hzf P A u) := by
  apply Subtype.ext
  change z A' * F.map f u.1 * (z A')⁻¹ = F.map f (z A * u.1 * (z A)⁻¹)
  rw [map_mul, map_mul, map_inv, hzn]

theorem cutConj_act (P : AddSubsemigroup (I → ℤ)) {A : CommAlgCat.{u} R} (t : I → Aˣ)
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ P)).obj A) :
    cutConj e σ hzn hzf P A ((weightAction e σ P).act t u) =
      (weightAction e σ P).act t (cutConj e σ hzn hzf P A u) := by
  apply Subtype.ext
  change z A * σ.act t u.1 * (z A)⁻¹ = σ.act t (z A * u.1 * (z A)⁻¹)
  rw [σ.act_map_mul, σ.act_map_mul, TorusAction.act_inv, hzf]

/-- The coordinate endomorphism of the conjugation. -/
def conjCoord (P : AddSubsemigroup (I → ℤ)) :
    B ⧸ weightIdeal e σ P →ₐ[R] B ⧸ weightIdeal e σ P :=
  coord (weightCorep e σ P) (cutConj e σ hzn hzf P _ (univ (weightCorep e σ P)))

theorem coord_cutConj (P : AddSubsemigroup (I → ℤ)) {A : CommAlgCat.{u} R}
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ P)).obj A) :
    coord (weightCorep e σ P) (cutConj e σ hzn hzf P A u) =
      (coord (weightCorep e σ P) u).comp (conjCoord e σ hzn hzf P) :=
  coord_natural (weightCorep e σ P) (fun f u => cutConj_natural e σ hzn hzf P f u) u

theorem isHomogeneous_conjCoord (P : AddSubsemigroup (I → ℤ)) {m : I → ℤ}
    {g : B ⧸ weightIdeal e σ P}
    (hg : IsHomogeneous (weightCorep e σ P) (weightAction e σ P) m g) :
    IsHomogeneous (weightCorep e σ P) (weightAction e σ P) m (conjCoord e σ hzn hzf P g) :=
  isHomogeneous_coord_natural (weightCorep e σ P) (weightAction e σ P)
    (fun f u => cutConj_natural e σ hzn hzf P f u) (fun t u => cutConj_act e σ hzn hzf P t u) hg

end Torus

section Matrix

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)
  {z : ∀ A : CommAlgCat.{u} (CommRingCat.of k), F.obj A}
  (hzn : ∀ {A A' : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ A'), F.map f (z A) = z A')
  (hzf : ∀ {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ), σ.act t (z A) = z A)
  {a : I → ℤ} (ha : a ≠ 0)
  {n : ℕ} {d : Fin n → ℕ} {x : Fin n → B ⧸ weightIdeal e σ (cyclicTail a 1)}
  (hd : ∀ i, 0 < d i)
  (hx : ∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a 1))
    (weightAction e σ (cyclicTail a 1)) (d i • a) (x i))
  (hsurj : Function.Surjective
    (aeval x : MvPolynomial (Fin n) k →ₐ[k] B ⧸ weightIdeal e σ (cyclicTail a 1)))

include ha hx hsurj in
/-- The conjugate of a graded coordinate is a weighted homogeneous polynomial of the same
weight in the graded coordinates. -/
theorem exists_conjCoord_eq_aeval (i : Fin n) :
    ∃ p : MvPolynomial (Fin n) k, p.IsWeightedHomogeneous d (d i) ∧
      aeval x p = conjCoord e σ hzn hzf (cyclicTail a 1) (x i) := by
  have hφ : Function.Injective (multiplesHom (I → ℤ) a) := nsmul_left_injective_of_ne_zero ha
  let _ := gradedAlgebra (weightCorep e σ (cyclicTail a 1)) (weightAction e σ (cyclicTail a 1)) hφ
    (comp_cyclicTail_mem_range e σ 1)
  let 𝒜 : ℕ → Submodule k (B ⧸ weightIdeal e σ (cyclicTail a 1)) := fun j =>
    homogeneousSubmodule (weightCorep e σ (cyclicTail a 1)) (weightAction e σ (cyclicTail a 1))
      (multiplesHom (I → ℤ) a j)
  have hx' : ∀ j, x j ∈ 𝒜 (d j) := fun j => (mem_homogeneousSubmodule _ _ _ _).2 (hx j)
  have hg : conjCoord e σ hzn hzf (cyclicTail a 1) (x i) ∈ 𝒜 (d i) :=
    (mem_homogeneousSubmodule _ _ _ _).2 (isHomogeneous_conjCoord e σ hzn hzf _ (hx i))
  obtain ⟨p, hp⟩ := hsurj (conjCoord e σ hzn hzf (cyclicTail a 1) (x i))
  refine ⟨weightedHomogeneousComponent d (d i) p,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  have h1 := Langlands.Algebra.GradedFormallySmooth.decompose_aeval 𝒜 hx' p (d i)
  rw [hp, DirectSum.decompose_of_mem_same 𝒜 hg] at h1
  exact h1.symm

/-- A choice of weighted homogeneous polynomials expressing the conjugated coordinates. -/
def conjPoly (i : Fin n) : MvPolynomial (Fin n) k :=
  (exists_conjCoord_eq_aeval e σ hzn hzf ha hx hsurj i).choose

theorem conjPoly_isWeightedHomogeneous (i : Fin n) :
    (conjPoly e σ hzn hzf ha hx hsurj i).IsWeightedHomogeneous d (d i) :=
  (exists_conjCoord_eq_aeval e σ hzn hzf ha hx hsurj i).choose_spec.1

theorem aeval_conjPoly (i : Fin n) :
    aeval x (conjPoly e σ hzn hzf ha hx hsurj i) = conjCoord e σ hzn hzf (cyclicTail a 1) (x i) :=
  (exists_conjCoord_eq_aeval e σ hzn hzf ha hx hsurj i).choose_spec.2

/-- The linear part of the conjugation in the graded coordinates. -/
def conjMatrix : Matrix (Fin n) (Fin n) k := fun i j =>
  (conjPoly e σ hzn hzf ha hx hsurj i).coeff (Finsupp.single j 1)

include hd in
/-- **Linearity on the graded pieces.** On `U_r`, conjugation acts on the coordinates of weight
`r` by the corresponding block of the linear part. -/
theorem coord_cutConj_eq_sum {A : CommAlgCat.{u} (CommRingCat.of k)}
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A) {r : ℕ} (hr : 0 < r)
    (hu : u.1 ∈ weightSubgroup e σ (cyclicTail a r) A) {i : Fin n} (hi : d i = r) :
    coord (weightCorep e σ (cyclicTail a 1)) (cutConj e σ hzn hzf (cyclicTail a 1) A u) (x i) =
      ∑ j ∈ Finset.univ.filter (fun j => d j = r),
        algebraMap k A (conjMatrix e σ hzn hzf ha hx hsurj i j) *
          coord (weightCorep e σ (cyclicTail a 1)) u (x j) := by
  have hv := (mem_weightSubgroup_iff_coord_eq_zero e σ ha hd hx hsurj u).1 hu
  rw [coord_cutConj, AlgHom.comp_apply, ← aeval_conjPoly e σ hzn hzf ha hx hsurj i,
    comp_aeval_apply]
  have hp := conjPoly_isWeightedHomogeneous e σ hzn hzf ha hx hsurj i
  rw [hi] at hp
  exact aeval_eq_sum_of_isWeightedHomogeneous hd hr hp hv

/-- The linear part of the conjugation preserves the weights of the coordinates. -/
theorem conjMatrix_eq_zero_of_ne {i j : Fin n} (h : d j ≠ d i) :
    conjMatrix e σ hzn hzf ha hx hsurj i j = 0 := by
  refine (conjPoly_isWeightedHomogeneous e σ hzn hzf ha hx hsurj i).coeff_eq_zero _ ?_
  rw [Finsupp.weight_single, one_smul]
  exact h

/-- The linear part is block triangular for the weights. -/
theorem conjMatrix_blockTriangular :
    (conjMatrix e σ hzn hzf ha hx hsurj).BlockTriangular d := fun _ _ h =>
  conjMatrix_eq_zero_of_ne e σ hzn hzf ha hx hsurj (ne_of_lt h)

/-- The determinant of the linear part is the product of its weight blocks. -/
theorem det_conjMatrix :
    (conjMatrix e σ hzn hzf ha hx hsurj).det =
      ∏ s ∈ Finset.univ.image d,
        ((conjMatrix e σ hzn hzf ha hx hsurj).toSquareBlock d s).det :=
  (conjMatrix_blockTriangular e σ hzn hzf ha hx hsurj).det

end Matrix

end Langlands.GroupScheme.Corepresented
