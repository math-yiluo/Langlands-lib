import Langlands.GroupScheme.Rational.TorusWeightPolynomial
import Langlands.GroupScheme.Lie.AffineModule

/-! # Primitive weight coordinates on cyclic weight subgroups -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section DualNumbers

variable {A : CommAlgCat.{u} R}

/-- On points over the dual numbers which reduce to the identity, the infinitesimal parts of
the coordinates add. -/
theorem snd_coord_mul {z z' : F.obj (CommAlgCat.of R (DualNumber A))}
    (hz : F.map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)) z = 1)
    (hz' : F.map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)) z' = 1) (f : B) :
    (coord e (z * z') f).snd = (coord e z f).snd + (coord e z' f).snd := by
  have push : ∀ (g : A × A →ₗ[A] A) (h : A →ₗ[A] A × A)
      (x : F.obj (CommAlgCat.of R (DualNumber A))),
      F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) g))
          (F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) h)) x) =
        F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) (g.comp h))) x := by
    intro g h x
    apply coord_injective e
    rw [coord_map, coord_map, coord_map, Lie.squareMap_comp]
    rfl
  have hid : ∀ x : F.obj (CommAlgCat.of R (DualNumber A)),
      F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) (LinearMap.id : A →ₗ[A] A))) x = x := by
    intro x
    apply coord_injective e
    rw [coord_map, Lie.squareMap_id]
    rfl
  have hzero : ∀ x : F.obj (CommAlgCat.of R (DualNumber A)),
      F.map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)) x = 1 →
        F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) (0 : A →ₗ[A] A))) x = 1 := by
    intro x hx
    refine (eq_one_iff e).2 fun f => ?_
    have h := (eq_one_iff e).1 hx f
    rw [coord_map, AlgHom.comp_apply, CommAlgCat.hom_ofHom] at h
    rw [coord_map, Lie.squareMap_zero, AlgHom.comp_apply, CommAlgCat.hom_ofHom,
      AlgHom.comp_apply, h, TrivSqZeroExt.algebraMap_eq_inl']
    rfl
  set w : F.obj (CommAlgCat.of R (TrivSqZeroExt A (A × A))) :=
    F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) (LinearMap.inl A A A))) z *
      F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) (LinearMap.inr A A A))) z' with hw
  have h1 : F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) (LinearMap.fst A A A))) w = z := by
    rw [hw, map_mul, push, push, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hid,
      hzero z' hz', mul_one]
  have h2 : F.map (CommAlgCat.ofHom (Lie.squareMap (R := R) (LinearMap.snd A A A))) w = z' := by
    rw [hw, map_mul, push, push, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hid,
      hzero z hz, one_mul]
  have h3 : F.map (CommAlgCat.ofHom (Lie.squareMap (R := R)
      (LinearMap.id.coprod LinearMap.id : A × A →ₗ[A] A))) w = z * z' := by
    rw [hw, map_mul, push, push, LinearMap.coprod_inl, LinearMap.coprod_inr, hid, hid]
  have c1 := congrArg (fun p : F.obj (CommAlgCat.of R (DualNumber A)) => (coord e p f).snd) h1
  have c2 := congrArg (fun p : F.obj (CommAlgCat.of R (DualNumber A)) => (coord e p f).snd) h2
  have c3 := congrArg (fun p : F.obj (CommAlgCat.of R (DualNumber A)) => (coord e p f).snd) h3
  simp only [coord_map, AlgHom.comp_apply, CommAlgCat.hom_ofHom, Lie.squareMap_snd,
    LinearMap.fst_apply] at c1
  simp only [coord_map, AlgHom.comp_apply, CommAlgCat.hom_ofHom, Lie.squareMap_snd,
    LinearMap.snd_apply] at c2
  simp only [coord_map, AlgHom.comp_apply, CommAlgCat.hom_ofHom, Lie.squareMap_snd,
    LinearMap.coprod_apply, LinearMap.id_apply] at c3
  rw [← c1, ← c2, ← c3]

end DualNumbers

section Supported

variable {I : Type u} [Fintype I] [DecidableEq I] {A : CommAlgCat.{u} R}

omit [Fintype I] [DecidableEq I] in
/-- The coefficient of `χ` of a product of elements supported on `{0} ∪ P`, when `χ` is not a
sum of two elements of `P`. -/
theorem coeff_mul_of_supported {P : AddSubsemigroup (I → ℤ)} {χ : I → ℤ} (hχ0 : χ ≠ 0)
    (hχ : ∀ i ∈ P, ∀ j ∈ P, i + j ≠ χ) {x y : AddMonoidAlgebra A (I → ℤ)}
    (hx : ∀ i ∉ insertZero P, x.coeff i = 0) (hy : ∀ j ∉ insertZero P, y.coeff j = 0) :
    (x * y).coeff χ = x.coeff 0 * y.coeff χ + x.coeff χ * y.coeff 0 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum,
    Finset.sum_eq_add (0 : I → ℤ) χ hχ0.symm]
  · rw [neg_zero, zero_add, neg_add_cancel]
  · rintro i - ⟨hi0, hiχ⟩
    by_cases hxi : x.coeff i = 0
    · rw [hxi, zero_mul]
    by_cases hyj : y.coeff (-i + χ) = 0
    · rw [hyj, mul_zero]
    exfalso
    rcases (mem_insertZero P i).1 (by_contra fun h => hxi (hx i h)) with h | hiP
    · exact hi0 h
    rcases (mem_insertZero P _).1 (by_contra fun h => hyj (hy _ h)) with h | hjP
    · exact hiχ (by rw [← neg_add_eq_zero.mp h])
    · exact hχ i hiP _ hjP (by abel)
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]

variable (A) in
/-- The constant and `χ`-th coefficients of elements supported on `{0} ∪ P`, as an algebra
map to the dual numbers, when `0 ∉ P`, `χ ≠ 0` and `χ` is not a sum of two elements of
`P`. -/
def dualCoeffHom (P : AddSubsemigroup (I → ℤ)) (h0 : (0 : I → ℤ) ∉ P) {χ : I → ℤ}
    (hχ0 : χ ≠ 0) (hχ : ∀ i ∈ P, ∀ j ∈ P, i + j ≠ χ) :
    supportedSubalgebra I A (insertZero P) →ₐ[R] DualNumber A where
  toFun s := TrivSqZeroExt.inl (((s : laurent I A) : AddMonoidAlgebra A (I → ℤ)).coeff 0) +
    TrivSqZeroExt.inr (((s : laurent I A) : AddMonoidAlgebra A (I → ℤ)).coeff χ)
  map_one' := by
    apply TrivSqZeroExt.ext
    · change ((1 : AddMonoidAlgebra A (I → ℤ)).coeff 0) + 0 = 1
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
        add_zero]
    · change 0 + (1 : AddMonoidAlgebra A (I → ℤ)).coeff χ = 0
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_of_ne hχ0, zero_add]
  map_mul' s t := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        TrivSqZeroExt.fst_mul]
      exact coeff_zero_mul_of_supported h0 s.2 t.2
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      rw [show ((s * t : supportedSubalgebra I A (insertZero P)) : laurent I A) =
        (s : laurent I A) * t from rfl]
      rw [coeff_mul_of_supported hχ0 hχ s.2 t.2]
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' s t := by
    apply TrivSqZeroExt.ext
    · change (((s : laurent I A) + t : AddMonoidAlgebra A (I → ℤ)).coeff 0) + 0 = _
      simp [AddMonoidAlgebra.coeff_add]
    · change 0 + (((s : laurent I A) + t : AddMonoidAlgebra A (I → ℤ)).coeff χ) = _
      simp [AddMonoidAlgebra.coeff_add]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · change (algebraMap R (AddMonoidAlgebra A (I → ℤ)) c).coeff 0 + 0 = _
      rw [coeff_algebraMap, ite_eq_left rfl, add_zero, TrivSqZeroExt.algebraMap_eq_inl']
      rfl
    · change 0 + (algebraMap R (AddMonoidAlgebra A (I → ℤ)) c).coeff χ = _
      rw [coeff_algebraMap, ite_eq_right hχ0, map_zero, zero_add, TrivSqZeroExt.algebraMap_eq_inl']
      rfl

omit [DecidableEq I] in
theorem dualCoeffHom_apply (P : AddSubsemigroup (I → ℤ)) (h0 : (0 : I → ℤ) ∉ P) {χ : I → ℤ}
    (hχ0 : χ ≠ 0) (hχ : ∀ i ∈ P, ∀ j ∈ P, i + j ≠ χ)
    (s : supportedSubalgebra I A (insertZero P)) :
    dualCoeffHom A P h0 hχ0 hχ s =
      TrivSqZeroExt.inl (((s : laurent I A) : AddMonoidAlgebra A (I → ℤ)).coeff 0) +
        TrivSqZeroExt.inr (((s : laurent I A) : AddMonoidAlgebra A (I → ℤ)).coeff χ) :=
  rfl

include e in
/-- Points over a subalgebra are determined by their images. -/
theorem map_subalgebraHom_injective (S : Subalgebra R A) :
    Function.Injective fun x : F.obj (CommAlgCat.of R S) => F.map (subalgebraHom S) x := by
  intro x y h
  apply coord_injective e
  apply AlgHom.ext
  intro f
  apply Subtype.val_injective
  have h' := congrArg (fun p => coord e p f) h
  simp only [coord_map] at h'
  exact h'

end Supported

section WeightSubgroup

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)
  (P : AddSubsemigroup (I → ℤ)) {A : CommAlgCat.{u} R}

/-- The twisted point of an element of `U_P`, as a point over the supported subalgebra. -/
def supportedPointFun (x : weightSubgroup e σ P A) :
    F.obj (CommAlgCat.of R (supportedSubalgebra I A (insertZero P))) :=
  ofCoord e ((coord e (hat σ x.1)).codRestrict _
    (coord_hat_mem_supportedSubalgebra e σ _ fun f _ hm =>
      coord_comp_eq_zero_of_mem_weightSubgroup e σ x.2 f hm))

theorem map_supportedPointFun (x : weightSubgroup e σ P A) :
    F.map (subalgebraHom (supportedSubalgebra I A (insertZero P))) (supportedPointFun e σ P x) =
      hat σ x.1 := by
  apply coord_injective e
  rw [coord_map, supportedPointFun, coord_ofCoord]
  exact AlgHom.val_comp_codRestrict _ _ _

/-- The twisted points of `U_P` over the supported subalgebra, as a homomorphism. -/
def supportedPoint : weightSubgroup e σ P A →*
    F.obj (CommAlgCat.of R (supportedSubalgebra I A (insertZero P))) where
  toFun := supportedPointFun e σ P
  map_one' := map_subalgebraHom_injective e _ (by
    change F.map _ (supportedPointFun e σ P 1) = F.map _ 1
    rw [map_supportedPointFun, map_one, OneMemClass.coe_one, map_one])
  map_mul' x y := map_subalgebraHom_injective e _ (by
    change F.map _ (supportedPointFun e σ P (x * y)) =
      F.map _ (supportedPointFun e σ P x * supportedPointFun e σ P y)
    rw [map_mul, map_supportedPointFun, map_supportedPointFun, map_supportedPointFun,
      Subgroup.coe_mul, map_mul])

theorem coord_supportedPoint (x : weightSubgroup e σ P A) (f : B) :
    ((coord e (supportedPoint e σ P x) f : laurent I A) : AddMonoidAlgebra A (I → ℤ)) =
      coord e (hat σ x.1) f := by
  change ((coord e (supportedPointFun e σ P x) f : laurent I A) :
    AddMonoidAlgebra A (I → ℤ)) = _
  rw [supportedPointFun, coord_ofCoord]
  rfl

/-- On `U_P`, the coordinates of weight components of weight `χ` are additive, when `0 ∉ P`,
`χ ≠ 0` and `χ` is not a sum of two elements of `P`. -/
theorem coord_mul_comp_of_notMem_add (h0 : (0 : I → ℤ) ∉ P) {χ : I → ℤ} (hχ0 : χ ≠ 0)
    (hχ : ∀ i ∈ P, ∀ j ∈ P, i + j ≠ χ) {x y : F.obj A} (hx : x ∈ weightSubgroup e σ P A)
    (hy : y ∈ weightSubgroup e σ P A) (f : B) :
    coord e (x * y) (comp e σ χ f) = coord e x (comp e σ χ f) + coord e y (comp e σ χ f) := by
  let D : CommAlgCat.of R (supportedSubalgebra I A (insertZero P)) ⟶
      CommAlgCat.of R (DualNumber A) := CommAlgCat.ofHom (dualCoeffHom A P h0 hχ0 hχ)
  let ζ : weightSubgroup e σ P A →* F.obj (CommAlgCat.of R (DualNumber A)) :=
    (F.map D).hom.comp (supportedPoint e σ P)
  have hζ : ∀ (z : weightSubgroup e σ P A) (g : B),
      coord e (ζ z) g = TrivSqZeroExt.inl (coord e z.1 (comp e σ 0 g)) +
        TrivSqZeroExt.inr (coord e z.1 (comp e σ χ g)) := by
    intro z g
    change coord e (F.map D (supportedPoint e σ P z)) g = _
    rw [coord_map]
    change dualCoeffHom A P h0 hχ0 hχ (coord e (supportedPoint e σ P z) g) = _
    rw [dualCoeffHom_apply, coord_supportedPoint, coord_hat_coeff, coord_hat_coeff]
  have hred : ∀ z : weightSubgroup e σ P A,
      F.map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)) (ζ z) = 1 := by
    intro z
    refine (eq_one_iff e).2 fun g => ?_
    rw [coord_map, AlgHom.comp_apply, hζ]
    change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : DualNumber A).fst = _
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      (mem_weightSubgroup e σ P z.1).1 z.2 g 0 h0, counit_comp, ite_eq_left rfl]
  have key := snd_coord_mul e (hred ⟨x, hx⟩) (hred ⟨y, hy⟩) f
  rw [← map_mul] at key
  have hsnd : ∀ z : weightSubgroup e σ P A,
      (coord e (ζ z) f).snd = coord e z.1 (comp e σ χ f) := by
    intro z
    rw [hζ, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  rw [hsnd, hsnd, hsnd] at key
  exact key

end WeightSubgroup

section Cyclic

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)
  {a : I → ℤ} {r : ℕ} {A : CommAlgCat.{u} R}

omit [Fintype I] [DecidableEq I] in
theorem nsmul_ne_zero_of_pos (ha : a ≠ 0) (hr : 0 < r) : r • a ≠ 0 := by
  intro h
  have h' : r • a = (0 : ℕ) • a := by rw [h, zero_nsmul]
  exact hr.ne' (nsmul_left_injective_of_ne_zero ha h')

omit [Fintype I] [DecidableEq I] in
theorem add_ne_nsmul_of_mem_cyclicTail (ha : a ≠ 0) (hr : 0 < r) :
    ∀ i ∈ cyclicTail a r, ∀ j ∈ cyclicTail a r, i + j ≠ r • a := by
  rintro _ ⟨n, hn, -, rfl⟩ _ ⟨m, hm, -, rfl⟩ h
  rw [← add_nsmul] at h
  have := nsmul_left_injective_of_ne_zero ha h
  omega

/-- On the `r`-th cyclic weight subgroup, the coordinates of weight components of weight
`r • a` are additive. -/
theorem coord_mul_comp_nsmul (ha : a ≠ 0) (hr : 0 < r) {x y : F.obj A} (hx : x ∈ weightSubgroup e σ (cyclicTail a r) A)
    (hy : y ∈ weightSubgroup e σ (cyclicTail a r) A) (f : B) :
    coord e (x * y) (comp e σ (r • a) f) =
      coord e x (comp e σ (r • a) f) + coord e y (comp e σ (r • a) f) :=
  coord_mul_comp_of_notMem_add e σ _ (zero_notMem_cyclicTail ha r) (nsmul_ne_zero_of_pos ha hr)
    (add_ne_nsmul_of_mem_cyclicTail ha hr) hx hy f

/-- An element of the `r`-th cyclic weight subgroup lies in the next one exactly when its
coordinates of weight `r • a` components vanish. -/
theorem mem_weightSubgroup_succ_iff (ha : a ≠ 0) (hr : 0 < r) {x : F.obj A}
    (hx : x ∈ weightSubgroup e σ (cyclicTail a r) A) :
    x ∈ weightSubgroup e σ (cyclicTail a (r + 1)) A ↔
      ∀ f, coord e x (comp e σ (r • a) f) = 0 := by
  have hra : r • a ≠ 0 := nsmul_ne_zero_of_pos ha hr
  constructor
  · intro h f
    have hnot : r • a ∉ cyclicTail a (r + 1) := by
      rintro ⟨n, hn, -, hna⟩
      have := nsmul_left_injective_of_ne_zero ha hna
      omega
    rw [(mem_weightSubgroup e σ _ x).1 h f _ hnot, counit_comp, ite_eq_right hra, map_zero]
  · intro h
    refine (mem_weightSubgroup e σ _ x).2 fun f m hm => ?_
    by_cases hmr : m ∈ cyclicTail a r
    · obtain ⟨n, hn, hn0, rfl⟩ := hmr
      have hnr : n = r := by
        by_contra hne
        exact hm ⟨n, by omega, hn0, rfl⟩
      subst hnr
      rw [h f, counit_comp, ite_eq_right hra, map_zero]
    · exact (mem_weightSubgroup e σ _ x).1 hx f m hmr

end Cyclic

section Coordinates

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- A homogeneous element of the coordinate algebra of `U_P` is the image of a weight
component. -/
theorem exists_eq_mk_comp (P : AddSubsemigroup (I → ℤ)) {m : I → ℤ}
    {g : B ⧸ weightIdeal e σ P}
    (hg : IsHomogeneous (weightCorep e σ P) (weightAction e σ P) m g) :
    ∃ f : B, Ideal.Quotient.mk _ (comp e σ m f) = g := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  exact ⟨f, by
    rw [← comp_restrict (isCutOutBy_weightIdeal e σ P)
      (fun t _ hx => act_mem_weightSubgroup e σ P t hx), hg.comp_self]⟩

/-- The coordinate algebra of the `r`-th cyclic weight subgroup is a polynomial algebra in
primitive coordinates `y` of weight `r • a` and further coordinates `z`; the coordinates `y`
cut out the next cyclic weight subgroup. -/
theorem exists_primitive_coordinates [Algebra.FormallySmooth k B] [Algebra.FiniteType k B]
    {a : I → ℤ} (ha : a ≠ 0) {r : ℕ} (hr : 0 < r) :
    ∃ (N : ℕ) (y : Fin N → B ⧸ weightIdeal e σ (cyclicTail a r)) (ι : Type) (_ : Finite ι)
      (z : ι → B ⧸ weightIdeal e σ (cyclicTail a r)),
      (∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a r))
        (weightAction e σ (cyclicTail a r)) (r • a) (y i)) ∧
      (∀ {A : CommAlgCat.{u} (CommRingCat.of k)}
        (x x' : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a r))).obj A) (i : Fin N),
        coord (weightCorep e σ (cyclicTail a r)) (x * x') (y i) =
          coord (weightCorep e σ (cyclicTail a r)) x (y i) +
            coord (weightCorep e σ (cyclicTail a r)) x' (y i)) ∧
      (∀ {A : CommAlgCat.{u} (CommRingCat.of k)}
        (x : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a r))).obj A),
        (∀ i, coord (weightCorep e σ (cyclicTail a r)) x (y i) = 0) ↔
          x.1 ∈ weightSubgroup e σ (cyclicTail a (r + 1)) A) ∧
      Function.Bijective (MvPolynomial.aeval (Sum.elim y z) :
        MvPolynomial (Fin N ⊕ ι) k →ₐ[k] B ⧸ weightIdeal e σ (cyclicTail a r)) := by
  classical
  set P := cyclicTail a r with hP
  obtain ⟨n, d, x, hd, hdr, hx, hbij⟩ := exists_aeval_bijective_cyclicTail e σ ha r
  let s := {i : Fin n // d i = r}
  let eN : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let ι := {i : Fin n // ¬ d i = r}
  let E : Fin (Fintype.card s) ⊕ ι ≃ Fin n :=
    (Equiv.sumCongr eN.symm (Equiv.refl ι)).trans (Equiv.sumCompl fun i => d i = r)
  let y : Fin (Fintype.card s) → B ⧸ weightIdeal e σ P := fun j => x (eN.symm j).1
  let z : ι → B ⧸ weightIdeal e σ P := fun i => x i.1
  have hyz : Sum.elim y z = x ∘ E := by
    funext j
    rcases j with j | j <;> rfl
  have hy : ∀ j, IsHomogeneous (weightCorep e σ P) (weightAction e σ P) (r • a) (y j) := by
    intro j
    have h := hx (eN.symm j).1
    rwa [(eN.symm j).2] at h
  -- Linear span of the primitive coordinates.
  have hspan : ∀ {g : B ⧸ weightIdeal e σ P},
      IsHomogeneous (weightCorep e σ P) (weightAction e σ P) (r • a) g →
        g ∈ Submodule.span k (Set.range y) := by
    intro g hg
    have hφ : Function.Injective (multiplesHom (I → ℤ) a) := nsmul_left_injective_of_ne_zero ha
    have hsupp : ∀ (g : B ⧸ weightIdeal e σ P) m,
        comp (weightCorep e σ P) (weightAction e σ P) m g ≠ 0 →
          m ∈ Set.range (multiplesHom (I → ℤ) a) := by
      intro g m hg
      rcases (mem_insertZero P m).1 (mem_insertZero_of_comp_weightAction_ne_zero e σ P g hg) with
        rfl | ⟨n, -, -, rfl⟩
      · exact ⟨0, zero_nsmul a⟩
      · exact ⟨n, rfl⟩
    let _ := gradedAlgebra (weightCorep e σ P) (weightAction e σ P) hφ hsupp
    have h := mem_span_of_mem_graded (k := k)
      (fun i => homogeneousSubmodule (weightCorep e σ P) (weightAction e σ P)
        (multiplesHom (I → ℤ) a i)) (x := x) (d := d) hx hbij.2 hr hdr (g := g) hg
    refine Submodule.span_mono ?_ h
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨eN ⟨i, hi⟩, by simp [y]⟩
  refine ⟨Fintype.card s, y, ι, inferInstance, z, hy, ?_, ?_, ?_⟩
  · intro A u u' j
    obtain ⟨f, hf⟩ := exists_eq_mk_comp e σ P (hy j)
    rw [← hf, coord_cut_mk, coord_cut_mk, coord_cut_mk]
    exact coord_mul_comp_nsmul e σ ha hr u.2 u'.2 f
  · intro A u
    rw [mem_weightSubgroup_succ_iff e σ ha hr u.2]
    constructor
    · intro h f
      have hmem := hspan (isHomogeneous_comp (weightCorep e σ P) (weightAction e σ P) (r • a)
        (Ideal.Quotient.mk _ f))
      rw [comp_restrict] at hmem
      rw [← coord_cut_mk (isCutOutBy_weightIdeal e σ P) u]
      refine Submodule.span_induction (p := fun g _ =>
        coord (weightCorep e σ P) u g = 0) ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨i, rfl⟩
        exact h i
      · exact map_zero _
      · intro g g' _ _ hg hg'
        rw [map_add, hg, hg', add_zero]
      · intro c g _ hg
        rw [map_smul, hg, smul_zero]
    · intro h j
      obtain ⟨f, hf⟩ := exists_eq_mk_comp e σ P (hy j)
      rw [← hf, coord_cut_mk]
      exact h f
  · rw [hyz]
    have : (MvPolynomial.aeval (x ∘ E) : MvPolynomial (Fin (Fintype.card s) ⊕ ι) k →ₐ[k] _) =
        (MvPolynomial.aeval x).comp (MvPolynomial.renameEquiv k E).toAlgHom := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [MvPolynomial.renameEquiv]
    rw [this, AlgHom.coe_comp]
    exact hbij.comp (MvPolynomial.renameEquiv k E).bijective

end Coordinates

end Langlands.GroupScheme.Corepresented
