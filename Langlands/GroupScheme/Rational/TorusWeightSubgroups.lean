import Langlands.GroupScheme.Rational.TorusGrading
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Weight subgroups of corepresented groups with split-torus actions -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A point is the identity exactly when its coordinates are the augmentation. -/
theorem eq_one_iff {A : CommAlgCat.{u} R} {x : F.obj A} :
    x = 1 ↔ ∀ f, coord e x f = algebraMap R A (AffineLinearEmbedding.counit e f) := by
  constructor
  · rintro rfl f
    rw [coord_one]
    rfl
  · intro h
    apply coord_injective e
    rw [coord_one]
    exact AlgHom.ext h

section KernelSubgroup

variable {A : CommAlgCat.{u} R} (S : Subalgebra R A) (J : Ideal S)

/-- The inclusion of a subalgebra, as a morphism of algebras. -/
abbrev subalgebraHom : CommAlgCat.of R S ⟶ A := CommAlgCat.ofHom S.val

/-- The quotient map of an ideal of a subalgebra, as a morphism of algebras. -/
abbrev subalgebraQuotientHom : CommAlgCat.of R S ⟶ CommAlgCat.of R (S ⧸ J) :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)

variable (F) in
/-- The points with coordinates in a subalgebra which are trivial modulo an ideal of it. -/
def kerSubgroup : Subgroup (F.obj A) :=
  (F.map (subalgebraQuotientHom S J)).hom.ker.map (F.map (subalgebraHom S)).hom

/-- A point whose coordinates factor through a subalgebra comes from that subalgebra. -/
theorem eq_map_ofCoord {y : F.obj A} {g : B →ₐ[R] S} (hg : S.val.comp g = coord e y) :
    y = F.map (subalgebraHom S) (ofCoord e g) := by
  apply coord_injective e
  rw [coord_map, coord_ofCoord]
  exact hg.symm

theorem mem_kerSubgroup {y : F.obj A} :
    y ∈ kerSubgroup F S J ↔ ∃ g : B →ₐ[R] S, S.val.comp g = coord e y ∧
      ∀ f, g f - algebraMap R S (AffineLinearEmbedding.counit e f) ∈ J := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨coord e y', (coord_map e (subalgebraHom S) y').symm, fun f => ?_⟩
    have h := (eq_one_iff e).1 (MonoidHom.mem_ker.mp hy') f
    rw [coord_map] at h
    change Ideal.Quotient.mk J (coord e y' f) = _ at h
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq] at h
    exact h
  · rintro ⟨g, hg, hJ⟩
    refine ⟨ofCoord e g, MonoidHom.mem_ker.mpr ((eq_one_iff e).2 fun f => ?_),
      (eq_map_ofCoord e S hg).symm⟩
    rw [coord_map, coord_ofCoord]
    change Ideal.Quotient.mk J (g f) = _
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
    exact hJ f

theorem kerSubgroup_le_range : kerSubgroup F S J ≤ (F.map (subalgebraHom S)).hom.range :=
  Subgroup.map_le_range _ _

/-- The kernel subgroup is normalized by the points with coordinates in the subalgebra. -/
theorem conj_mem_kerSubgroup {z y : F.obj A} (hz : z ∈ (F.map (subalgebraHom S)).hom.range)
    (hy : y ∈ kerSubgroup F S J) : z * y * z⁻¹ ∈ kerSubgroup F S J := by
  obtain ⟨z', rfl⟩ := hz
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨z' * y' * z'⁻¹, (MonoidHom.normal_ker _).conj_mem y' hy' z', by
    rw [map_mul, map_mul, map_inv]⟩

/-- Two points with coordinates in the subalgebra which agree modulo the ideal differ by an
element of the kernel subgroup. -/
theorem inv_mul_mem_kerSubgroup {y y' : F.obj A} {g g' : B →ₐ[R] S}
    (hg : S.val.comp g = coord e y) (hg' : S.val.comp g' = coord e y')
    (h : ∀ f, g f - g' f ∈ J) : y⁻¹ * y' ∈ kerSubgroup F S J := by
  rw [eq_map_ofCoord e S hg, eq_map_ofCoord e S hg']
  refine ⟨(ofCoord e g)⁻¹ * ofCoord e g', MonoidHom.mem_ker.mpr ?_, by
    rw [map_mul, map_inv]⟩
  rw [map_mul, map_inv, inv_mul_eq_one]
  apply coord_injective e
  rw [coord_map, coord_map, coord_ofCoord, coord_ofCoord]
  apply AlgHom.ext
  intro f
  change Ideal.Quotient.mk J (g f) = Ideal.Quotient.mk J (g' f)
  rw [Ideal.Quotient.eq]
  exact h f

end KernelSubgroup

section Supported

/-- A coefficient of a product vanishes if no pair of nonzero coefficients contributes. -/
theorem coeff_mul_eq_zero_of {Λ A : Type*} [AddCommMonoid Λ] [CommSemiring A]
    {s t : AddMonoidAlgebra A Λ} {m : Λ}
    (h : ∀ i j, i + j = m → s.coeff i ≠ 0 → t.coeff j ≠ 0 → False) : (s * t).coeff m = 0 := by
  classical
  by_contra hm
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset s t (Finsupp.mem_support_iff.mpr hm))
  exact h i j hij (Finsupp.mem_support_iff.mp hi) (Finsupp.mem_support_iff.mp hj)

variable (I : Type u) (A : CommAlgCat.{u} R)

/-- The subalgebra of the group algebra of elements supported on a submonoid. -/
def supportedSubalgebra (M : AddSubmonoid (I → ℤ)) : Subalgebra R (laurent I A) where
  carrier := {s | ∀ m ∉ M, (s : AddMonoidAlgebra A (I → ℤ)).coeff m = 0}
  mul_mem' {s t} hs ht m hm := coeff_mul_eq_zero_of fun i j hij hi hj =>
    hm (hij ▸ M.add_mem (by_contra fun h => hi (hs i h)) (by_contra fun h => hj (ht j h)))
  add_mem' {s t} hs ht m hm := by
    change (s + t : AddMonoidAlgebra A (I → ℤ)).coeff m = 0
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hs m hm, ht m hm, add_zero]
  algebraMap_mem' r m hm := by
    change (algebraMap R (AddMonoidAlgebra A (I → ℤ)) r).coeff m = 0
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single]
    exact Finsupp.single_eq_of_ne fun h => hm (by rw [h]; exact M.zero_mem)

theorem mem_supportedSubalgebra (M : AddSubmonoid (I → ℤ)) (s : laurent I A) :
    s ∈ supportedSubalgebra I A M ↔ ∀ m ∉ M, (s : AddMonoidAlgebra A (I → ℤ)).coeff m = 0 :=
  Iff.rfl

/-- The ideal of elements supported on a subset absorbing the submonoid. -/
def supportedIdeal (M : AddSubmonoid (I → ℤ)) (P : Set (I → ℤ))
    (hP : ∀ m ∈ M, ∀ p ∈ P, m + p ∈ P) : Ideal (supportedSubalgebra I A M) where
  carrier := {s | ∀ m ∉ P, ((s : laurent I A) : AddMonoidAlgebra A (I → ℤ)).coeff m = 0}
  add_mem' {s t} hs ht m hm := by
    change ((s : laurent I A) + t : AddMonoidAlgebra A (I → ℤ)).coeff m = 0
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hs m hm, ht m hm, add_zero]
  zero_mem' m _ := rfl
  smul_mem' c s hs m hm := by
    change ((c : laurent I A) * s : AddMonoidAlgebra A (I → ℤ)).coeff m = 0
    exact coeff_mul_eq_zero_of fun i j hij hi hj =>
      hm (hij ▸ hP i (by_contra fun h => hi (c.2 i h)) j (by_contra fun h => hj (hs j h)))

theorem mem_supportedIdeal (M : AddSubmonoid (I → ℤ)) (P : Set (I → ℤ))
    (hP : ∀ m ∈ M, ∀ p ∈ P, m + p ∈ P) (s : supportedSubalgebra I A M) :
    s ∈ supportedIdeal I A M P hP ↔
      ∀ m ∉ P, ((s : laurent I A) : AddMonoidAlgebra A (I → ℤ)).coeff m = 0 :=
  Iff.rfl

variable [Fintype I] in
theorem coeff_algebraMap (c : R) (m : I → ℤ) :
    (algebraMap R (AddMonoidAlgebra A (I → ℤ)) c).coeff m =
      algebraMap R A (if m = 0 then c else 0) := by
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single]
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [Finsupp.single_eq_of_ne hm]
    simp [hm]

end Supported

/-- A semigroup together with zero, as a submonoid. -/
def insertZero {Λ : Type*} [AddMonoid Λ] (P : AddSubsemigroup Λ) : AddSubmonoid Λ where
  carrier := insert 0 (P : Set Λ)
  add_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact Or.inl (add_zero 0)
    · rw [zero_add]
      exact Or.inr hb
    · rw [add_zero]
      exact Or.inr ha
    · exact Or.inr (P.add_mem ha hb)
  zero_mem' := Set.mem_insert _ _

theorem mem_insertZero {Λ : Type*} [AddMonoid Λ] (P : AddSubsemigroup Λ) (m : Λ) :
    m ∈ insertZero P ↔ m = 0 ∨ m ∈ P :=
  Iff.rfl

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

section WeightSubgroup

theorem coeff_coord_hat_sub {A : CommAlgCat.{u} R} (x : F.obj A) (f : B) (m : I → ℤ) :
    (coord e (hat σ x) f - algebraMap R (laurent I A) (AffineLinearEmbedding.counit e f)).coeff m =
      coord e x (comp e σ m f) - algebraMap R A (AffineLinearEmbedding.counit e (comp e σ m f)) := by
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coord_hat_coeff]
  erw [coeff_algebraMap I A (AffineLinearEmbedding.counit e f) m]
  rw [counit_comp]

/-- The weight condition outside `P` is membership of the twisted point in the kernel
subgroup of the supported subalgebra. -/
theorem weightCondition_iff (P : Set (I → ℤ)) (M : AddSubmonoid (I → ℤ)) (hPM : P ⊆ M)
    (hP : ∀ m ∈ M, ∀ p ∈ P, m + p ∈ P) {A : CommAlgCat.{u} R} (x : F.obj A) :
    (∀ f m, m ∉ P → coord e x (comp e σ m f) = algebraMap R A (AffineLinearEmbedding.counit e (comp e σ m f))) ↔
      hat σ x ∈ kerSubgroup F (supportedSubalgebra I A M) (supportedIdeal I A M P hP) := by
  rw [mem_kerSubgroup e]
  constructor
  · intro h
    have hS : ∀ f, coord e (hat σ x) f ∈ supportedSubalgebra I A M := by
      intro f m hm
      have hm0 : m ≠ 0 := fun h' => hm (by rw [h']; exact M.zero_mem)
      rw [coord_hat_coeff, h f m fun h' => hm (hPM h'), counit_comp]
      simp [hm0]
    refine ⟨(coord e (hat σ x)).codRestrict _ hS, AlgHom.val_comp_codRestrict _ _ _,
      fun f m hm => ?_⟩
    change (coord e (hat σ x) f - algebraMap R (laurent I A) (AffineLinearEmbedding.counit e f)).coeff m = 0
    rw [coeff_coord_hat_sub, h f m hm, sub_self]
  · rintro ⟨g, hg, hJ⟩ f m hm
    have h1 := hJ f m hm
    have h2 : ((g f : laurent I A) : AddMonoidAlgebra A (I → ℤ)) = coord e (hat σ x) f :=
      AlgHom.congr_fun hg f
    change ((g f : laurent I A) - algebraMap R (laurent I A) (AffineLinearEmbedding.counit e f)).coeff m = 0 at h1
    rw [h2, coeff_coord_hat_sub, sub_eq_zero] at h1
    exact h1

/-- The points whose weight components outside `P` agree with those of the identity,
using an auxiliary submonoid for the subgroup structure. -/
def weightSubgroupOf (P : Set (I → ℤ)) (M : AddSubmonoid (I → ℤ)) (hPM : P ⊆ M)
    (hP : ∀ m ∈ M, ∀ p ∈ P, m + p ∈ P) (A : CommAlgCat.{u} R) : Subgroup (F.obj A) :=
  ((kerSubgroup F (supportedSubalgebra I A M) (supportedIdeal I A M P hP)).comap
      (hat σ)).copy
    {x | ∀ f m, m ∉ P → coord e x (comp e σ m f) = algebraMap R A (AffineLinearEmbedding.counit e (comp e σ m f))}
    (Set.ext fun x => weightCondition_iff e σ P M hPM hP x)

omit [Fintype I] [DecidableEq I] in
theorem insertZero_add_mem (P : AddSubsemigroup (I → ℤ)) :
    ∀ m ∈ insertZero P, ∀ p ∈ (P : Set (I → ℤ)), m + p ∈ (P : Set (I → ℤ)) := by
  rintro m (rfl | hm) p hp
  · rwa [zero_add]
  · exact P.add_mem hm hp

/-- The points whose weight components outside the semigroup `P` agree with those of the
identity. -/
def weightSubgroup (P : AddSubsemigroup (I → ℤ)) (A : CommAlgCat.{u} R) : Subgroup (F.obj A) :=
  weightSubgroupOf e σ P (insertZero P) (Set.subset_insert _ _) (insertZero_add_mem P) A

theorem mem_weightSubgroup (P : AddSubsemigroup (I → ℤ)) {A : CommAlgCat.{u} R} (x : F.obj A) :
    x ∈ weightSubgroup e σ P A ↔
      ∀ f m, m ∉ P → coord e x (comp e σ m f) = algebraMap R A (AffineLinearEmbedding.counit e (comp e σ m f)) :=
  Iff.rfl

theorem weightSubgroup_eq (P : AddSubsemigroup (I → ℤ)) (M : AddSubmonoid (I → ℤ))
    (hPM : (P : Set (I → ℤ)) ⊆ M) (hP : ∀ m ∈ M, ∀ p ∈ (P : Set (I → ℤ)), m + p ∈ P)
    (A : CommAlgCat.{u} R) : weightSubgroup e σ P A = weightSubgroupOf e σ P M hPM hP A :=
  Subgroup.ext fun _ => Iff.rfl

theorem hat_mem_kerSubgroup (P : Set (I → ℤ)) (M : AddSubmonoid (I → ℤ)) (hPM : P ⊆ M)
    (hP : ∀ m ∈ M, ∀ p ∈ P, m + p ∈ P) {A : CommAlgCat.{u} R} {x : F.obj A}
    (hx : x ∈ weightSubgroupOf e σ P M hPM hP A) :
    hat σ x ∈ kerSubgroup F (supportedSubalgebra I A M) (supportedIdeal I A M P hP) :=
  (weightCondition_iff e σ P M hPM hP x).1 hx

/-- A smaller weight subgroup whose semigroup absorbs the larger one is normalized by it. -/
theorem conj_mem_weightSubgroup {P P' : AddSubsemigroup (I → ℤ)}
    (hP'P : (P' : Set (I → ℤ)) ⊆ P) (hPP' : ∀ m ∈ P, ∀ p ∈ P', m + p ∈ P')
    {A : CommAlgCat.{u} R} {x y : F.obj A} (hx : x ∈ weightSubgroup e σ P A)
    (hy : y ∈ weightSubgroup e σ P' A) : x * y * x⁻¹ ∈ weightSubgroup e σ P' A := by
  have hP' : ∀ m ∈ insertZero P, ∀ p ∈ (P' : Set (I → ℤ)), m + p ∈ (P' : Set (I → ℤ)) := by
    rintro m (rfl | hm) p hp
    · rwa [zero_add]
    · exact hPP' m hm p hp
  have hPM' : (P' : Set (I → ℤ)) ⊆ insertZero P := hP'P.trans (Set.subset_insert _ _)
  rw [weightSubgroup_eq e σ P' (insertZero P) hPM' hP'] at hy ⊢
  have hx' := hat_mem_kerSubgroup e σ (P : Set (I → ℤ)) (insertZero P) (Set.subset_insert _ _)
    (insertZero_add_mem P) hx
  have hy' := hat_mem_kerSubgroup e σ _ _ hPM' hP' hy
  refine (weightCondition_iff e σ _ _ hPM' hP' _).2 ?_
  rw [map_mul, map_mul, map_inv]
  exact conj_mem_kerSubgroup _ _ (kerSubgroup_le_range _ _ hx') hy'

/-- Weight subgroups are preserved by algebra maps. -/
theorem map_mem_weightSubgroup (P : AddSubsemigroup (I → ℤ)) {A A' : CommAlgCat.{u} R}
    (g : A ⟶ A') {x : F.obj A} (hx : x ∈ weightSubgroup e σ P A) :
    F.map g x ∈ weightSubgroup e σ P A' := by
  intro f m hm
  rw [coord_map, AlgHom.comp_apply, hx f m hm, AlgHom.commutes]

/-- Weight subgroups are stable under the torus. -/
theorem act_mem_weightSubgroup (P : AddSubsemigroup (I → ℤ)) {A : CommAlgCat.{u} R}
    (t : I → Aˣ) {x : F.obj A} (hx : x ∈ weightSubgroup e σ P A) :
    σ.act t x ∈ weightSubgroup e σ P A := by
  intro f m hm
  rw [coord_act_of_isHomogeneous e σ t x (isHomogeneous_comp e σ m f), hx f m hm, counit_comp]
  by_cases h0 : m = 0
  · subst h0
    simp
  · simp [h0]

/-- The ideal generated by the differences between the weight components outside `P`
and their augmentations. -/
def weightIdeal (P : Set (I → ℤ)) : Ideal B :=
  Ideal.span {b | ∃ f m, m ∉ P ∧ comp e σ m f - algebraMap R B (AffineLinearEmbedding.counit e (comp e σ m f)) = b}

theorem isCutOutBy_weightIdeal (P : AddSubsemigroup (I → ℤ)) :
    IsCutOutBy e (weightSubgroup e σ P) (weightIdeal e σ P) := by
  intro A x
  rw [mem_weightSubgroup]
  change _ ↔ ∀ b ∈ weightIdeal e σ P, coord e x b = 0
  have key : (∀ b ∈ weightIdeal e σ P, coord e x b = 0) ↔
      weightIdeal e σ P ≤ RingHom.ker (coord e x) :=
    ⟨fun h b hb => RingHom.mem_ker.mpr (h b hb), fun h b hb => RingHom.mem_ker.mp (h hb)⟩
  rw [key, weightIdeal, Ideal.span_le]
  constructor
  · rintro h b ⟨f, m, hm, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, AlgHom.commutes, h f m hm, sub_self]
  · intro h f m hm
    have h1 := h ⟨f, m, hm, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    exact h1

end WeightSubgroup

section Restrict

variable {e σ} {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {J : Ideal B}
  (hJ : IsCutOutBy e H J)

/-- The restriction of a torus action to a stable subgroup cut out by an ideal. -/
def TorusAction.restrict
    (hH : ∀ {A : CommAlgCat.{u} R} (t : I → Aˣ) {x : F.obj A}, x ∈ H A → σ.act t x ∈ H A) :
    TorusAction (cutFunctor hJ) I where
  act t x := ⟨σ.act t x.1, hH t x.2⟩
  act_one x := Subtype.ext (σ.act_one x.1)
  act_mul t t' x := Subtype.ext (σ.act_mul t t' x.1)
  act_map_mul t x y := Subtype.ext (σ.act_map_mul t x.1 y.1)
  naturality g t x := Subtype.ext (σ.naturality g t x.1)

variable (hH : ∀ {A : CommAlgCat.{u} R} (t : I → Aˣ) {x : F.obj A}, x ∈ H A → σ.act t x ∈ H A)

theorem coord_cut_mk {A : CommAlgCat.{u} R} (y : (cutFunctor hJ).obj A) (f : B) :
    coord (cutCorepresentableBy hJ) y (Ideal.Quotient.mk J f) = coord e y.1 f :=
  rfl

theorem univ_cut : (univ (cutCorepresentableBy hJ)).1 = ofCoord e (Ideal.Quotient.mkₐ R J) := by
  change e.homEquiv (quotientMap J ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

/-- The coaction on the quotient is the coaction on the representing algebra followed by the
quotient map. -/
theorem rho_restrict (f : B) :
    rho (cutCorepresentableBy hJ) (σ.restrict hJ hH) (Ideal.Quotient.mk J f) =
      AddMonoidAlgebra.mapAlgHom (I → ℤ) (Ideal.Quotient.mkₐ R J) (rho e σ f) := by
  rw [rho, coord_cut_mk]
  change coord e (hat σ (univ (cutCorepresentableBy hJ)).1) f = _
  rw [univ_cut, coord_hat, coord_ofCoord]
  rfl

theorem comp_restrict (m : I → ℤ) (f : B) :
    comp (cutCorepresentableBy hJ) (σ.restrict hJ hH) m (Ideal.Quotient.mk J f) =
      Ideal.Quotient.mk J (comp e σ m f) := by
  rw [comp_apply, rho_restrict, AddMonoidAlgebra.coeff_mapAlgHom, comp_apply]
  rfl

theorem counit_cut_mk (f : B) :
    AffineLinearEmbedding.counit (cutCorepresentableBy hJ) (Ideal.Quotient.mk J f) = AffineLinearEmbedding.counit e f :=
  rfl

end Restrict

end Langlands.GroupScheme.Corepresented
