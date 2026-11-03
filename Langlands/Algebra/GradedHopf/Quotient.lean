import Langlands.Algebra.GradedHopf.Basic
import Mathlib.RingTheory.Bialgebra.Quotient

/-! # Graded quotients by homogeneous ideals -/

noncomputable section

open DirectSum TensorProduct

namespace Langlands.Algebra.GradedHopf

variable {ι ι' k A : Type*} [DecidableEq ι] [DecidableEq ι'] [AddCommMonoid ι] [AddCommMonoid ι']
  [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ι → Submodule k A) [GradedAlgebra 𝒜]
  (J : Ideal A) (e : ι' →+ ι)

/-- The family of submodules of `A ⧸ J` indexed by `ι'` whose member of index `i'` is the image
of `𝒜 (e i')`. -/
def quotGrade (i' : ι') : Submodule k (A ⧸ J) :=
  (𝒜 (e i')).map (Ideal.Quotient.mkₐ k J).toLinearMap

variable {𝒜 J e}

omit [DecidableEq ι] [DecidableEq ι'] [GradedAlgebra 𝒜] in
theorem mk_mem_quotGrade {i' : ι'} {a : A} (ha : a ∈ 𝒜 (e i')) :
    Ideal.Quotient.mk J a ∈ quotGrade 𝒜 J e i' :=
  Submodule.mem_map_of_mem ha

omit [DecidableEq ι] [DecidableEq ι'] [GradedAlgebra 𝒜] in
theorem exists_of_mem_quotGrade {i' : ι'} {x : A ⧸ J} (hx : x ∈ quotGrade 𝒜 J e i') :
    ∃ a ∈ 𝒜 (e i'), Ideal.Quotient.mk J a = x := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, rfl⟩

variable (𝒜 J e)

instance quotGrade_gradedMonoid : SetLike.GradedMonoid (quotGrade 𝒜 J e) where
  one_mem := by
    rw [← map_one (Ideal.Quotient.mk J)]
    exact mk_mem_quotGrade (by rw [map_zero]; exact SetLike.GradedOne.one_mem)
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotGrade hx
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_quotGrade hy
    rw [← map_mul]
    exact mk_mem_quotGrade (by rw [map_add]; exact SetLike.GradedMul.mul_mem ha hb)

variable {𝒜 J e}

/-- `DFinsupp.comapDomain` along an injective map, as a linear map of direct sums. -/
def comapDomainLinear (he : Function.Injective e) :
    (⨁ i, 𝒜 i) →ₗ[k] ⨁ i', 𝒜 (e i') where
  toFun f := DFinsupp.comapDomain e he f
  map_add' f g := DFinsupp.comapDomain_add e he f g
  map_smul' c f := DFinsupp.comapDomain_smul e he c f

/-- The linear map `A → ⨁ i', quotGrade 𝒜 J e i'` whose component of index `i'` is the image in
`A ⧸ J` of the component of degree `e i'`. -/
def quotDecomposeAux (he : Function.Injective e) : A →ₗ[k] ⨁ i', quotGrade 𝒜 J e i' :=
  DFinsupp.mapRange.linearMap
      (fun i' => (Ideal.Quotient.mkₐ k J).toLinearMap.submoduleMap (𝒜 (e i'))) ∘ₗ
    comapDomainLinear he ∘ₗ (decomposeLinearEquiv 𝒜).toLinearMap

omit [DecidableEq ι'] in
theorem quotDecomposeAux_apply (he : Function.Injective e) (a : A) (i' : ι') :
    (quotDecomposeAux (𝒜 := 𝒜) (J := J) he a i' : A ⧸ J) =
      Ideal.Quotient.mk J (decompose 𝒜 a (e i')) :=
  rfl

theorem quotDecomposeAux_of_mem (he : Function.Injective e) {i' : ι'} {a : A}
    (ha : a ∈ 𝒜 (e i')) :
    quotDecomposeAux (𝒜 := 𝒜) (J := J) he a = DirectSum.of (fun j' => quotGrade 𝒜 J e j') i'
      ⟨Ideal.Quotient.mk J a, mk_mem_quotGrade ha⟩ := by
  ext j'
  rw [quotDecomposeAux_apply]
  by_cases h : j' = i'
  · subst h
    rw [decompose_of_mem_same 𝒜 ha, DirectSum.of_eq_same]
  · rw [decompose_of_mem_ne 𝒜 ha (fun h' => h (he h').symm), DirectSum.of_eq_of_ne _ _ _ h,
      map_zero, ZeroMemClass.coe_zero]

theorem quotDecomposeAux_of_not_mem (he : Function.Injective e) {i : ι}
    (hi : i ∉ Set.range e) {a : A} (ha : a ∈ 𝒜 i) : quotDecomposeAux (𝒜 := 𝒜) (J := J) he a = 0 := by
  ext j'
  rw [quotDecomposeAux_apply, decompose_of_mem_ne 𝒜 ha (fun h => hi ⟨j', h.symm⟩), map_zero]
  rfl

theorem quotDecomposeAux_eq_zero (hJ : J.IsHomogeneous 𝒜) (he : Function.Injective e) {a : A}
    (ha : a ∈ J) : quotDecomposeAux (𝒜 := 𝒜) (J := J) he a = 0 := by
  ext j'
  rw [quotDecomposeAux_apply, Ideal.Quotient.eq_zero_iff_mem.2 (hJ (e j') ha)]
  rfl

/-- The decomposition map of the graded quotient. -/
def quotDecompose (hJ : J.IsHomogeneous 𝒜) (he : Function.Injective e) :
    A ⧸ J →ₗ[k] ⨁ i', quotGrade 𝒜 J e i' :=
  Submodule.liftQ (R₂ := k) (M₂ := ⨁ i', quotGrade 𝒜 J e i') (τ₁₂ := RingHom.id k)
      (J.restrictScalars k) (quotDecomposeAux (𝒜 := 𝒜) (J := J) he)
      (fun _ ha => LinearMap.mem_ker.2 (quotDecomposeAux_eq_zero hJ he ha)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k J).symm.toLinearMap

theorem quotDecompose_mk (hJ : J.IsHomogeneous 𝒜) (he : Function.Injective e) (a : A) :
    quotDecompose hJ he (Ideal.Quotient.mk J a) = quotDecomposeAux he a := by
  rw [← Ideal.Quotient.mk_eq_mk]
  simp only [quotDecompose, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]

/-- The quotient of a graded algebra by a homogeneous ideal `J`, regraded along an injective
additive map `e : ι' → ι` such that `J` contains every summand whose degree is not in the range
of `e`. -/
@[instance_reducible]
def quotGradedAlgebra (hJ : J.IsHomogeneous 𝒜) (he : Function.Injective e)
    (hkill : ∀ i, i ∉ Set.range e → ∀ a ∈ 𝒜 i, a ∈ J) : GradedAlgebra (quotGrade 𝒜 J e) where
  __ := quotGrade_gradedMonoid 𝒜 J e
  decompose' := quotDecompose hJ he
  left_inv x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotDecompose_mk]
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, map_zero, map_zero]
    | @homogeneous i a =>
      by_cases hi : i ∈ Set.range e
      · obtain ⟨i', rfl⟩ := hi
        rw [quotDecomposeAux_of_mem he a.2, DirectSum.coeAddMonoidHom_of]
      · rw [quotDecomposeAux_of_not_mem he hi a.2, map_zero, eq_comm,
          Ideal.Quotient.eq_zero_iff_mem]
        exact hkill i hi a a.2
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of i' c =>
      obtain ⟨a, ha, hac⟩ := exists_of_mem_quotGrade c.2
      rw [DirectSum.coeAddMonoidHom_of, ← hac, quotDecompose_mk, quotDecomposeAux_of_mem he ha]
      congr 1
      exact Subtype.ext hac
    | add x y hx hy => rw [map_add, map_add, hx, hy]

section AnyInstance

variable [GradedAlgebra (quotGrade 𝒜 J e)]

/-- For any grading instance on the quotient, the components of the class of `a` are the
classes of the components of `a` in the degrees `e i'`. -/
theorem gradeProj_quot_mk (he : Function.Injective e)
    (hkill : ∀ i, i ∉ Set.range e → ∀ a ∈ 𝒜 i, a ∈ J) (i' : ι') (a : A) :
    gradeProj (quotGrade 𝒜 J e) i' (Ideal.Quotient.mk J a) =
      Ideal.Quotient.mk J (gradeProj 𝒜 (e i') a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | @homogeneous i a =>
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j', rfl⟩ := hi
      rw [gradeProj_of_mem _ (mk_mem_quotGrade a.2), gradeProj_of_mem 𝒜 a.2]
      by_cases h : j' = i'
      · subst h; simp
      · simp [h, he.eq_iff]
    · have h : i ≠ e i' := fun h => hi ⟨i', h.symm⟩
      rw [(Ideal.Quotient.eq_zero_iff_mem).2 (hkill i hi a a.2), map_zero,
        gradeProj_of_mem 𝒜 a.2]
      simp [h]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end AnyInstance

section Bialgebra

variable {ι k A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommRing k] [CommRing A]
  [Bialgebra k A] {𝒜 : ι → Submodule k A} [GradedAlgebra 𝒜] {J : Ideal A}

omit [DecidableEq ι] [GradedAlgebra 𝒜] in
/-- The quotient map is graded for the quotient family indexed by `ι` itself. -/
theorem isGradedMap_mkₐ :
    IsGradedMap (ℳ := 𝒜) (ℳ' := quotGrade 𝒜 J (AddMonoidHom.id ι))
      (Ideal.Quotient.mkₐ k J).toLinearMap :=
  fun _ _ ha => mk_mem_quotGrade (e := AddMonoidHom.id ι) ha

variable [(J.restrictScalars k).IsCoideal]

omit [GradedAlgebra 𝒜] in
/-- The quotient of a graded bialgebra by a homogeneous biideal is a graded bialgebra, for any
grading instance on the family `quotGrade 𝒜 J id`. -/
theorem IsGradedBialgebra.quot [GradedAlgebra (quotGrade 𝒜 J (AddMonoidHom.id ι))]
    (h𝒜 : IsGradedBialgebra 𝒜) : IsGradedBialgebra (quotGrade 𝒜 J (AddMonoidHom.id ι)) where
  comul_mem n x hx := by
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotGrade hx
    rw [Bialgebra.Quotient.comul_mk]
    exact isGradedMap_mkₐ.map_tensorGrade isGradedMap_mkₐ (h𝒜.comul_mem n a ha)
  counit_eq_zero n hn x hx := by
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotGrade hx
    rw [Bialgebra.Quotient.counit_mk]
    exact h𝒜.counit_eq_zero n hn a ha

end Bialgebra

end Langlands.Algebra.GradedHopf
