import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Noetherian.Basic

/-! # A free cover of a finitely generated abelian group, functorial in isomorphisms -/

noncomputable section

universe u

namespace Langlands.GroupScheme.FreeCharacterCover

variable (Λ : Type u) [AddCommGroup Λ]

/-- The order of the torsion subgroup of `Λ` (zero when it is infinite). -/
def torsionOrder : ℕ := Nat.card (Submodule.torsion ℤ Λ)

variable {Λ} in
theorem torsionOrder_smul_eq_zero {x : Λ} (hx : x ∈ Submodule.torsion ℤ Λ) :
    torsionOrder Λ • x = 0 := by
  have h := card_nsmul_eq_zero' (G := Submodule.torsion ℤ Λ) (x := ⟨x, hx⟩)
  simpa [torsionOrder] using congrArg Subtype.val h

theorem finite_torsion [AddGroup.FG Λ] : Finite (Submodule.torsion ℤ Λ) := by
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact Module.finite_of_fg_torsion _ (Submodule.torsion_isTorsion)

theorem torsionOrder_pos [AddGroup.FG Λ] : 0 < torsionOrder Λ := by
  have := finite_torsion Λ
  exact Nat.card_pos

/-- The subgroup of multiples by the torsion order. -/
def multiples : Submodule ℤ Λ :=
  LinearMap.range (LinearMap.lsmul ℤ Λ (torsionOrder Λ : ℤ))

variable {Λ} in
theorem mem_multiples {x : Λ} : x ∈ multiples Λ ↔ ∃ y : Λ, (torsionOrder Λ : ℤ) • y = x := by
  simp [multiples]

/-- The finite quotient `Λ / eΛ`, with `e` the torsion order. -/
abbrev Quot : Type u := Λ ⧸ multiples Λ

theorem quot_isTorsion [AddGroup.FG Λ] : Module.IsTorsion ℤ (Quot Λ) := by
  intro q
  refine ⟨⟨(torsionOrder Λ : ℤ), mem_nonZeroDivisors_of_ne_zero
    (by exact_mod_cast (torsionOrder_pos Λ).ne')⟩, ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change (torsionOrder Λ : ℤ) • (Submodule.Quotient.mk x : Quot Λ) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_multiples]
    exact ⟨x, rfl⟩

instance quot_finite [AddGroup.FG Λ] : Finite (Quot Λ) := by
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact Module.finite_of_fg_torsion _ (quot_isTorsion Λ)

/-- The sum map `ℤ[Λ/eΛ] → Λ/eΛ`. -/
def sumMap : (Quot Λ →₀ ℤ) →ₗ[ℤ] Quot Λ := Finsupp.linearCombination ℤ id

@[simp] theorem sumMap_single (q : Quot Λ) (n : ℤ) :
    sumMap Λ (Finsupp.single q n) = n • q := by
  simp [sumMap]

/-- The defining equation of the fibre product. -/
def coverEquation : Λ × (Quot Λ →₀ ℤ) →ₗ[ℤ] Quot Λ :=
  (multiples Λ).mkQ ∘ₗ LinearMap.fst ℤ Λ _ - sumMap Λ ∘ₗ LinearMap.snd ℤ Λ _

/-- The fibre product `Λ ×_{Λ/eΛ} ℤ[Λ/eΛ]`, as a submodule. -/
def cover : Submodule ℤ (Λ × (Quot Λ →₀ ℤ)) := LinearMap.ker (coverEquation Λ)

/-- The free cover `F(Λ) = Λ ×_{Λ/eΛ} ℤ[Λ/eΛ]`. -/
abbrev Cover : Type u := cover Λ

variable {Λ} in
theorem mem_cover {x : Λ × (Quot Λ →₀ ℤ)} :
    x ∈ cover Λ ↔ (Submodule.Quotient.mk x.1 : Quot Λ) = sumMap Λ x.2 := by
  simp [cover, coverEquation, sub_eq_zero]

/-- The projection `F(Λ) → Λ`. -/
def proj : Cover Λ →+ Λ :=
  ((LinearMap.fst ℤ Λ (Quot Λ →₀ ℤ)).comp (cover Λ).subtype).toAddMonoidHom

@[simp] theorem proj_apply (x : Cover Λ) : proj Λ x = x.1.1 := rfl

theorem proj_surjective : Function.Surjective (proj Λ) := by
  intro x
  refine ⟨⟨(x, Finsupp.single (Submodule.Quotient.mk x) 1), ?_⟩, rfl⟩
  rw [mem_cover]
  simp

instance cover_finite [AddGroup.FG Λ] : Module.Finite ℤ (Cover Λ) := by
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact Module.Finite.of_injective (cover Λ).subtype Subtype.val_injective

instance cover_isTorsionFree [AddGroup.FG Λ] : Module.IsTorsionFree ℤ (Cover Λ) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x hx => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨⟨l, c⟩, hlc⟩ := x
  have hx' : r • ((l, c) : Λ × (Quot Λ →₀ ℤ)) = 0 := congrArg Subtype.val hx
  have h1 : r • l = 0 := congrArg Prod.fst hx'
  have h2 : r • c = 0 := congrArg Prod.snd hx'
  have hc : c = 0 := by
    ext a
    have := congrArg (fun f => f a) h2
    simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul,
      mul_eq_zero] at this
    simpa using this.resolve_left hr
  subst hc
  rw [mem_cover] at hlc
  simp only [map_zero] at hlc
  obtain ⟨y, rfl⟩ := mem_multiples.mp ((Submodule.Quotient.mk_eq_zero _).mp hlc)
  have hy : y ∈ Submodule.torsion ℤ Λ := by
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨r * torsionOrder Λ, mem_nonZeroDivisors_of_ne_zero
      (mul_ne_zero hr (by exact_mod_cast (torsionOrder_pos Λ).ne'))⟩, ?_⟩
    change (r * torsionOrder Λ) • y = 0
    rw [mul_smul]
    exact h1
  have hy0 : (torsionOrder Λ : ℤ) • y = 0 := by
    rw [natCast_zsmul]
    exact torsionOrder_smul_eq_zero hy
  ext
  · exact hy0
  · rfl

instance cover_free [AddGroup.FG Λ] : Module.Free ℤ (Cover Λ) :=
  Module.free_of_finite_type_torsion_free'

/-! ### Functoriality in isomorphisms -/

variable {Λ} {Λ' Λ'' : Type u} [AddCommGroup Λ'] [AddCommGroup Λ'']

theorem mem_torsion_congr (g : Λ ≃+ Λ') (x : Λ) :
    g x ∈ Submodule.torsion ℤ Λ' ↔ x ∈ Submodule.torsion ℤ Λ := by
  simp only [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, g.injective ?_⟩
    change g ((a : ℤ) • x) = g 0
    rw [map_zsmul, map_zero]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    change (a : ℤ) • g x = 0
    rw [← map_zsmul]
    change g (a • x) = 0
    rw [ha, map_zero]

theorem torsionOrder_congr (g : Λ ≃+ Λ') : torsionOrder Λ = torsionOrder Λ' :=
  Nat.card_congr (Equiv.subtypeEquiv g.toEquiv fun x => (mem_torsion_congr g x).symm)

theorem map_multiples (g : Λ ≃+ Λ') :
    (multiples Λ).map g.toIntLinearEquiv.toLinearMap = multiples Λ' := by
  ext x
  simp only [Submodule.mem_map, mem_multiples, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨g y, ?_⟩
    rw [← torsionOrder_congr g]
    exact (map_zsmul g _ y).symm
  · rintro ⟨y, rfl⟩
    refine ⟨(torsionOrder Λ : ℤ) • g.symm y, ⟨g.symm y, rfl⟩, ?_⟩
    change g ((torsionOrder Λ : ℤ) • g.symm y) = _
    rw [map_zsmul, AddEquiv.apply_symm_apply, torsionOrder_congr g]

/-- The induced isomorphism of the finite quotients. -/
def quotEquiv (g : Λ ≃+ Λ') : Quot Λ ≃+ Quot Λ' :=
  (Submodule.Quotient.equiv (multiples Λ) (multiples Λ') g.toIntLinearEquiv
    (map_multiples g)).toAddEquiv

@[simp] theorem quotEquiv_mk (g : Λ ≃+ Λ') (x : Λ) :
    quotEquiv g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x) := rfl

theorem quotEquiv_refl (q : Quot Λ) : quotEquiv (AddEquiv.refl Λ) q = q := by
  induction q using Submodule.Quotient.induction_on with
  | H x => rfl

theorem quotEquiv_trans (g : Λ ≃+ Λ') (h : Λ' ≃+ Λ'') (q : Quot Λ) :
    quotEquiv (g.trans h) q = quotEquiv h (quotEquiv g q) := by
  induction q using Submodule.Quotient.induction_on with
  | H x => rfl

theorem sumMap_mapDomain (g : Λ ≃+ Λ') (c : Quot Λ →₀ ℤ) :
    sumMap Λ' (Finsupp.mapDomain (quotEquiv g) c) = quotEquiv g (sumMap Λ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [Finsupp.mapDomain_add, hc, hd]
  | single q n => simp [Finsupp.mapDomain_single]

/-- The map of free covers induced by an isomorphism, as an additive map. -/
def coverHom (g : Λ ≃+ Λ') : Cover Λ →+ Cover Λ' where
  toFun x := ⟨(g x.1.1, Finsupp.mapDomain (quotEquiv g) x.1.2), by
    rw [mem_cover]
    have hx := mem_cover.mp x.2
    simp only [sumMap_mapDomain, ← hx]
    rfl⟩
  map_zero' := by
    ext
    · simp
    · simp
  map_add' x y := by
    ext
    · simp
    · simp [Finsupp.mapDomain_add]

@[simp] theorem coverHom_fst (g : Λ ≃+ Λ') (x : Cover Λ) :
    (coverHom g x).1.1 = g x.1.1 := rfl

@[simp] theorem coverHom_snd (g : Λ ≃+ Λ') (x : Cover Λ) :
    (coverHom g x).1.2 = Finsupp.mapDomain (quotEquiv g) x.1.2 := rfl

theorem coverHom_refl (x : Cover Λ) : coverHom (AddEquiv.refl Λ) x = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Finsupp.mapDomain (quotEquiv (AddEquiv.refl Λ)) x.1.2 = x.1.2
    have : (quotEquiv (AddEquiv.refl Λ) : Quot Λ → Quot Λ) = id :=
      funext quotEquiv_refl
    rw [this, Finsupp.mapDomain_id]

theorem coverHom_trans (g : Λ ≃+ Λ') (h : Λ' ≃+ Λ'') (x : Cover Λ) :
    coverHom (g.trans h) x = coverHom h (coverHom g x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Finsupp.mapDomain (quotEquiv (g.trans h)) x.1.2 =
      Finsupp.mapDomain (quotEquiv h) (Finsupp.mapDomain (quotEquiv g) x.1.2)
    have : (quotEquiv (g.trans h) : Quot Λ → Quot Λ'') = quotEquiv h ∘ quotEquiv g :=
      funext (quotEquiv_trans g h)
    rw [this, Finsupp.mapDomain_comp]

/-- The isomorphism of free covers induced by an isomorphism `g : Λ ≃+ Λ'`. -/
def coverEquiv (g : Λ ≃+ Λ') : Cover Λ ≃+ Cover Λ' where
  toFun := coverHom g
  invFun := coverHom g.symm
  left_inv x := by
    rw [← coverHom_trans]
    simp only [AddEquiv.self_trans_symm]
    exact coverHom_refl x
  right_inv x := by
    rw [← coverHom_trans]
    simp only [AddEquiv.symm_trans_self]
    exact coverHom_refl x
  map_add' := (coverHom g).map_add

@[simp] theorem coverEquiv_apply (g : Λ ≃+ Λ') (x : Cover Λ) :
    coverEquiv g x = coverHom g x := rfl

@[simp] theorem coverEquiv_refl : coverEquiv (AddEquiv.refl Λ) = AddEquiv.refl _ := by
  ext x : 1
  exact coverHom_refl x

theorem coverEquiv_trans (g : Λ ≃+ Λ') (h : Λ' ≃+ Λ'') :
    coverEquiv (g.trans h) = (coverEquiv g).trans (coverEquiv h) := by
  ext x : 1
  exact coverHom_trans g h x

/-- The projection is natural in isomorphisms. -/
theorem proj_coverEquiv (g : Λ ≃+ Λ') (x : Cover Λ) :
    proj Λ' (coverEquiv g x) = g (proj Λ x) := rfl

theorem proj_comp_coverEquiv (g : Λ ≃+ Λ') :
    (proj Λ').comp (coverEquiv g).toAddMonoidHom = (g.toAddMonoidHom).comp (proj Λ) := by
  ext x
  rfl

end Langlands.GroupScheme.FreeCharacterCover
