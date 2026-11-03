import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.TitsStandardParabolicStatement

/-! # Generation of the standard relative Weyl subgroups from a Coxeter realization

In a Coxeter realization of the relative Weyl group, the simple reflection of a simple
relative root `a` is the unique relative reflection in `a`. Hence the relative reflections
in a set `J` of simple roots are the Coxeter generators labelled by `J`, and the parabolic
clause of the realization identifies the subgroup they generate with the standard relative
Weyl subgroup of `J`. This gives `StandardRelativeWeylGenerationStatement` from
`RelativeWeylCoxeterStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.LinearAlgebra

/-- Two reflections in the same vector over a field of characteristic zero have the same
linear form when their product has finite order: the product is the shear
`y ↦ y + (f - g) y • x`, of infinite order unless `f = g`. -/
theorem dual_eq_of_isOfFinOrder_reflection_mul {R M : Type*} [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] {x : M} {f g : Module.Dual R M} (hf : f x = 2)
    (hg : g x = 2) (hu : IsOfFinOrder (Module.reflection hg * Module.reflection hf)) :
    f = g := by
  have hx : x ≠ 0 := by rintro rfl; simp at hf
  set u := Module.reflection hg * Module.reflection hf with hu_def
  have hu1 : (u : M →ₗ[R] M) = LinearMap.id + (f - g).smulRight x := by
    ext y
    simp only [u, Module.reflection_apply, hg, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, Module.End.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  have hpow : ∀ n : ℕ,
      ((u ^ n : M ≃ₗ[R] M) : M →ₗ[R] M) = LinearMap.id + (n : R) • (f - g).smulRight x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf, hg]
      rw [pow_succ', LinearEquiv.coe_toLinearMap_mul, ih, hu1, add_mul, mul_add, mul_add]
      simp_rw [Module.End.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
        add_assoc, Nat.cast_succ, add_smul, one_smul]
  obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
  replace hn₁ : ((u ^ n : M ≃ₗ[R] M) : M →ₗ[R] M) = LinearMap.id :=
    LinearEquiv.toLinearMap_inj.mpr hn₁
  simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hpow n

namespace RationalSpan

variable {M : Type*} [AddCommGroup M]

/-- The `ℚ`-linear extension `q ⊗ m ↦ q * f m` of an integral linear form `f`. -/
def ratForm (f : M →+ ℤ) : Module.Dual ℚ (ℚ ⊗[ℤ] M) :=
  ((Int.castAddHom ℚ).comp f).toIntLinearMap.liftBaseChange ℚ

theorem ratForm_tmul (f : M →+ ℤ) (q : ℚ) (m : M) : ratForm f (q ⊗ₜ[ℤ] m) = q * f m := by
  simp [ratForm]

/-- An integral reflection formula `σ χ = χ - f χ • a` extends to `ℚ ⊗[ℤ] M`. -/
theorem ratAut_apply_of_forall_eq_sub (σ : M ≃ₗ[ℤ] M) (f : M →+ ℤ) (a : M)
    (hσ : ∀ χ, σ χ = χ - f χ • a) (v : ℚ ⊗[ℤ] M) :
    ratAut σ v = v - ratForm f v • toRat a := by
  have h : (ratAut σ : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M)) =
      LinearMap.id - (ratForm f).smulRight (toRat a) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q χ
    change q ⊗ₜ[ℤ] σ χ = q ⊗ₜ[ℤ] χ - ratForm f (q ⊗ₜ[ℤ] χ) • toRat a
    rw [hσ, ratForm_tmul, toRat_apply, TensorProduct.tmul_sub, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_comm]
  exact LinearMap.congr_fun h v

end RationalSpan

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom]

/-- The action on the relative-root span is the rationalized character action. -/
theorem coe_relativeWeylAction_apply_eq_ratAut (w : relativeWeylGroup i)
    (x : relativeRootSpan i) :
    (relativeWeylAction i w x : ℚ ⊗[ℤ] characterLattice T) =
      ratAut (schemeWeylCharacterAction i w) x := by
  induction w using QuotientGroup.induction_on with
  | H n => rfl

variable {ν : cocharacterLattice T} {M : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem M (relativeWeylGroup i)}

/-- In a Coxeter realization, the simple reflection of `a` is a relative reflection in `a`. -/
theorem IsRelativeWeylCoxeterRealization.isRelativeReflection_simple
    (h : IsRelativeWeylCoxeterRealization i ν cs) (a : SimpleRoot i ν) :
    IsRelativeReflection i a.1 (cs.simple a) := by
  obtain ⟨f, hfa, hf⟩ := h.1 a
  refine ⟨a.2.1.1, (ratForm f).domRestrict (relativeRootSpan i), ?_, ?_⟩
  · change ratForm f (toRat a.1) = 2
    rw [toRat_apply, ratForm_tmul, hfa]
    norm_num
  · apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [coe_relativeWeylAction_apply_eq_ratAut, ratAut_apply_of_forall_eq_sub _ f a.1 hf,
      Module.reflection_apply]
    rfl

/-- In a Coxeter realization, an element acting trivially on the relative-root span is
trivial: it fixes every relative root, so its inversion set is empty and its length is
zero. -/
theorem IsRelativeWeylCoxeterRealization.eq_one_of_relativeWeylAction_eq_one
    (hT : IsSplitTorus T.toGrp) (h : IsRelativeWeylCoxeterRealization i ν cs)
    {v : relativeWeylGroup i} (hv : relativeWeylAction i v = 1) : v = 1 := by
  induction v using QuotientGroup.induction_on with | H n => ?_
  have hfix := (hT.relativeWeylAction_mk_eq_one_iff i n).1 hv
  have hempty : relativeInversionSet i ν (QuotientGroup.mk n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    rintro α ⟨⟨⟨hα, hpos⟩, -⟩, -, hneg⟩
    rw [schemeWeylCharacterAction_mk, hfix α hα, map_neg, LinearMap.neg_apply] at hneg
    omega
  rw [← cs.length_eq_zero_iff, h.2.2.2.1, hempty, Set.ncard_empty]

/-- In a Coxeter realization of a finite relative Weyl group, every relative reflection in a
simple root `a` is the simple reflection of `a`. -/
theorem IsRelativeWeylCoxeterRealization.eq_simple_of_isRelativeReflection
    [Finite (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)
    (h : IsRelativeWeylCoxeterRealization i ν cs) (a : SimpleRoot i ν)
    {w : relativeWeylGroup i} (hw : IsRelativeReflection i a.1 w) : w = cs.simple a := by
  obtain ⟨_, g, hg, hwg⟩ := hw
  obtain ⟨_, f, hf, hsf⟩ := h.isRelativeReflection_simple a
  have hu : IsOfFinOrder (Module.reflection hg * Module.reflection hf) := by
    have := (relativeWeylAction i).isOfFinOrder (isOfFinOrder_of_finite (w * cs.simple a))
    rwa [map_mul, hwg, hsf] at this
  obtain rfl := Langlands.LinearAlgebra.dual_eq_of_isOfFinOrder_reflection_mul hf hg hu
  have h1 : relativeWeylAction i (w * (cs.simple a)⁻¹) = 1 := by
    rw [map_mul, map_inv, hwg, hsf, mul_inv_cancel]
  exact mul_inv_eq_one.mp (h.eq_one_of_relativeWeylAction_eq_one hT h1)

/-- In a Coxeter realization of a finite relative Weyl group with finitely many simple roots,
the relative reflections in a set `J` of simple roots generate the standard relative Weyl
subgroup of `J`. -/
theorem IsRelativeWeylCoxeterRealization.closure_relativeReflections_eq
    [Finite (relativeWeylGroup i)] [Finite (SimpleRoot i ν)] (hT : IsSplitTorus T.toGrp)
    (h : IsRelativeWeylCoxeterRealization i ν cs) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    Subgroup.closure (relativeReflections i J) = standardRelativeWeylGroup i ν J := by
  obtain ⟨I, hI⟩ : ∃ I : Finset (SimpleRoot i ν), ∀ a, a ∈ I ↔ a.1 ∈ J :=
    ⟨(Set.toFinite {a : SimpleRoot i ν | a.1 ∈ J}).toFinset, fun a => by simp⟩
  have hroot : rootSet i ν I = J := by
    ext α
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hI a).1 ha
    · intro hα
      exact ⟨⟨α, hJ hα⟩, (hI _).2 hα, rfl⟩
  have hrefl : relativeReflections i J = cs.simple '' (I : Set (SimpleRoot i ν)) := by
    ext w
    constructor
    · rintro ⟨α, hα, hw⟩
      exact ⟨⟨α, hJ hα⟩, (hI _).2 hα,
        (h.eq_simple_of_isRelativeReflection hT ⟨α, hJ hα⟩ hw).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.1, (hI a).1 ha, h.isRelativeReflection_simple a⟩
  have hpar := h.2.2.2.2 I
  rw [hroot] at hpar
  rw [hrefl, ← hpar]
  rfl

/-- **Borel–Tits 5.17 from the Coxeter statement.** The Coxeter realization of the relative
Weyl group identifies the subgroup generated by the reflections in a set of simple roots with
the standard relative Weyl subgroup. -/
theorem standardRelativeWeylGenerationStatement_of_relativeWeylCoxeter
    (hcox : RelativeWeylCoxeterStatement.{u}) : StandardRelativeWeylGenerationStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν J hJ
  obtain ⟨hW, hS, M, cs, h⟩ := hcox k G hG T i hi ν hν
  exact h.closure_relativeReflections_eq hi.isSplitSubtorus.1 hJ

end Langlands.GroupScheme
