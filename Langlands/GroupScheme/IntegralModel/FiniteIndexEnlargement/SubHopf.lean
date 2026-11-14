/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License 2.0; see licenses/Anthropic-FLT/LICENSE.
Adapted by Worker 33 from the `TakK` section of
P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean
at 6e837e75355538c7f80bab5b956861e86c4eacc2 (published in this Library as
Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed).
Changes: base field replaced by a commutative ring with flatness hypotheses; comultiplication
hypothesis stated through the range of `ι₂`; current induction principle; added the bialgebra
inclusion `valBialgHom`. See the paired Markdown.
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Flat.Basic

/-! # Hopf subalgebras of flat Hopf algebras

Let `A` be a Hopf algebra over a commutative ring `R` and `B` a subalgebra of `A`, with `A` and
`B` flat over `R`. If the comultiplication of `A` maps `B` into the image of `B ⊗[R] B` and the
antipode maps `B` into `B`, then `B` inherits a Hopf algebra structure for which the inclusion is
a bialgebra homomorphism.

The construction follows `TakK` in
`Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed`
(ported from the Anthropic FLT formalization, Copyright 2026 Anthropic, PBC, Apache License 2.0),
where the base is a field. Here the base is an arbitrary commutative ring and flatness of `A`
and `B` replaces the field hypothesis in the injectivity of the tensor-product maps. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.SubHopf

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
variable (B : Subalgebra R A)

/-- The inclusion of the subalgebra, as a linear map. -/
abbrev ι : B →ₗ[R] A := B.val.toLinearMap

/-- The inclusion of `B ⊗[R] B` into `A ⊗[R] A`. -/
abbrev ι₂ : B ⊗[R] B →ₗ[R] A ⊗[R] A := TensorProduct.map (ι B) (ι B)

theorem ι_injective : Function.Injective (ι B) := Subtype.val_injective

theorem ι₂_tmul (a b : B) : ι₂ B (a ⊗ₜ[R] b) = (a : A) ⊗ₜ[R] (b : A) := rfl

/-- The tensor product of two injective maps out of flat modules is injective. -/
theorem map_injective_of_flat {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N] [Module R P] [Module R Q]
    [Module.Flat R M] [Module.Flat R Q] (f : M →ₗ[R] P) (g : N →ₗ[R] Q)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)


/-- The counit of the subalgebra. -/
def counitLin : B →ₗ[R] R := Coalgebra.counit ∘ₗ ι B

theorem counitLin_apply (x : B) : counitLin B x = Coalgebra.counit (R := R) (x : A) := rfl

theorem map_ι₂_ι_rTensor {f : B →ₗ[R] B ⊗[R] B} {F : A →ₗ[R] A ⊗[R] A}
    (hfF : ∀ x, ι₂ B (f x) = F (x : A)) (z : B ⊗[R] B) :
    TensorProduct.map (ι₂ B) (ι B) (LinearMap.rTensor B f z) =
      LinearMap.rTensor A F (ι₂ B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, hfF]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_ι_ι₂_lTensor {f : B →ₗ[R] B ⊗[R] B} {F : A →ₗ[R] A ⊗[R] A}
    (hfF : ∀ x, ι₂ B (f x) = F (x : A)) (z : B ⊗[R] B) :
    TensorProduct.map (ι B) (ι₂ B) (LinearMap.lTensor B f z) =
      LinearMap.lTensor A F (ι₂ B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, hfF]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_ι_ι₂_assoc (w : (B ⊗[R] B) ⊗[R] B) :
    TensorProduct.map (ι B) (ι₂ B) (TensorProduct.assoc R _ _ _ w) =
      TensorProduct.assoc R A A A (TensorProduct.map (ι₂ B) (ι B) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z c =>
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul]
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem lTensor_ι_rTensor_counit (z : B ⊗[R] B) :
    LinearMap.lTensor R (ι B) (LinearMap.rTensor B (counitLin B) z) =
      LinearMap.rTensor A Coalgebra.counit (ι₂ B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      counitLin_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem rTensor_ι_lTensor_counit (z : B ⊗[R] B) :
    LinearMap.rTensor R (ι B) (LinearMap.lTensor B (counitLin B) z) =
      LinearMap.lTensor A Coalgebra.counit (ι₂ B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      counitLin_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ι₂_eq_toLinearMap :
    ι₂ B = (Algebra.TensorProduct.map B.val B.val).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  rfl

theorem ι₂_mul (z w : B ⊗[R] B) : ι₂ B (z * w) = ι₂ B z * ι₂ B w := by
  rw [ι₂_eq_toLinearMap]
  exact map_mul (Algebra.TensorProduct.map B.val B.val) z w

theorem ι₂_one : ι₂ B 1 = 1 := by
  rw [ι₂_eq_toLinearMap]
  exact map_one (Algebra.TensorProduct.map B.val B.val)

variable [Module.Flat R A] [Module.Flat R B]

theorem ι₂_injective : Function.Injective (ι₂ B) :=
  map_injective_of_flat _ _ (ι_injective B) (ι_injective B)

theorem ι₃_injective : Function.Injective (TensorProduct.map (ι B) (ι₂ B)) :=
  map_injective_of_flat _ _ (ι_injective B) (ι₂_injective B)

section comul

variable (hΔ : ∀ x : B, Coalgebra.comul (R := R) (x : A) ∈ LinearMap.range (ι₂ B))

/-- The comultiplication of the subalgebra. -/
def comulLin : B →ₗ[R] B ⊗[R] B :=
  (LinearEquiv.ofInjective (ι₂ B) (ι₂_injective B)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (ι₂ B)) (Coalgebra.comul ∘ₗ ι B) hΔ

theorem ι₂_comulLin (x : B) : ι₂ B (comulLin B hΔ x) = Coalgebra.comul (R := R) (x : A) := by
  simp only [comulLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← LinearEquiv.ofInjective_apply (ι₂ B) (h := ι₂_injective B), LinearEquiv.apply_symm_apply]
  rfl

end comul

section structures

variable (hΔ : ∀ x : B, Coalgebra.comul (R := R) (x : A) ∈ LinearMap.range (ι₂ B))

/-- The coalgebra structure maps of the subalgebra. -/
@[reducible] def coalgebraStruct : CoalgebraStruct R B where
  comul := comulLin B hΔ
  counit := counitLin B

/-- The coalgebra structure of the subalgebra. -/
@[reducible] def coalgebra : Coalgebra R B :=
  { coalgebraStruct B hΔ with
    coassoc := by
      apply LinearMap.ext
      intro x
      apply ι₃_injective B
      change TensorProduct.map (ι B) (ι₂ B) (TensorProduct.assoc R _ _ _
          (LinearMap.rTensor B (comulLin B hΔ) (comulLin B hΔ x))) =
        TensorProduct.map (ι B) (ι₂ B) (LinearMap.lTensor B (comulLin B hΔ) (comulLin B hΔ x))
      rw [map_ι_ι₂_assoc, map_ι₂_ι_rTensor B (ι₂_comulLin B hΔ),
        map_ι_ι₂_lTensor B (ι₂_comulLin B hΔ), ι₂_comulLin, Coalgebra.coassoc_apply]
    rTensor_counit_comp_comul := by
      apply LinearMap.ext
      intro x
      apply Module.Flat.lTensor_preserves_injective_linearMap (M := R) (ι B) (ι_injective B)
      change LinearMap.lTensor R (ι B) (LinearMap.rTensor B (counitLin B) (comulLin B hΔ x)) =
        LinearMap.lTensor R (ι B) ((1 : R) ⊗ₜ[R] x)
      rw [lTensor_ι_rTensor_counit, ι₂_comulLin, Coalgebra.rTensor_counit_comul]
      simp
    lTensor_counit_comp_comul := by
      apply LinearMap.ext
      intro x
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := R) (ι B) (ι_injective B)
      change LinearMap.rTensor R (ι B) (LinearMap.lTensor B (counitLin B) (comulLin B hΔ x)) =
        LinearMap.rTensor R (ι B) (x ⊗ₜ[R] (1 : R))
      rw [rTensor_ι_lTensor_counit, ι₂_comulLin, Coalgebra.lTensor_counit_comul]
      simp }

theorem comulLin_mul (a b : B) :
    comulLin B hΔ (a * b) = comulLin B hΔ a * comulLin B hΔ b := by
  apply ι₂_injective B
  rw [ι₂_mul, ι₂_comulLin, ι₂_comulLin, ι₂_comulLin, Subalgebra.coe_mul, Bialgebra.comul_mul]

theorem comulLin_one : comulLin B hΔ 1 = 1 := by
  apply ι₂_injective B
  rw [ι₂_comulLin, ι₂_one, Subalgebra.coe_one, Bialgebra.comul_one]

/-- The bialgebra structure of the subalgebra. -/
@[reducible] def bialgebra : Bialgebra R B :=
  { coalgebra B hΔ with
    counit_one := by
      change counitLin B 1 = 1
      rw [counitLin_apply, Subalgebra.coe_one, Bialgebra.counit_one]
    mul_compr₂_counit := by
      apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
      change counitLin B (a * b) = counitLin B a * counitLin B b
      rw [counitLin_apply, counitLin_apply, counitLin_apply, Subalgebra.coe_mul,
        Bialgebra.counit_mul]
    comul_one := comulLin_one B hΔ
    mul_compr₂_comul := by
      apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
      exact comulLin_mul B hΔ a b }

variable (hS : ∀ x : B, HopfAlgebra.antipode R (x : A) ∈ B)

/-- The antipode of the subalgebra. -/
def antipodeLin : B →ₗ[R] B :=
  LinearMap.codRestrict B.toSubmodule ((HopfAlgebra.antipode R).comp (ι B)) hS

omit [Module.Flat R A] [Module.Flat R B] in
theorem coe_antipodeLin (x : B) :
    (antipodeLin B hS x : A) = HopfAlgebra.antipode R (x : A) := rfl

omit [Module.Flat R A] [Module.Flat R B] in
theorem ι_mul'_rTensor (z : B ⊗[R] B) :
    ι B (LinearMap.mul' R B (LinearMap.rTensor B (antipodeLin B hS) z)) =
      LinearMap.mul' R A (LinearMap.rTensor A (HopfAlgebra.antipode R) (ι₂ B z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [Module.Flat R A] [Module.Flat R B] in
theorem ι_mul'_lTensor (z : B ⊗[R] B) :
    ι B (LinearMap.mul' R B (LinearMap.lTensor B (antipodeLin B hS) z)) =
      LinearMap.mul' R A (LinearMap.lTensor A (HopfAlgebra.antipode R) (ι₂ B z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The Hopf algebra structure of the subalgebra. -/
@[reducible] def hopfAlgebra : HopfAlgebra R B :=
  { bialgebra B hΔ with
    antipode := antipodeLin B hS
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext; intro x
      apply ι_injective B
      change ι B (LinearMap.mul' R B (LinearMap.rTensor B (antipodeLin B hS)
          (comulLin B hΔ x))) = ι B (algebraMap R B (counitLin B x))
      rw [ι_mul'_rTensor, ι₂_comulLin, HopfAlgebra.mul_antipode_rTensor_comul_apply,
        counitLin_apply]
      rfl
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext; intro x
      apply ι_injective B
      change ι B (LinearMap.mul' R B (LinearMap.lTensor B (antipodeLin B hS)
          (comulLin B hΔ x))) = ι B (algebraMap R B (counitLin B x))
      rw [ι_mul'_lTensor, ι₂_comulLin, HopfAlgebra.mul_antipode_lTensor_comul_apply,
        counitLin_apply]
      rfl }

/-- The inclusion of the Hopf subalgebra is a bialgebra homomorphism. -/
def valBialgHom : letI := hopfAlgebra B hΔ hS; B →ₐc[R] A :=
  letI := hopfAlgebra B hΔ hS
  { B.val with
    map_smul' := fun r x => map_smul B.val r x
    counit_comp := by
      apply LinearMap.ext
      intro x
      rfl
    map_comp_comul := by
      apply LinearMap.ext
      intro x
      exact ι₂_comulLin B hΔ x }

theorem valBialgHom_apply (x : B) :
    letI := hopfAlgebra B hΔ hS
    valBialgHom B hΔ hS x = (x : A) := rfl

theorem toAlgHom_valBialgHom :
    letI := hopfAlgebra B hΔ hS
    ((valBialgHom B hΔ hS : B →ₐ[R] A)) = B.val := rfl

theorem comul_val (x : B) :
    letI := hopfAlgebra B hΔ hS
    Coalgebra.comul (R := R) (x : A) = ι₂ B (Coalgebra.comul (R := R) x) :=
  (ι₂_comulLin B hΔ x).symm

end structures

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.SubHopf
