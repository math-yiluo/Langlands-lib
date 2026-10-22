import Langlands.AbelianScheme.IsogenyInverseStatement
import Langlands.AbelianScheme.IsogenyStability
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Proof of rational invertibility with a uniform kernel annihilator -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- The underlying scheme morphism of an isogeny is an effective epimorphism. -/
theorem IsIsogeny.effectiveEpi {f : G ⟶ H} (hf : IsIsogeny f) :
    EffectiveEpi f.hom.hom.left := by
  have : IsFinite f.hom.hom.left := hf.1
  have : Flat f.hom.hom.left := hf.2.1
  have : Surjective f.hom.hom.left := hf.2.2
  infer_instance

/-- The product of an isogeny with itself is again an isogeny of underlying schemes. -/
theorem IsIsogeny.tensorHom {f : G ⟶ H} (hf : IsIsogeny f) :
    isogenyProperty (f.hom.hom ⊗ₘ f.hom.hom).left :=
  MorphismProperty.pullbackMap (P := isogenyProperty) hf hf
    (Over.w f.hom.hom).symm (Over.w f.hom.hom).symm

/-- The product of an isogeny with itself is an epimorphism over the base. -/
theorem IsIsogeny.epi_tensorHom {f : G ⟶ H} (hf : IsIsogeny f) :
    Epi (f.hom.hom ⊗ₘ f.hom.hom) := by
  have h := hf.tensorHom
  have : IsFinite (f.hom.hom ⊗ₘ f.hom.hom).left := h.1
  have : Flat (f.hom.hom ⊗ₘ f.hom.hom).left := h.2.1
  have : Surjective (f.hom.hom ⊗ₘ f.hom.hom).left := h.2.2
  exact Over.epi_of_epi_left _

section Descent

variable [IsCommMonObj G.X] [IsCommMonObj H.X]

omit [IsCommMonObj H.X] in
/-- If multiplication by `n` kills the kernel, it agrees on any two scheme points
with the same image. -/
theorem multiplication_comp_eq_of_comp_eq (f : G ⟶ H) {n : ℤ}
    (hn : multiplication (kernel f) n = 1) {Z : Scheme.{u}} (a b : Z ⟶ G.X.left)
    (h : a ≫ f.hom.hom.left = b ≫ f.hom.hom.left) :
    a ≫ (multiplication G n).hom.hom.left = b ≫ (multiplication G n).hom.hom.left := by
  have hb : b ≫ G.X.hom = a ≫ G.X.hom := by
    rw [← Over.w f.hom.hom, ← Category.assoc, ← h, Category.assoc]
  let a' : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk a rfl
  let b' : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk b hb
  have h' : a' ≫ f.hom.hom = b' ≫ f.hom.hom := Over.OverMorphism.ext h
  have hker : (a' / b') ≫ f.hom.hom = toUnit _ ≫ η[H.X] := by
    rw [GrpObj.div_comp, h', div_self']
    rfl
  let k := (kernel_isPullback f).lift (a' / b') (toUnit _) hker
  have hk : k ≫ (kernelι f).hom.hom = a' / b' := (kernel_isPullback f).lift_fst _ _ _
  have hpow : (a' / b') ^ n = 1 := by
    rw [← hk, ← GrpObj.zpow_comp, ← points_multiplication, hn]
    simp
  have hab : a' ≫ (multiplication G n).hom.hom = b' ≫ (multiplication G n).hom.hom := by
    rw [points_multiplication, points_multiplication, ← div_eq_one, ← div_zpow, hpow]
  exact congrArg (fun x => x.left) hab

variable {f : G ⟶ H} (hf : IsIsogeny f) {n : ℤ} (hn : multiplication (kernel f) n = 1)

/-- The scheme morphism obtained by descending multiplication by `n` along the isogeny. -/
def descentHom : H.X.left ⟶ G.X.left :=
  haveI := hf.effectiveEpi
  EffectiveEpi.desc f.hom.hom.left (multiplication G n).hom.hom.left
    (fun a b h => multiplication_comp_eq_of_comp_eq f hn a b h)

omit [IsCommMonObj H.X] in
@[reassoc]
theorem fac_descentHom :
    f.hom.hom.left ≫ descentHom hf hn = (multiplication G n).hom.hom.left :=
  haveI := hf.effectiveEpi
  EffectiveEpi.fac _ _ _

/-- The descended morphism is a morphism over the base. -/
def descentOver : H.X ⟶ G.X :=
  Over.homMk (descentHom hf hn) (by
    have := hf.effectiveEpi
    apply (cancel_epi f.hom.hom.left).mp
    rw [fac_descentHom_assoc, Over.w, Over.w])

omit [IsCommMonObj H.X] in
@[reassoc]
theorem comp_descentOver :
    f.hom.hom ≫ descentOver hf hn = (multiplication G n).hom.hom :=
  Over.OverMorphism.ext (fac_descentHom hf hn)

instance : IsMonHom (descentOver hf hn) where
  one_hom := by
    rw [← IsMonHom.one_hom f.hom.hom, Category.assoc, comp_descentOver, IsMonHom.one_hom]
  mul_hom := by
    have := hf.epi_tensorHom
    apply (cancel_epi (f.hom.hom ⊗ₘ f.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, comp_descentOver, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, comp_descentOver]

/-- The group-scheme homomorphism descended from multiplication by `n`. -/
def descent : H ⟶ G := Grp.homMk (descentOver hf hn)

omit [IsCommMonObj H.X] in
theorem comp_descent : f ≫ descent hf hn = multiplication G n :=
  Grp.hom_ext _ _ (comp_descentOver hf hn)

theorem descent_comp : descent hf hn ≫ f = multiplication H n := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  have := hf.effectiveEpi
  apply (cancel_epi f.hom.hom.left).mp
  change f.hom.hom.left ≫ descentHom hf hn ≫ f.hom.hom.left =
    f.hom.hom.left ≫ (multiplication H n).hom.hom.left
  rw [fac_descentHom_assoc]
  exact congrArg (fun φ => φ.hom.hom.left) (multiplication_naturality f n)

end Descent

end Langlands.GroupScheme

namespace Langlands.CommGroupScheme

theorem isogenyInverse : IsogenyInverseStatement.{u} := by
  intro S G H f hf ⟨n, hn0, hn⟩
  let g : H ⟶ G := Additive.ofMul (GroupScheme.descent hf hn)
  have hfg : f ≫ g = n • 𝟙 G := by
    change Additive.ofMul (groupHom f ≫ GroupScheme.descent hf hn) =
      n • Additive.ofMul (𝟙 G.toGrp)
    rw [GroupScheme.comp_descent, ← ofMul_zpow]
    rfl
  have hgf : g ≫ f = n • 𝟙 H := by
    change Additive.ofMul (GroupScheme.descent hf hn ≫ groupHom f) =
      n • Additive.ofMul (𝟙 H.toGrp)
    rw [GroupScheme.descent_comp, ← ofMul_zpow]
    rfl
  have hq : (n : ℚ) • (n : ℚ)⁻¹ = 1 := by
    rw [smul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hn0)
  refine ⟨⟨(n : ℚ)⁻¹ ⊗ₜ[ℤ] g, ?_, ?_⟩⟩
  · change Rationalization.comp _ _ _ ((1 : ℚ) ⊗ₜ[ℤ] f) ((n : ℚ)⁻¹ ⊗ₜ[ℤ] g) =
      Rationalization.identity _
    rw [Rationalization.comp_tmul, hfg, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      one_mul, ← Int.cast_smul_eq_zsmul ℚ, hq]
    rfl
  · change Rationalization.comp _ _ _ ((n : ℚ)⁻¹ ⊗ₜ[ℤ] g) ((1 : ℚ) ⊗ₜ[ℤ] f) =
      Rationalization.identity _
    rw [Rationalization.comp_tmul, hgf, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      mul_one, ← Int.cast_smul_eq_zsmul ℚ, hq]
    rfl

end Langlands.CommGroupScheme
