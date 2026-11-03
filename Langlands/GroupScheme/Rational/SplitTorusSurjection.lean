import Langlands.Geometry.Building.RealTorusDuality
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Real cocharacter surjectivity for actual fppf maps of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An epimorphism of underlying schemes induces injective restriction on
actual integral characters. -/
theorem characterRestrict_injective_of_epi (f : A ⟶ T)
    [Epi (CommGroupScheme.groupHom f).hom.hom.left] :
    Function.Injective (characterRestrict (CommGroupScheme.groupHom f)) := by
  intro χ ψ h
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_epi (CommGroupScheme.groupHom f).hom.hom.left).mp
    (congrArg (fun z : rationalCharacters A.toGrp => z.toMul.hom.hom.left) h)

/-- Restriction on real characters is injective along an epimorphism of
underlying schemes. -/
theorem rationalCharacterRestrictReal_injective_of_epi (f : A ⟶ T)
    [Epi (CommGroupScheme.groupHom f).hom.hom.left] :
    Function.Injective (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)) := by
  simpa only [rationalCharacterRestrictReal, LinearMap.baseChange_eq_ltensor] using
    Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
      (characterRestrict (CommGroupScheme.groupHom f)).toIntLinearMap
      (characterRestrict_injective_of_epi f)

/-- An epimorphism of underlying schemes between split tori is surjective on
real cocharacters. -/
theorem cocharacterMapReal_surjective_of_epi (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    [Epi (CommGroupScheme.groupHom f).hom.hom.left] :
    Function.Surjective (cocharacterMapReal f) := by
  apply LinearMap.dualMap_injective_iff.mp
  intro φ ψ h
  obtain ⟨x, rfl⟩ := (characterDualEquiv hT).surjective φ
  obtain ⟨y, rfl⟩ := (characterDualEquiv hT).surjective ψ
  apply congrArg (characterDualEquiv hT)
  apply rationalCharacterRestrictReal_injective_of_epi f
  apply (characterDualEquiv hA).injective
  apply LinearMap.ext
  intro v
  change pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x) v =
    pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y) v
  rw [← pair_cocharacterMapReal, ← pair_cocharacterMapReal]
  exact congrArg (fun l : Module.Dual ℝ (V A) => l v) h

/-- An actual fppf covering map of split tori is surjective on real
cocharacters, without any finite-kernel or integral-surjectivity premise. -/
theorem cocharacterMapReal_surjective_of_fppf (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    [Flat (CommGroupScheme.groupHom f).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom f).hom.hom.left]
    [LocallyOfFinitePresentation (CommGroupScheme.groupHom f).hom.hom.left] :
    Function.Surjective (cocharacterMapReal f) :=
  cocharacterMapReal_surjective_of_epi hA hT f

/-- The quotient of the actual source real cocharacter space by the actual
real kernel of an fppf map of split tori. -/
def cocharacterQuotientEquivOfFppf (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    [Flat (CommGroupScheme.groupHom f).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom f).hom.hom.left]
    [LocallyOfFinitePresentation (CommGroupScheme.groupHom f).hom.hom.left] :
    (V A ⧸ (cocharacterMapReal f).ker) ≃ₗ[ℝ] V T :=
  (cocharacterMapReal f).quotKerEquivOfSurjective
    (cocharacterMapReal_surjective_of_fppf hA hT f)

/-- The quotient equivalence is induced by the actual torus morphism. -/
@[simp] theorem cocharacterQuotientEquivOfFppf_mk (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    [Flat (CommGroupScheme.groupHom f).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom f).hom.hom.left]
    [LocallyOfFinitePresentation (CommGroupScheme.groupHom f).hom.hom.left] (v : V A) :
    cocharacterQuotientEquivOfFppf hA hT f (Submodule.Quotient.mk v) =
      cocharacterMapReal f v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

end Langlands.GroupScheme.RealTorusSpace
