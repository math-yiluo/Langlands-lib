import Langlands.Geometry.FormalGroup.IsogenyKernelTorsion
import Langlands.Geometry.FormalGroup.KernelTorsor
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Actual isogenies from scalar composites -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {f : Hom M N} {g : Hom N M}

/-- Translation identifies the base change of the composite kernel with the
zero fibre times the cover, given a corepresentation of the second kernel. -/
private theorem fibreMap_flat_of_corepresentation
    (C : FiniteKernelModel (g.comp f)) {L B : CommAlgCat.{v} R}
    (e : g.kernelSetFunctor.CorepresentableBy L) (β : L ⟶ B)
    (η : (g.comp f).kernelPoints B)
    (hη : f.onAlgebraPoints η.val = (e.homEquiv β).val) (hβ : β.hom.Flat) :
    (KernelTorsor.fibreMap C (f := g) (g := f) rfl η).hom.Flat := by
  let compEq : g.comp f = g.comp f := rfl
  let image : L ⟶ C.coordinateAlgebra :=
    e.homEquiv.symm ⟨f.onAlgebraPoints C.universalPoint.val, by
      change g.onAlgebraPoints (f.onAlgebraPoints C.universalPoint.val) = 0
      rw [← onAlgebraPoints_comp]
      exact C.universalPoint.property⟩
  have image_apply {A : CommAlgCat.{v} R} (c : C.coordinateAlgebra ⟶ A) :
      (e.homEquiv (image ≫ c)).val = f.onAlgebraPoints (C.represents.homEquiv c).val := by
    rw [e.homEquiv_comp]
    change N.algebraMapPoints c.hom
      (e.homEquiv (e.homEquiv.symm ⟨f.onAlgebraPoints C.universalPoint.val, _⟩)).val = _
    erw [Equiv.apply_symm_apply]
    rw [f.onAlgebraPoints_natural, C.universalPoint_map]
  let fibre := KernelTorsor.fibreMap C compEq η
  have hs : image ≫ fibre = β ≫ KernelTorsor.tensorInr C := by
    apply e.homEquiv.injective
    apply Subtype.ext
    rw [image_apply, e.homEquiv_comp]
    change f.onAlgebraPoints (C.represents.homEquiv
      (C.represents.homEquiv.symm (KernelTorsor.translatePoint C compEq η
        (KernelTorsor.tensorInl C) (KernelTorsor.tensorInr C)))).val = _
    erw [Equiv.apply_symm_apply]
    change f.onAlgebraPoints
      (((KernelTorsor.quotientRepresents C compEq).homEquiv (KernelTorsor.tensorInl C)).val +
        M.algebraMapPoints (KernelTorsor.tensorInr C).hom η.val) = _
    rw [map_add, ((KernelTorsor.quotientRepresents C compEq).homEquiv
      (KernelTorsor.tensorInl C)).property, zero_add, ← f.onAlgebraPoints_natural, hη]
    rfl
  let untranslate {A : CommAlgCat.{v} R} (c : C.coordinateAlgebra ⟶ A) (b : B ⟶ A)
      (hc : image ≫ c = β ≫ b) : KernelQuotient.coordinateAlgebra C f ⟶ A :=
    (KernelTorsor.quotientRepresents C compEq).homEquiv.symm
      ⟨(C.represents.homEquiv c).val - M.algebraMapPoints b.hom η.val, by
        change f.onAlgebraPoints
          ((C.represents.homEquiv c).val - M.algebraMapPoints b.hom η.val) = 0
        erw [map_sub, ← image_apply c, hc, e.homEquiv_comp, ← f.onAlgebraPoints_natural, hη]
        exact sub_self _⟩
  have translate_untranslate {A : CommAlgCat.{v} R} (c : C.coordinateAlgebra ⟶ A) (b : B ⟶ A)
      (hc : image ≫ c = β ≫ b) :
      KernelTorsor.translateMap C compEq η (untranslate c b hc) b = c := by
    apply C.represents.homEquiv.injective
    change C.represents.homEquiv (C.represents.homEquiv.symm
      (KernelTorsor.translatePoint C compEq η (untranslate c b hc) b)) = _
    erw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change ((KernelTorsor.quotientRepresents C compEq).homEquiv
      ((KernelTorsor.quotientRepresents C compEq).homEquiv.symm
        ⟨(C.represents.homEquiv c).val - M.algebraMapPoints b.hom η.val, _⟩)).val +
      M.algebraMapPoints b.hom η.val = _
    erw [Equiv.apply_symm_apply]
    exact sub_add_cancel _ _
  have hpush : IsPushout image β fibre (KernelTorsor.tensorInr C) := by
    apply IsPushout.of_isColimit (c := PushoutCocone.mk fibre (KernelTorsor.tensorInr C) hs)
    refine PushoutCocone.IsColimit.mk hs
      (fun s => KernelTorsor.tensorDesc C (untranslate s.inl s.inr s.condition) s.inr) ?_ ?_ ?_
    · intro s
      dsimp only [fibre, KernelTorsor.fibreMap]
      rw [KernelTorsor.translateMap_comp, KernelTorsor.tensorInl_desc, KernelTorsor.tensorInr_desc]
      exact translate_untranslate s.inl s.inr s.condition
    · intro s
      exact KernelTorsor.tensorInr_desc C _ _
    · intro s m hm₁ hm₂
      apply KernelTorsor.tensor_hom_ext C
      · rw [KernelTorsor.tensorInl_desc]
        apply KernelTorsor.translateMap_injective C compEq η s.inr
        dsimp only
        rw [translate_untranslate s.inl s.inr s.condition, ← hm₂,
          ← KernelTorsor.translateMap_comp]
        exact hm₁
      · rw [KernelTorsor.tensorInr_desc]
        exact hm₂
  let : PreservesColimitsOfShape WalkingSpan (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}) := by
    change PreservesColimitsOfShape WalkingSpan
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R))
    infer_instance
  exact CommRingCat.flat.of_isPushout
    (hpush.map (forget₂ (CommAlgCat.{v} R) CommRingCat.{v})) hβ

/-- Two maps with both composites equal to the corresponding scalar power
give actual isogenies between scalar-divisible formal modules. -/
theorem isIsogeny_of_scalarComposites_overRing {π : O} (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {j : ℕ} (hgf : g.comp f = M.scalarHom (π ^ j)) (hfg : f.comp g = N.scalarHom (π ^ j)) :
    f.IsIsogeny := by
  have hf := isFppfLocallySurjective_of_comp_eq_scalarHom hN g f j hfg
  refine ⟨hf, ?_⟩
  obtain ⟨C⟩ : (g.comp f).HasFiniteLocallyFreeKernel := hgf ▸ hM.scalarPower_finiteKernel j
  obtain ⟨D⟩ := hN.scalarPower_finiteKernel j
  let K := KernelQuotient.coordinateAlgebra C f
  let L := KernelQuotient.coordinateAlgebra D g
  let eK : f.kernelSetFunctor.CorepresentableBy K := KernelTorsor.quotientRepresents C (f := g) rfl
  let eL : g.kernelSetFunctor.CorepresentableBy L := KernelTorsor.quotientRepresents D hfg
  obtain ⟨B, β, hβ, -, x, hx⟩ := hf L (eL.homEquiv (𝟙 L)).val
  have hη : f.onAlgebraPoints x = (eL.homEquiv β).val := by
    rw [hx]
    exact (congrArg Subtype.val (eL.homEquiv_eq β)).symm
  let η : (g.comp f).kernelPoints B := ⟨x, by
    change (g.comp f).onAlgebraPoints x = 0
    rw [onAlgebraPoints_comp, hη]
    exact (eL.homEquiv β).property⟩
  let T := KernelTorsor.tensorAlgebra C f B
  let θ : C.coordinateAlgebra ⟶ T := KernelTorsor.fibreMap C (f := g) rfl η
  have hθ : θ.hom.Flat := fibreMap_flat_of_corepresentation C eL β η hη hβ.flat
  have : Module.Flat R T := by
    apply RingHom.flat_algebraMap_iff.mp
    have he : θ.hom.toRingHom.comp (algebraMap R C.coordinateAlgebra) = algebraMap R T :=
      RingHom.ext θ.hom.commutes
    rw [← he]
    exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) hθ
  -- The zero point of the first kernel splits the inclusion of the cover.
  let zeroK : K ⟶ B := eK.homEquiv.symm ⟨0, map_zero _⟩
  have : Module.Flat R B := by
    let i : B ⟶ T := KernelTorsor.tensorInr C
    let r : T ⟶ B := KernelTorsor.tensorDesc C zeroK (𝟙 B)
    have hr : i ≫ r = 𝟙 B := KernelTorsor.tensorInr_desc C _ _
    apply Module.Flat.of_retract i.hom.toLinearMap r.hom.toLinearMap
    exact congrArg (fun φ : B ⟶ B => φ.hom.toLinearMap) hr
  -- The zero point of the second kernel lifts every base prime to its spectrum.
  let zeroL : L ⟶ CommAlgCat.of R R := eL.homEquiv.symm ⟨0, map_zero _⟩
  have : Module.FaithfullyFlat R B := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    obtain ⟨q, hq⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hβ).2
      (p.comap zeroL.hom.toRingHom)
    refine ⟨q, ?_⟩
    have hB : β.hom.toRingHom.comp (algebraMap R L) = algebraMap R B :=
      RingHom.ext β.hom.commutes
    have hL : zeroL.hom.toRingHom.comp (algebraMap R L) = RingHom.id R :=
      RingHom.ext zeroL.hom.commutes
    rw [← hB, PrimeSpectrum.comap_comp_apply, hq, ← PrimeSpectrum.comap_comp_apply,
      hL, PrimeSpectrum.comap_id]
  have : Module.Flat R K := by
    let : Module.Flat R (K ⊗[R] B) := ‹Module.Flat R T›
    let : Module.Flat R (B ⊗[R] K) :=
      Module.Flat.of_linearEquiv (TensorProduct.comm R B K)
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro X Y _ _ _ _ a ha
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective R B]
    have he : LinearMap.lTensor B (LinearMap.lTensor K a) =
        (TensorProduct.assoc R B K Y).toLinearMap ∘ₗ
          LinearMap.lTensor (B ⊗[R] K) a ∘ₗ
            (TensorProduct.assoc R B K X).symm.toLinearMap := by
      ext
      rfl
    rw [he]
    exact (TensorProduct.assoc R B K Y).injective.comp
      ((Module.Flat.lTensor_preserves_injective_linearMap a ha).comp
        (TensorProduct.assoc R B K X).symm.injective)
  let := KernelQuotient.finitePresentation C f
  exact ⟨{
    coordinateAlgebra := K
    finite := inferInstance
    projective := Module.Flat.projective_of_finitePresentation
    represents := eK }⟩

end Langlands.FormalGroup.ModuleLaw.Hom
