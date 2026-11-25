/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE

/-!
# Tor amplitude of bounded below complexes of abelian groups

If every object of `C` has a flat resolution of length one, every object `K` of `D(C)` vanishing
in degrees `< b` has Tor amplitude in `[b - 1, ∞)`
(`DerivedCategory.torAmplitudeGE_of_isGE_of_flat_resolution`). This applies to modules over a
principal ideal domain
(`DerivedCategory.torAmplitudeGE_of_isGE_of_isPrincipalIdealRing`), for instance abelian groups,
that is modules over `ULift ℤ` (`DerivedCategory.torAmplitudeGE_of_isGE_int`): a module is a
quotient of a free module by a submodule, which is torsion free, hence flat over the principal
ideal domain.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- If every object of `C` is the cokernel of a monomorphism between flat objects, an object of
`D(C)` vanishing in degrees `< b` has Tor amplitude in `[b - 1, ∞)`: for `0 ⟶ F₁ ⟶ F₀ ⟶ F ⟶ 0`
with `F₀`, `F₁` flat, `K ⊗ᴸ F[0]` is an extension of `(K ⊗ᴸ F₁[0])[1]` by `K ⊗ᴸ F₀[0]`. -/
lemma torAmplitudeGE_of_isGE_of_flat_resolution
    (hC : ∀ F : C, ∃ S : ShortComplex C, S.ShortExact ∧ ObjectProperty.flat S.X₁ ∧
      ObjectProperty.flat S.X₂ ∧ Nonempty (S.X₃ ≅ F))
    (K : DerivedCategory C) (b : ℤ) [K.IsGE b] : torAmplitudeGE C (b - 1) K := fun F ↦ by
  obtain ⟨S, hS, h₁, h₂, ⟨e⟩⟩ := hC F
  have hT := Pretriangulated.rot_of_distTriang _
    (((curriedTensor (DerivedCategory C)).obj K).map_distinguished _
      hS.singleTriangle_distinguished)
  have hK (X : C) (hX : ObjectProperty.flat X) : (K ⊗ (singleFunctor C 0).obj X).IsGE b := by
    have := isGE_tensor_of_torAmplitudeGE_right
      (torAmplitudeGE_of_torAmplitudeIn (torAmplitudeIn_singleFunctor_obj_of_flat hX)) K b
    rwa [add_zero] at this
  have h₁' := hK _ h₁
  have h₂' := hK _ h₂
  have : TStructure.t.IsGE ((K ⊗ (singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧) (b - 1) :=
    TStructure.t.isGE_shift _ b 1 (b - 1) (by lia)
  have : TStructure.t.IsGE (K ⊗ (singleFunctor C 0).obj S.X₃) (b - 1) :=
    TStructure.t.isGE₂ _ hT (b - 1)
      (TStructure.t.isGE_of_ge (K ⊗ (singleFunctor C 0).obj S.X₂) (b - 1) b (by lia)) this
  exact TStructure.t.isGE_of_iso (whiskerLeftIso K ((singleFunctor C 0).mapIso e)) (b - 1)

end

attribute [local instance] IsPrincipalIdealRing.isDedekindDomain in
/-- Over a principal ideal domain `R`, every bounded below complex of modules vanishing in degrees
`< b` has Tor amplitude in `[b - 1, ∞)`: every module is the quotient of a free module by a
torsion free, hence flat, submodule. -/
lemma torAmplitudeGE_of_isGE_of_isPrincipalIdealRing {R : Type (u + 1)} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [HasDerivedCategory.{w} (ModuleCat.{u + 1} R)]
    (K : DerivedCategory (ModuleCat.{u + 1} R)) (b : ℤ) [K.IsGE b] :
    torAmplitudeGE (ModuleCat.{u + 1} R) (b - 1) K := by
  refine torAmplitudeGE_of_isGE_of_flat_resolution (fun F ↦ ?_) K b
  let π : (F →₀ R) →ₗ[R] F := Finsupp.linearCombination R id
  have hπ : Function.Surjective π := fun x ↦ ⟨Finsupp.single x 1, by simp [π]⟩
  let S : ShortComplex (ModuleCat.{u + 1} R) :=
    ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker π).subtype) (ModuleCat.ofHom π) (by
      ext x
      simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
        (LinearMap.exact_subtype_ker_map π)
      mono_f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
      epi_g := (ModuleCat.epi_iff_surjective _).2 hπ }
  have : Module.IsTorsionFree R (LinearMap.ker π) :=
    Function.Injective.moduleIsTorsionFree _ Subtype.val_injective (fun _ _ ↦ rfl)
  exact ⟨S, hS, (ModuleCat.flat_iff_flat _).2 (inferInstanceAs (Module.Flat R (LinearMap.ker π))),
    (ModuleCat.flat_iff_flat _).2 (inferInstanceAs (Module.Flat R (F →₀ R))), ⟨Iso.refl _⟩⟩

/-- Every bounded below complex of abelian groups (modules over `ULift ℤ`) vanishing in degrees
`< b` has Tor amplitude in `[b - 1, ∞)`. -/
lemma torAmplitudeGE_of_isGE_int
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))]
    (K : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (b : ℤ) [K.IsGE b] :
    torAmplitudeGE (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) (b - 1) K :=
  have : IsDomain (ULift.{u + 1} ℤ) := MulEquiv.isDomain ℤ ULift.ringEquiv.toMulEquiv
  have : IsPrincipalIdealRing (ULift.{u + 1} ℤ) :=
    IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm.toRingHom
      ULift.ringEquiv.symm.surjective
  torAmplitudeGE_of_isGE_of_isPrincipalIdealRing K b

end DerivedCategory
