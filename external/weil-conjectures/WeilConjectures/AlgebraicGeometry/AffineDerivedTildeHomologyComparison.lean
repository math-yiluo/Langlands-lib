/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Cohomology of the derived affine associated-sheaf functor

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5.
(blueprint: new-affine-derived-tilde-homology-comparison).
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

private theorem tilde_preservesKernel (A : Type u) [CommRing A]
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    Limits.PreservesLimit (Limits.parallelPair f 0) (tilde.functor (.of A)) := by
  let T := tilde.functor (.of A)
  let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
  let : T.Full := ff.full
  let : T.Faithful := ff.faithful
  let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  have : (T.obj M).IsQuasicoherent := by
    change (tilde.{u} (R := .of A) M).IsQuasicoherent
    infer_instance
  have : (T.obj N).IsQuasicoherent := by
    change (tilde.{u} (R := .of A) N).IsQuasicoherent
    infer_instance
  let k := Limits.kernel (T.map f)
  have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
  have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
  let e : T.obj ((moduleSpecΓFunctor (R := .of A)).obj k) ≅ k :=
    asIso (Scheme.Modules.fromTildeΓ (R := .of A) k)
  let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map f))
  have ht : t ≫ f = 0 := by
    apply T.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
      Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
  let c := Limits.KernelFork.ofι t ht
  have hc : Limits.IsLimit (c.map T) := by
    apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map f))
    exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
  have hc' : Limits.IsLimit c :=
    Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
  exact Limits.preservesLimit_of_preserves_limit_cone hc'
    ((c.isLimitMapConeEquiv T).symm hc)

/-- Derived associated sheaf commutes with cohomology, naturally in the derived object.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5 (exactness of associated sheaf).
(blueprint: new-affine-derived-tilde-homology-comparison).

Proof: The kernel of a map between associated sheaves is quasi-coherent, by
Scheme.Modules.isQuasicoherent_kernel. Its ordinary counit is therefore invertible.
Use full faithfulness of tilde to lift this kernel fork to modules. Its image is a
limit fork, so full faithfulness reflects that it is a limit; hence tilde preserves
kernels. The additive left adjoint tilde also preserves colimits, so it is exact.
The universal property of Q descends the given comparison to an isomorphism between
F followed by inclusion and tilde.mapDerivedCategory. Whisker this with cohomology
and compose with Functor.mapDerivedCategoryHomologyFunctorIso. All comparisons are
natural; this works in every integer degree and for arbitrary rings, including zero.
-/
theorem affineDerivedTilde_homology_comparison (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (hF : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q))
    (n : ℤ) :
    Nonempty ((F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙ tilde.functor (.of A)) := by
  let T : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
    tilde.functor (.of A)
  let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N),
      Limits.PreservesLimit (Limits.parallelPair f 0) T :=
    fun {_ _} f ↦ tilde_preservesKernel A f
  let : Limits.PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesKernels T
  obtain ⟨α⟩ := hF
  let e : F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι ≅ T.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (DerivedCategory.Q ⋙ F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι)
      (T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι) T.mapDerivedCategory α
  exact ⟨Functor.isoWhiskerRight e _ ≪≫ (T.mapDerivedCategoryHomologyFunctorIso n).symm⟩

end AlgebraicGeometry
