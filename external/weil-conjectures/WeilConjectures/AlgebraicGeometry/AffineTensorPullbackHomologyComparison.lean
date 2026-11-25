/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.AffineTensorPullbackComplexComparison
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-! # Affine tensor and pullback homology comparison

Source: Stacks Project, Tags 01IB and 01I9, and steps 1--2 of
lem-pc-affine-universal-tensor-exact.
(blueprint: lem-pc-affine-tensor-pullback-homology-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The homology of the module tensor complex is the restricted module of sections
of the homology of the affine scheme pullback.
Source: Stacks Project, Tags 01IB and 01I9, and steps 1--2 of
lem-pc-affine-universal-tensor-exact.
(blueprint: lem-pc-affine-tensor-pullback-homology-comparison).

Proof: The complex comparison identifies ordinary scalar extension of the section
complex P, after applying tilde, with the scheme pullback complex. To commute tilde
with homology, first prove it preserves kernels: the kernel of a map between tilde
objects is quasi-coherent; its affine counit presents it as a tilde object. Lift
its kernel inclusion through full faithfulness and reflect the kernel limit cone.
Thus tilde preserves finite limits, while its left adjunction preserves colimits.
The affine unit identifies each module with sections of its tilde. Apply the
homology comparison isomorphisms for tilde and for restriction of scalars, then
apply global sections to the complex comparison. Finally commute the tensor
factors to identify restricted B tensor_A P with P tensor_A B. Compatibility with
differentials is checked by tensor induction, so these isomorphisms give
the asserted isomorphism. No flatness or boundedness is used: the functor applied
to C is ordinary pullback, and the tensor is ordinary tensor, not derived tensor.
For B the zero ring both sides are zero; for C zero or for an empty affine S the
same argument gives the zero isomorphism. -/
theorem affine_tensor_pullback_homology_comparison (S : Scheme.{u}) [IsAffine S]
    (C : CochainComplex S.Modules ℤ)
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] (a : ℤ) :
    Nonempty (
      ((((tensorRight (ModuleCat.of Γ(S, ⊤) B)).mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
          S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤)).mapHomologicalComplex
          (.up ℤ)).obj C)).homology a) ≅
      (ModuleCat.restrictScalars (algebraMap Γ(S, ⊤) B)).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
          ((((Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫
              S.isoSpec.inv)).mapHomologicalComplex
              (.up ℤ)).obj C).homology a))) := by
  let A := Γ(S, ⊤)
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
      S.Modules ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).obj C
  let Q := ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
    (.up ℤ)).obj P
  let T := tilde.functor (CommRingCat.of B)
  let : T.IsLeftAdjoint := (tilde.adjunction (R := CommRingCat.of B)).isLeftAdjoint
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let E := moduleSpecΓFunctor (R := CommRingCat.of B)
  let U := ModuleCat.restrictScalars (algebraMap A B)
  let : E.IsRightAdjoint := (tilde.adjunction (R := CommRingCat.of B)).isRightAdjoint
  let := preservesBinaryBiproducts_of_preservesBinaryProducts E
  let : E.Additive := Functor.additive_of_preservesBinaryBiproducts E
  let tilde_preservesKernel : ∀ {M N : ModuleCat.{u} B} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) T := by
    intro M N f
    let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := CommRingCat.of B)
    let : T.Full := ff.full
    let : T.Faithful := ff.faithful
    have : (T.obj M).IsQuasicoherent := by
      change (tilde.{u} (R := CommRingCat.of B) M).IsQuasicoherent
      infer_instance
    have : (T.obj N).IsQuasicoherent := by
      change (tilde.{u} (R := CommRingCat.of B) N).IsQuasicoherent
      infer_instance
    let k := kernel (T.map f)
    have hk : k.IsQuasicoherent := isQuasicoherent_kernel (T.map f)
    have : IsIso k.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent k
    let e : T.obj (E.obj k) ≅ k := asIso k.fromTildeΓ
    let t := T.preimage (e.hom ≫ kernel.ι (T.map f))
    have ht : t ≫ f = 0 := by
      apply T.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
        Category.assoc, kernel.condition, comp_zero, t]
    let c := KernelFork.ofι t ht
    have hc : IsLimit (c.map T) := by
      apply IsLimit.ofIsoLimit (kernelIsKernel (T.map f))
      exact Fork.ext e.symm (by simp [c, t, KernelFork.map])
    have hc' : IsLimit c := isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
    exact preservesLimit_of_preserves_limit_cone hc'
      ((c.isLimitMapConeEquiv T).symm hc)
  let : ∀ {M N : ModuleCat.{u} B} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) T := tilde_preservesKernel
  let : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesKernels T
  let F := tensorRight (ModuleCat.of A B)
  let RQ := (U.mapHomologicalComplex (.up ℤ)).obj Q
  let B' := U.obj (ModuleCat.of B B)
  let eB : B ≃ₗ[A] B' :=
    { toFun := fun b ↦ b
      invFun := fun b ↦ b
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r b ↦ Algebra.smul_def r b
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e₀ (n : ℤ) : ((F.mapHomologicalComplex (.up ℤ)).obj P).X n ≅ RQ.X n :=
    ((TensorProduct.comm A (P.X n) B).trans
      (TensorProduct.congr eB (LinearEquiv.refl A (P.X n)))).toModuleIso
  let e : (F.mapHomologicalComplex (.up ℤ)).obj P ≅ RQ :=
    HomologicalComplex.Hom.isoOfComponents e₀ (by
      intro i j hij
      ext x
      induction x using TensorProduct.inductionOn with
      | tmul x b => rfl
      | add x y hx hy =>
        simp only [ModuleCat.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy])
  obtain ⟨e₁⟩ := affine_tensor_pullback_complex_comparison S C hqc B
  let hT := (T.mapHomologicalComplexHomologyIso (.up ℤ) a).app Q
  let hU := (U.mapHomologicalComplexHomologyIso (.up ℤ) a).app Q
  let unit := (tilde.toTildeΓNatIso (R := CommRingCat.of B)).app (Q.homology a)
  exact ⟨(HomologicalComplex.homologyFunctor _ (.up ℤ) a).mapIso e ≪≫ hU ≪≫
    U.mapIso (unit ≪≫ E.mapIso hT.symm ≪≫
      E.mapIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) a).mapIso e₁))⟩

end AlgebraicGeometry.Scheme.Modules
