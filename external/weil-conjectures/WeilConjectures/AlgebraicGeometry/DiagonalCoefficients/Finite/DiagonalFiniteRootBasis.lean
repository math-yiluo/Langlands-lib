/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sp.SpEllCoefficientTower
import all WeilConjectures.AlgebraicGeometry.Sp.SpRootBasisLevel

/-! # Finite root bases with arbitrary annihilated coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A prescribed cyclic root basis trivializes the internal free module over any
commutative coefficient sheaf annihilated by the same positive ell-power.

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, clause (3), finite root bases.
(blueprint: lem-diagonal-finite-root-basis).

Proof in words. On the prescribed slice, the root module is the constant Z/N
module with the given generator. Tensor its basis with B. The map b -> b tensor 1
from B to B tensor_Z Z/N is bijective because N annihilates B: its inverse is the
Z/N action on B. The constant-presheaf sheafification map and the comparison from
the sectionwise tensor to the sheaf tensor are locally bijective. Their whiskered
composite sends b to b tensor the restricted root generator. This map is B-linear
and locally bijective, hence an isomorphism of module sheaves. The identity-scalar
restriction comparison gives exactly the regular and free internal modules below.
The proof covers zero coefficient sheaves and empty slices. -/
theorem diagonalFiniteRootBasis
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (W : X.ProEt) (n : ℕ)
    (ζ : (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : (SheafOfModules.unit
        (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
      (Scheme.purTwistRootsModule X ℓ n).over W)
    (he : ∀ (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      e.hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op ζ)
    (B : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj B] [IsCommMonObj B]
    (hB : ∀ (V : X.ProEtᵒᵖ) (b : B.obj.obj V), (ℓ ^ (n + 1)) • b = 0) :
    Nonempty ((spRootBasisSliceSections X B W).obj (Mod.regular B) ≅
      (spRootBasisSliceSections X B W).obj
        ((Mod.free B).obj (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))) := by
  let J := Scheme.ProEt.topology X
  let F := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let M := Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))
  let K := Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)
  let S := spRootBasisSliceSections X B W
  let A := S.obj ((Mod.comap (𝟙 B)).obj (Mod.regular B))
  let T := S.obj ((Mod.comap (𝟙 B)).obj ((Mod.free B).obj M))
  let p : A ⟶ T := AlgebraicGeometry.ProEtale.rootTensorInsertion X B B (𝟙 B) W M ζ
  let H := (Over.forget W).op
  let B' := H ⋙ B.obj
  let Z := (Functor.const X.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))
  let κ := Functor.whiskerRight (toSheafify J Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  have hκi : Presheaf.IsLocallyInjective J κ := by
    apply (Presheaf.isLocallyInjective_forget_iff J κ).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (toSheafify J Z) (forget CommRingCat.{u + 1}))
    infer_instance
  have hκs : Presheaf.IsLocallySurjective J κ := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J κ).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J Z) (forget CommRingCat.{u + 1}))
    infer_instance
  have hκ : J.W κ := J.W_of_isLocallyBijective κ
  let j := Functor.whiskerLeft H (B.obj ◁ κ)
  have hji : Presheaf.IsLocallyInjective (J.over W) j := by
    have := (hκ.whiskerLeft B.obj).isLocallyInjective
    exact Presheaf.isLocallyInjective_whisker (J.over W) J (Over.forget W) _
  have hjs : Presheaf.IsLocallySurjective (J.over W) j := by
    have := (hκ.whiskerLeft B.obj).isLocallySurjective
    exact Presheaf.isLocallySurjective_whisker (J.over W) J (Over.forget W) _
  let v := (PresheafOfModules.toPresheaf (K.over W).obj).map e.hom.val
  let k := B' ◁ v
  have hk : IsIso k := by
    have : IsIso e.hom.val := by
      change IsIso ((SheafOfModules.forget (K.over W)).map e.hom)
      infer_instance
    dsimp only [k, v]
    infer_instance
  let tensorMap := Functor.whiskerLeft H (Functor.LaxMonoidal.μ F B M)
  have hμi : Presheaf.IsLocallyInjective (J.over W) tensorMap := by
    have := (AlgebraicGeometry.ProEtale.tensorComparison_mem X B M).isLocallyInjective
    exact Presheaf.isLocallyInjective_whisker (J.over W) J (Over.forget W) _
  have hμs : Presheaf.IsLocallySurjective (J.over W) tensorMap := by
    have := (AlgebraicGeometry.ProEtale.tensorComparison_mem X B M).isLocallySurjective
    exact Presheaf.isLocallySurjective_whisker (J.over W) J (Over.forget W) _
  let a : B' ⟶ H ⋙ (B.obj ⊗ (Z ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        (AlgebraicGeometry.ProEtale.cyclicTensorInsertion.toAddMonoidHom)
      naturality := by
        intro V V' f
        ext b
        rfl }
  have hai : Presheaf.IsLocallyInjective (J.over W) a := by
    apply Presheaf.isLocallyInjective_of_injective
    intro V
    exact (AlgebraicGeometry.ProEtale.cyclicTensorInsertion_bijective
      (hB (op V.unop.left))).1
  have has : Presheaf.IsLocallySurjective (J.over W) a := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro V
    exact (AlgebraicGeometry.ProEtale.cyclicTensorInsertion_bijective
      (hB (op V.unop.left))).2
  have hp : ((SheafOfModules.toSheaf _).map p).hom = a ≫ j ≫ k ≫ tensorMap := by
    ext V b
    have h1 : κ.app (op V.unop.left) (1 : ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))) =
        (1 : K.obj.obj (op V.unop.left)) := by
      exact ((toSheafify J Z).app (op V.unop.left)).hom.map_one
    change (Functor.LaxMonoidal.μ F B M).app (op V.unop.left)
        (b ⊗ₜ[ℤ] M.obj.map V.unop.hom.op ζ) =
      (Functor.LaxMonoidal.μ F B M).app (op V.unop.left)
        (b ⊗ₜ[ℤ] e.hom.val.app V
          (κ.app (op V.unop.left) (1 : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))))
    rw [h1, he, one_smul]
    rfl
  have hpi : Presheaf.IsLocallyInjective (J.over W)
      ((SheafOfModules.toSheaf _).map p).hom := by
    rw [hp]
    infer_instance
  have hps : Presheaf.IsLocallySurjective (J.over W)
      ((SheafOfModules.toSheaf _).map p).hom := by
    rw [hp]
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf _).map p) := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    exact ⟨(Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hpi,
      (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hps⟩
  have : IsIso p := isIso_of_reflects_iso p (SheafOfModules.toSheaf _)
  let c := Mod.comapId B
  exact ⟨(S.mapIso (c.app (Mod.regular B))).symm ≪≫ asIso p ≪≫
    S.mapIso (c.app ((Mod.free B).obj M))⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
