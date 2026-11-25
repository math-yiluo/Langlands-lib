/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree

import all WeilConjectures.AlgebraicGeometry.Tate.TateInverseLimitBaseChangeSupplement

/-! # Universal property of the finite Tate line

Source: blueprint sec-smooth-purity/sk-prop-sp-tower-geometric,
classes (2), evaluation of coefficient extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory Opposite AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

-- A module over the constant residue ring has the canonical normalized scalar action.
private theorem constant_normalized (T : Scheme.{u}) (k : ℕ)
    (M : SheafOfModules.{u + 1} (constantZModRingSheaf (Scheme.ProEt.topology T) k)) :
    IsConstantZModSheafModuleStructure (Scheme.ProEt.topology T) k
      ((SheafOfModules.toSheaf _).obj M)
      (fun V ↦ (inferInstance : Module
        ((constantZModRingSheaf (Scheme.ProEt.topology T) k).obj.obj V) (M.val.obj V))) := by
  constructor
  · intro V z y
    change ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} (ZMod k))))).app V
          (z : ULift.{u + 1} (ZMod k))) • (show M.val.obj V from y) =
            z • (show M.val.obj V from y)
    rw [map_intCast, Int.cast_smul_eq_zsmul]
  · intro V W i b y
    exact M.val.map_smul i b y

-- Normalize each module action on integer sections, then use torsion-sheaf linearity.
private theorem constant_linear (T : Scheme.{u}) (k : ℕ) (hk : 0 < k)
    (M N : SheafOfModules.{u + 1} (constantZModRingSheaf (Scheme.ProEt.topology T) k))
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (U : T.ProEtᵒᵖ) (a : (constantZModRingSheaf (Scheme.ProEt.topology T) k).obj.obj U)
    (x : M.val.obj U) :
    f.hom.app U (a • x) = a • (show N.val.obj U from f.hom.app U x) := by
  exact torsionSheaf_hom_linear (Scheme.ProEt.topology T) k hk
    ((SheafOfModules.toSheaf _).obj M) ((SheafOfModules.toSheaf _).obj N)
    (constantZModModuleSheaf_nsmul _ k hk M)
    (constantZModModuleSheaf_nsmul _ k hk N) f _ _
    (constant_normalized T k M) (constant_normalized T k N) U a x

-- Restriction along the coefficient comparison preserves the underlying additive sheaf.
private theorem transported_linear (T : Scheme.{u}) (k : ℕ) (hk : 0 < k)
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1})
    (e : R ≅ constantZModRingSheaf (Scheme.ProEt.topology T) k)
    (M N : SheafOfModules.{u + 1} R)
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (U : T.ProEtᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U) :
    f.hom.app U (a • x) = a • (show N.val.obj U from f.hom.app U x) := by
  have h := constant_linear T k hk
    ((SheafOfModules.restrictScalars e.inv).obj M)
    ((SheafOfModules.restrictScalars e.inv).obj N) f U (e.hom.hom.app U a) x
  have he : e.inv.hom.app U (e.hom.hom.app U a) = a :=
    congrArg (fun g ↦ g.hom.app U a) e.hom_inv_id
  change f.hom.app U (e.inv.hom.app U (e.hom.hom.app U a) • x) =
    e.inv.hom.app U (e.hom.hom.app U a) • (show N.val.obj U from f.hom.app U x) at h
  simpa only [he] using h

private def forgetHomEquiv (T : Scheme.{u}) (k : ℕ) (hk : 0 < k)
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1})
    (e : R ≅ constantZModRingSheaf (Scheme.ProEt.topology T) k)
    (M N : SheafOfModules.{u + 1} R) :
    (M ⟶ N) ≃ ((SheafOfModules.toSheaf _).obj M ⟶
      (SheafOfModules.toSheaf _).obj N) where
  toFun := (SheafOfModules.toSheaf _).map
  invFun f := ⟨PresheafOfModules.homMk f.hom (transported_linear T k hk R e M N f)⟩
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

/-- The finite Tate line represents additive maps out of the finite roots sheaf.
Source: blueprint classes (2), finite coefficient extension, and Stacks 03EK
(blueprint: lem-sp-finite-tate-line-universal).

Proof: the finite Tate line is the sheafification of the sectionwise tensor
B tensor over ZMod(ell^(n+1)) with the canonical roots module. The
sheafification adjunction followed by the tensor/restriction adjunction identifies
maps from it with linear maps from the roots module to the scalar restriction
of N. The underlying sheaf of the roots module is the actual roots sheaf.
Every additive map from it is linear over the constant ZMod sheaf: locally lift
a scalar to an integer section, use additivity, and descend the equality by
separatedness. This constructs the stated equivalence and its inverse. The
adjunctions are natural for postcomposition. On pure tensors the inverse sends
b tensor z to b times the image of z, which is the displayed scalar formula.
This applies also to the zero coefficient ring and to the empty scheme. -/
theorem finiteTateLine_universal (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (B : Type (u + 1)) [CommRing B] (n : ℕ) (a : ZMod (l ^ (n + 1)) →+* B) :
    ∃ Ψ : ∀ N : SheafOfModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (Scheme.tateFiniteCoefficient T B)),
      (Scheme.tateFiniteLine T l B n a ⟶ N) ≃
        ((roots l T).obj (op n) ⟶ (SheafOfModules.toSheaf _).obj N),
      (∀ {N N'} (f : Scheme.tateFiniteLine T l B n a ⟶ N) (g : N ⟶ N'),
        Ψ N' (f ≫ g) = Ψ N f ≫ (SheafOfModules.toSheaf _).map g) ∧
      (∀ N (f : Scheme.tateFiniteLine T l B n a ⟶ N) (U : T.ProEtᵒᵖ)
        (b : (Scheme.tateFiniteCoefficient T B).obj.obj U)
        (z : ((roots l T).obj (op n)).obj.obj U),
        b • (show N.val.obj U from (Ψ N f).hom.app U z) =
          f.val.app U (Scheme.tateFiniteTensor T l B n a U.unop b z)) := by
  let R := Scheme.purTwistRing T (Scheme.purTwistFiniteRing T l n)
  let c := Scheme.tateFiniteScalar T l B n a
  let M := Scheme.purTwistRootsModule T l n
  let res := SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)
  let Ψ := fun N ↦ (Scheme.tensorHomEquiv T c M N).trans
    (forgetHomEquiv T (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      R (Scheme.purTwistFiniteRingIso T l n) M (res.obj N))
  refine ⟨Ψ, ?_, ?_⟩
  · intro N N' f g
    ext U z
    change (Scheme.tensorHomEquiv T c M N' (f ≫ g)).val.app U z =
      g.val.app U ((Scheme.tensorHomEquiv T c M N f).val.app U z)
    rw [Scheme.tensorHomEquiv_apply, Scheme.tensorHomEquiv_apply]
    rfl
  · intro N f U b z
    exact (Scheme.tensorHomEquiv_tmul T c M N f U b z).symm

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
