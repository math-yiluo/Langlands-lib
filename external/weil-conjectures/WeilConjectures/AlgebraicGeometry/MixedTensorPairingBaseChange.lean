/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport
import WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChangeNaturality

/-! # Base change preserves the direct-image tensor pairing
Source: Stacks Project, cohomology.tex Tag 08I3 and Remark 08HY;
duality.tex Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-tensor-pairing-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The direct-image tensor pairing, constructed by transposing the tensor of counits.
Source: Stacks Project, cohomology.tex Tag 079U and Remark 08HY.
(blueprint: def-sc-mixed-direct-image-tensor-pairing). -/
def mixedDirectImageTensorPairing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : schemeDerivedCategory X) :
    (schemeDerivedDirectImage f).obj A ⊗ (schemeDerivedDirectImage f).obj B ⟶
      (schemeDerivedDirectImage f).obj (A ⊗ B) :=
  (schemeHomPullbackAdjunction f).homEquiv _ _
    ((mixedHomTensorPullbackIso f).hom.app
      ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      ((schemeHomPullbackAdjunction f).counit.app A ⊗ₘ
        (schemeHomPullbackAdjunction f).counit.app B))

/-- Base change transports an arbitrary tensor pairing. This is independent of internal
Hom: `a` is any morphism from a tensor product, with no closed structure involved.
Source: Stacks Project, cohomology.tex Tag 08I3 and Remark 08HY;
duality.tex Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-tensor-pairing-base-change).

Proof: first take a to be the identity on A tensor B and transpose under the f'
pullback/direct-image adjunction. Expand both base-change components by Remark 08HY.
Naturality of the f' counit and its triangle identity remove the f' unit-counit pairs.
The tensor of the two remaining f counits agrees with the f counit used in the
right-adjoint tensor pairing, by its definition. The remaining identity states that
pullback-composition comparisons preserve the normalized tensorators. On K-flat
representatives this is the ordinary module pullback-composition tensor identity:
both composites send a pure tensor of sections to the tensor of the same two
pulled-back sections. The normalization equations for the tensorators and the
composition comparisons, and the invertible K-flat derived counits, transport the
identity to the derived category. K-flat resolutions and naturality extend it to
arbitrary A and B. Finally postcompose with direct image of pulled-back a. Naturality
of the base-change mate in A tensor B moves a to the right side, and functoriality
gives the stated identity. No base-change morphism is cancelled or assumed invertible. -/
theorem mixedTensorPairing_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (A B C : schemeDerivedCategory X) (a : A ⊗ B ⟶ C) :
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition A ⊗ₘ
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition B) ≫
      mixedDirectImageTensorPairing (pullback.snd f g)
        ((derivedPullback (pullback.fst f g)).obj A)
        ((derivedPullback (pullback.fst f g)).obj B) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (A, B) ≫
          (derivedPullback (pullback.fst f g)).map a) =
    (mixedHomTensorPullbackIso g).inv.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      (derivedPullback g).map
        (mixedDirectImageTensorPairing f A B ≫ (schemeDerivedDirectImage f).map a) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition C := by
  have h :
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition A ⊗ₘ
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition B) ≫
      mixedDirectImageTensorPairing (pullback.snd f g)
        ((derivedPullback (pullback.fst f g)).obj A)
        ((derivedPullback (pullback.fst f g)).obj B) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (A, B)) =
    (mixedHomTensorPullbackIso g).inv.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      (derivedPullback g).map
        (mixedDirectImageTensorPairing f A B) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (A ⊗ B) := by
    exact mixedTensorPairing_baseChange_identity f g A B
  have ha := congrArg
    (fun z ↦ z ≫ (schemeDerivedDirectImage (pullback.snd f g)).map
      ((derivedPullback (pullback.fst f g)).map a)) h
  simpa only [Functor.map_comp, Category.assoc,
    mixedTensorPairing_baseChange_naturality] using ha


end AlgebraicGeometry
