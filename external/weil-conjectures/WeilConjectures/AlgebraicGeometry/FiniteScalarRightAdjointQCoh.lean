/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent
import WeilConjectures.AlgebraicGeometry.SheafAlgebraDerivedHomAdjunction
import WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Quasi-coherence of a specified finite scalar right adjoint

Source: Stacks Project, Tag 0AX2, comparison of right adjoints
(blueprint: lem-sc-finite-scalar-right-adjoint-qcoh).
-/

@[expose] public section

universe u wX wY wA

open CategoryTheory

namespace AlgebraicGeometry

-- Pushforward from Over U is faithful: every V over U is isomorphic to U × V.
-- Compose it with the faithful degree-zero embedding to shrink the local Hom types.
private theorem openModuleLocallySmall (Y : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) :
    LocallySmall.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) := by
  let R := moduleRings Y.toRingedSpace
  let P := SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := R) U)
  have : P.Faithful := by
    constructor
    intro M N a b hab
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    let V := W.unop
    let e : (Over.star U).obj V.left ≅ V :=
      { hom := Over.homMk Limits.prod.snd
        inv := Over.homMk (Limits.prod.lift V.hom (𝟙 V.left))
        hom_inv_id := by ext; apply Subsingleton.elim
        inv_hom_id := by ext; apply Subsingleton.elim }
    have h :
        ((PresheafOfModules.toPresheaf _).map a.val).app
          (Opposite.op ((Over.star U).obj V.left)) =
        ((PresheafOfModules.toPresheaf _).map b.val).app (Opposite.op ((Over.star U).obj V.left)) :=
      congrArg (fun g => ((PresheafOfModules.toPresheaf _).map g.val).app (Opposite.op V.left)) hab
    have hh : ((PresheafOfModules.toPresheaf _).map a.val).app W =
        ((PresheafOfModules.toPresheaf _).map b.val).app W := by
      have : IsIso e.hom := Iso.isIso_hom e
      have : IsIso e.hom.op := inferInstance
      have : IsIso (N.val.presheaf.map e.hom.op) := inferInstance
      apply (cancel_mono (N.val.presheaf.map e.hom.op)).1
      calc
        _ = M.val.presheaf.map e.hom.op ≫
            ((PresheafOfModules.toPresheaf _).map a.val).app _ :=
          (((PresheafOfModules.toPresheaf _).map a.val).naturality e.hom.op).symm
        _ = M.val.presheaf.map e.hom.op ≫
            ((PresheafOfModules.toPresheaf _).map b.val).app _ := by rw [h]
        _ = _ := ((PresheafOfModules.toPresheaf _).map b.val).naturality e.hom.op
    ext x
    exact congrArg (fun g => g.hom x) hh
  exact locallySmall_of_faithful.{wY}
    (P ⋙ DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0)

/-- Any specified right adjoint of derived scalar restriction has quasi-coherent
cohomology at a bounded-below quasi-coherent input.
Source: Stacks Project, Tag 0AX2, with Tags 0BV0 and 0AX3
(blueprint: lem-sc-finite-scalar-right-adjoint-qcoh).

Proof: Construct the direct-image algebra B with structure map f.c. On each open U,
local module pushforward is faithful, since an open V contained in U is isomorphic
to U × V. Composing it with the faithful degree-zero embedding into D(O_Y) proves
local smallness in the specified morphism universe. K-injective resolutions then
construct the local derived categories required by finite_pushforward_derivedHom_qcoherent.
That theorem gives quasi-coherence of B and of the constructed algebra-valued derived
Hom after restriction of scalars. The adjunction sheafAlgebraDerivedHom_adjunction
identifies this explicit derived Hom as a right adjoint of the specified left functor.
Uniqueness of right adjoints gives an isomorphism to rhoR. For each integer n,
quasiCoherent_iff_restrictScalars converts the underlying O_Y-module quasi-coherence
of the nth cohomology sheaf to B-module quasi-coherence. Apply the homology functor to
the right-adjoint isomorphism and transport quasi-coherence. No output bound must be
chosen or transported. Empty schemes, zero objects and shifts obey the same argument. -/
theorem finite_scalar_right_adjoint_qcoh {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (ρR : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
    (adjA : (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ ρR)
    (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n) :
    directImageAlgebraDerivedQCohProperty f (ρR.obj K.obj) := by
  let B : Y.CommAlgebraSheaf := Under.mk (⟨f.c⟩ : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)
  let : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := by
    change HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    infer_instance
  let : ∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) := fun U => by
    have := openModuleLocallySmall Y U
    let : IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) :=
      SheafOfModules.isGrothendieckAbelian _
    exact HasDerivedCategory.ofHasKInjectiveResolutions _
  obtain ⟨hB, _, hq, _, _⟩ := finite_pushforward_derivedHom_qcoherent f B rfl K hK
  obtain ⟨adjH⟩ := sheafAlgebraDerivedHom_adjunction Y B hB
  let e := (adjA.rightAdjointUniq adjH).app K.obj
  intro n
  apply (SheafOfModules.isQuasicoherent
    (moduleRings (directImageAlgebraSpace f))).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e.symm)
  exact (Scheme.Modules.quasiCoherent_iff_restrictScalars Y B hB _).mpr (hq.2 n)

end AlgebraicGeometry
