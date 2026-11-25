/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.RingTheory.ConormalExteriorModule

/-! # Constant affine sections followed by tensor pullback

Source: Stacks Project, Tags 01I6 and 0096.
(blueprint: new-t2-self-tor-affine-section). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Explicit restriction and tensor-pullback objects require more elaboration fuel.
/-- Send an algebraic element to the associated sheaf on its chart, extend it by
pushforward, and apply the canonical tensor-pullback unit.
Source: Stacks Project, Tags 01I6 and 0096.
(blueprint: new-t2-self-tor-affine-section). -/
noncomputable def selfTorAffineSection {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (m : M) :
    (((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i).obj M).val.obj
        (op (i ⁻¹ᵁ U.1))) := by
  let L := (tilde.functor Γ(Y, U.1)).obj M
  let W := U.1.ι ⁻¹ᵁ U.1
  let B := (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj L
  let C := (Scheme.Modules.pushforward U.1.ι).obj B
  let a : L.val.obj (op (U.2.isoSpec.hom ''ᵁ W)) :=
    L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app M) m)
  exact ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    C).val.app (op U.1) ((Scheme.Modules.restrictAppIso U.2.isoSpec.hom L W).inv a)

/-- The ideal element represented by a kernel section on an affine chart.
Source: Stacks Project, Tag 01R3.
(blueprint: new-t2-self-tor-affine-section). -/
noncomputable def selfTorIdealSection {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) (b : i.ker.toModules.val.obj (op U.1)) : i.ker.ideal U :=
  ⟨i.ker.toModulesι.app U.1 b, by
    have hm : i.ker.toModulesι.app U.1 b ∈ Set.range (i.ker.toModulesι.app U.1) :=
      ⟨b, rfl⟩
    rw [i.ker.range_toModulesι_app U] at hm
    exact hm⟩

/-- The pure conormal wedge of a tuple of actual ideal sections.
Source: Stacks Project, Tags 01R3 and 09PQ.
(blueprint: new-t2-self-tor-affine-section). -/
noncomputable def selfTorIdealWedge {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) (n : ℕ) (b : Fin n → i.ker.toModules.val.obj (op U.1)) :
    conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n :=
  exteriorPower.ιMulti ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U) n
    (fun j ↦ (i.ker.ideal U).toCotangent (selfTorIdealSection i U (b j)))

/-- Applying an affine module map to its constant section gives the constant section
of the image element.
Source: Stacks Project, Tags 01I6 and 0096.
(blueprint: new-t2-self-tor-affine-section).
Proof: Naturality of the tilde adjunction unit, of the sheaf module map, and of the
canonical tensor-pullback adjunction unit. -/
theorem selfTorAffineSection_map {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) {M P : ModuleCat.{u} (Γ(Y, U.1) : Type u)}
    (a : M ⟶ P) (m : M) :
    ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i).map a).val.app
        (op (i ⁻¹ᵁ U.1)) (selfTorAffineSection i U M m) =
      selfTorAffineSection i U P (a m) := by
  let L := tilde.functor Γ(Y, U.1)
  let F := L ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
    Scheme.Modules.pushforward U.1.ι
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit
  have hη := congrArg (fun q ↦ q.val.app (op U.1)) (η.naturality (F.map a))
  have ht := congrArg (fun q ↦ q m) (tilde.adjunction.unit.naturality a)
  have hn := PresheafOfModules.naturality_apply (L.map a).val
    (homOfLE (show U.2.isoSpec.hom ''ᵁ (U.1.ι ⁻¹ᵁ U.1) ≤ ⊤ from le_top)).op
    ((tilde.adjunction.unit.app M) m)
  change (tilde.adjunction.unit.app P) (a m) =
    (L.map a).val.app (op ⊤) ((tilde.adjunction.unit.app M) m) at ht
  let x := (L.obj M).val.map
    (homOfLE (show U.2.isoSpec.hom ''ᵁ (U.1.ι ⁻¹ᵁ U.1) ≤ ⊤ from le_top)).op
    ((tilde.adjunction.unit.app M) m)
  have hη' := congrArg (fun q ↦ q x) hη
  change (η.app (F.obj P)).val.app (op U.1) ((F.map a).val.app (op U.1) x) =
    ((Scheme.Modules.tensorPullback i).map (F.map a)).val.app (op (i ⁻¹ᵁ U.1))
      ((η.app (F.obj M)).val.app (op U.1) x) at hη'
  dsimp only [selfTorAffineSection]
  change ((Scheme.Modules.tensorPullback i).map (F.map a)).val.app
      (op (i ⁻¹ᵁ U.1)) ((η.app (F.obj M)).val.app (op U.1) x) = _
  rw [← hη']
  apply congrArg ((η.app (F.obj P)).val.app (op U.1))
  change (L.map a).val.app (op (U.2.isoSpec.hom ''ᵁ (U.1.ι ⁻¹ᵁ U.1))) x = _
  exact hn.trans (congrArg ((L.obj P).val.map (homOfLE le_top).op) ht.symm)

end AlgebraicGeometry
