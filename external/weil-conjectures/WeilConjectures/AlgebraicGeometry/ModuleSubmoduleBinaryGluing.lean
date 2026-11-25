/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ModuleSubmoduleBinaryGluingProperties
import WeilConjectures.AlgebraicGeometry.ModuleBinaryLocalProperties

/-! # Gluing a submodule with the ambient module on two opens

Source: Stacks Project, Properties, Lemma 01PF, binary gluing step.
(blueprint: lem-weil-pbc-module-submodule-binary-gluing).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules in
private theorem finiteType_of_data
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType :=
    ⟨fun i ↦ hq.isFiniteType i.2.choose⟩
  exact ⟨q.shrink, this⟩

open SheafOfModules in
private theorem finiteType_of_iso
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have : q'.IsFiniteType := ⟨fun i ↦ by
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType⟩
  exact finiteType_of_data q'



/-- Glue a finite-type submodule on V to the whole module on W when its inclusion
is an isomorphism on the overlap. No compactness or affineness is required.

Source: Stacks Project, Properties, Lemma 01PF (label lemma-extend), reduction
from a union to its affine member, gluing along the common value on the overlap.
https://stacks.math.columbia.edu/tag/01PF
(blueprint: lem-weil-pbc-module-submodule-binary-gluing).

Proof: Construct G as the pullback of the direct image of Q along the restriction
unit of H on W union V. The first projection φ is monic because direct image is a
right adjoint and pullback preserves monomorphisms. The sectionwise pullback
identifications make φ an isomorphism on W and identify G on V with Q. Transport
quasi-coherence and finite type across these two isomorphisms, then apply their
locality on the covering W,V. The concrete pullback requires no arbitrary choice
of an existence witness, and includes empty or disjoint opens. Neither compactness
nor affineness is used. -/
theorem exists_submodule_binary_gluing
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFiniteType]
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    [Q.IsQuasicoherent] [Q.IsFiniteType] (ι : Q ⟶ H.over V) [Mono ι]
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map ι)] :
    ∃ G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V)),
      G.IsQuasicoherent ∧ G.IsFiniteType ∧ ∃ (φ : G ⟶ H.over (W ⊔ V)),
        Mono φ ∧ IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map φ) := by
  -- Cache sheafification on iterated slices for the four isomorphism transports below.
  have (A : X.Opens) (T : Over A) :
      HasSheafify (((_root_.Opens.grothendieckTopology X).over A).over T)
        AddCommGrpCat.{u} := inferInstance
  have (A : X.Opens) (T : Over A) :
      (((_root_.Opens.grothendieckTopology X).over A).over T).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  let G := binarySubmodule X W V H Q ι
  let φ := binarySubmoduleInclusion X W V H Q ι
  obtain ⟨hW, ⟨eV⟩⟩ := binarySubmodule_restrictions X W V H Q ι
  have := hW
  let eW : (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).obj G ≅ H.over W :=
    asIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map φ) ≪≫
      (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
        (homOfLE (show W ≤ W ⊔ V from le_sup_left))).app H
  have hWqc : ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over W)).prop_of_iso eW.symm
      (SheafOfModules.isQuasicoherent_over H W)
  have hWft := finiteType_of_iso (R := (moduleRings X.toRingedSpace).over W) eW.symm
  have hVqc : ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show V ≤ W ⊔ V from le_sup_right))).obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over V)).prop_of_iso
      eV.symm inferInstance
  have hVft := finiteType_of_iso (R := (moduleRings X.toRingedSpace).over V) eV.symm
  obtain ⟨hqc, hft⟩ := module_binary_local_properties X W V G
    ⟨hWqc, hWft⟩ ⟨hVqc, hVft⟩
  exact ⟨G, hqc, hft, φ, inferInstance, hW⟩

end AlgebraicGeometry.Scheme.Modules
