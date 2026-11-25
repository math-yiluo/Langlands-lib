/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import all WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import all WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk

/-! # The generic stalk of a birational line pushforward

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
verification of property (a).
(blueprint: lem-pc-q2-birational-line-pushforward-generic-stalk)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits TopologicalSpace in
private theorem stalk_bijective_of_restrict_iso {Z W : Scheme.{u}}
    (j : Z ⟶ W) [IsOpenImmersion j] {M N : W.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)] (z : Z) :
    Function.Bijective ((RingedSpace.moduleStalkFunctor W.toRingedSpace (j z)).map f) := by
  let e := (restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
    restrictFunctorCongr j.isoOpensRange_inv_comp
  have : IsIso (((restrictFunctor j) ⋙ restrictFunctor j.isoOpensRange.inv).map f) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have : IsIso ((restrictFunctor j.opensRange.ι).map f) :=
    (NatIso.isIso_map_iff e f).mp inferInstance
  exact bijective_stalk_of_isIso_restrict (U := j.opensRange) f (j z) ⟨z, rfl⟩

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits TopologicalSpace in
private theorem stalk_free_of_restrict_iso {Z W : Scheme.{u}}
    (j : Z ⟶ W) [IsOpenImmersion j] (M : W.Modules)
    (e : M.restrict j ≅ SheafOfModules.unit Z.ringCatSheaf) (z : Z) :
    Nonempty (((RingedSpace.moduleStalkFunctor W.toRingedSpace (j z)).obj M)
      ≃ₗ[W.presheaf.stalk (j z)] W.presheaf.stalk (j z)) := by
  let A := restrictAdjunction j
  let f := A.unit.app M ≫ (pushforward j).map e.hom
  let g := A.unit.app (SheafOfModules.unit W.ringCatSheaf) ≫
    (pushforward j).map (restrictUnitIso j).hom
  have : IsIso ((restrictFunctor j).map f) := by
    dsimp only [f]
    rw [Functor.map_comp]
    infer_instance
  have : IsIso ((restrictFunctor j).map g) := by
    dsimp only [g]
    rw [Functor.map_comp]
    infer_instance
  let T := RingedSpace.moduleStalkFunctor W.toRingedSpace (j z)
  let ef := LinearEquiv.ofBijective (T.map f).hom
    (stalk_bijective_of_restrict_iso j f z)
  let eg := LinearEquiv.ofBijective (T.map g).hom
    (stalk_bijective_of_restrict_iso j g z)
  obtain ⟨eu, _⟩ := AlgebraicGeometry.Scheme.unit_stalk_iso W (j z)
  exact ⟨ef.trans (eg.symm.trans eu.toLinearEquiv)⟩

-- Local module-stalk comparisons unfold several nested restriction functors.
set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits TopologicalSpace in
/-- On an open where a morphism is an isomorphism, the pushforward of an
invertible module has a free stalk of rank one at each point of that open.

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
verification of property (a).
(blueprint: lem-pc-q2-birational-line-pushforward-generic-stalk)

Proof: Let y be the inverse image of x under the isomorphism from the inverse
image of U to U. Restriction of the pushforward to U identifies with pushforward
of the restriction of L along that isomorphism: on every open V of U, both
modules have sections L over the inverse image of V with the same scalar action.
Restriction preserves invertibility, as does transport along an isomorphism.
Choose an open neighbourhood of x on which this transported module is the
structure module, using the defining local trivialization of an invertible module.
Restriction to a neighbourhood preserves stalks: its neighbourhoods are cofinal
among the neighbourhoods of x in W. Taking the stalk of the trivialization
therefore identifies the original pushforward stalk with the structure-ring
stalk, linearly over that ring. Neither density nor integrality is needed.
The statement is conditional on x belonging to U, so an empty open is harmless. -/
private theorem line_pushforward_stalk_on_iso_open {W Y : Scheme.{u}}
    (π : Y ⟶ W) (U : W.Opens) [IsIso (π ∣_ U)]
    (L : Y.Modules) [L.IsInvertible] (x : W) (hx : x ∈ U) :
    Nonempty (((RingedSpace.moduleStalkFunctor W.toRingedSpace x).obj
      ((pushforward π).obj L)) ≃ₗ[W.presheaf.stalk x] W.presheaf.stalk x) := by
  classical
  let M := (pushforward π).obj L
  let e := (Scheme.Modules.pushforwardRestrictIso
    (isPullback_morphismRestrict π U).flip).app L
  have : (L.restrict (π ⁻¹ᵁ U).ι).IsInvertible :=
    IsInvertible.of_iso ((restrictFunctorIsoPullback (π ⁻¹ᵁ U).ι).app L).symm
  let q := π ∣_ U
  have : ((pullback (inv q)).obj (L.restrict (π ⁻¹ᵁ U).ι)).IsInvertible := inferInstance
  let eq : (pullback (inv q)).obj (L.restrict (π ⁻¹ᵁ U).ι) ≅
      (pushforward q).obj (L.restrict (π ⁻¹ᵁ U).ι) :=
    (pullbackIsoPushforwardInv (inv q)).app _ ≪≫ (pushforwardCongr (IsIso.inv_inv (f := q))).app _
  have : (M.restrict U.ι).IsInvertible := IsInvertible.of_iso (eq ≪≫ e.symm)
  let x' : U := ⟨x, hx⟩
  obtain ⟨V, hxV, ⟨a⟩⟩ := IsInvertible.exists_isoUnit (M := M.restrict U.ι) x'
  let b : (M.restrict U.ι).restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (restrictFunctorIsoPullback V.ι).app _ ≪≫ a
  let j := V.ι ≫ U.ι
  let c : M.restrict j ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (restrictFunctorComp V.ι U.ι).app M ≪≫ b
  exact stalk_free_of_restrict_iso j M c ⟨x', hxV⟩

set_option backward.isDefEq.respectTransparency false in
/-- A line pushed forward through a morphism that is an isomorphism on a dense
open of an integral scheme has the residue-field stalk after closed pushforward.
The equivalence respects the original stalk action through the residue map.

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
property (a) and the closed-immersion stalk comparison preceding Chow's lemma.
(blueprint: lem-pc-q2-birational-line-pushforward-generic-stalk)

Proof:
1. The generic point eta of integral W belongs to the dense open U. Restriction
   of pushforward to U is pushforward from pi^{-1}(U). As pi restricted to U is
   an isomorphism, this restricted module is invertible. A local trivialization
   gives its eta stalk an O_{W,eta}-linear equivalence with O_{W,eta}.
2. O_{W,eta} is a field. The residue quotient identifies it with kappa(eta).
   The stalk of i_* at i(eta) is that of the original module at eta, and its
   scalar action is induced by i.stalkMap eta (closed-pushforward stalks).
3. A closed immersion induces an isomorphism of residue fields at corresponding
   points. Compose the additive equivalences with this residue-field isomorphism.
   Naturality of the residue maps gives e(a v) = residue(a) e(v).
   This construction works for every invertible L, with no cohomological,
   projective, properness, or Noetherian hypothesis. -/
theorem birational_line_pushforward_generic_stalk {X W Y : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (π : Y ⟶ W) (U : W.Opens) (hU : Dense (U : Set W))
    [IsIso (π ∣_ U)] (L : Y.Modules) [L.IsInvertible] :
    ∃ e : ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj ((pushforward i).obj ((pushforward π).obj L))) ≃+
        X.residueField (i.base (genericPoint W)),
      ∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj ((pushforward i).obj ((pushforward π).obj L))),
        e (a • v) = (X.residue (i.base (genericPoint W))) a * e v := by
  classical
  have hη : genericPoint W ∈ U := by
    apply ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr
    simpa using hU.nonempty
  obtain ⟨l⟩ := line_pushforward_stalk_on_iso_open π U L (genericPoint W) hη
  let G := (pushforward π).obj L
  let c := TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf (genericPoint W)
  obtain ⟨hc, _, hlin⟩ :=
    (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).2.1 (genericPoint W)
  let ce : ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).obj ((pushforward i).obj G)) ≃+
      ((RingedSpace.moduleStalkFunctor W.toRingedSpace (genericPoint W)).obj G) :=
    AddEquiv.ofBijective c.hom hc
  let r : W.presheaf.stalk (genericPoint W) ≃+* W.residueField (genericPoint W) :=
    RingEquiv.ofBijective (W.residue (genericPoint W)).hom
      ⟨(W.residue (genericPoint W)).hom.injective, W.residue_surjective _⟩
  have hb : Function.Bijective (i.residueFieldMap (genericPoint W)) := by
    refine ⟨(i.residueFieldMap (genericPoint W)).hom.injective, ?_⟩
    intro b
    obtain ⟨a, rfl⟩ := W.residue_surjective (genericPoint W) b
    obtain ⟨a, rfl⟩ := i.stalkMap_surjective (genericPoint W) a
    refine ⟨X.residue (i.base (genericPoint W)) a, ?_⟩
    exact ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i (genericPoint W)) a
  let k := RingEquiv.ofBijective (i.residueFieldMap (genericPoint W)).hom hb
  refine ⟨ce.trans (l.toAddEquiv.trans (r.toAddEquiv.trans k.symm.toAddEquiv)), ?_⟩
  intro a v
  change k.symm (r (l (ce (a • v)))) =
    X.residue (i.base (genericPoint W)) a * k.symm (r (l (ce v)))
  have hce : ce (a • v) = (i.stalkMap (genericPoint W)).hom a • ce v := hlin a v
  rw [hce, l.map_smul, smul_eq_mul, r.map_mul, k.symm.map_mul]
  congr 1
  apply k.injective
  rw [k.apply_symm_apply]
  exact (ConcreteCategory.congr_hom
    (Scheme.residue_residueFieldMap i (genericPoint W)) a).symm

end AlgebraicGeometry.Scheme.Modules
