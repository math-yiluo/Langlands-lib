/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Injectivity of the structure-sheaf unit at a nonempty flat fibre

Source: Stacks Project, Tag 0E62 (the injective part of the proper-flat criterion),
with the flat local-ring argument in Mathlib's `epi_of_flat_of_surjective`.
(blueprint: lem-sc-proper-flat-structure-sheaf-stalk-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Flat local ring maps are faithfully flat and therefore injective.
Source: Mathlib, `AlgebraicGeometry.epi_of_flat_of_surjective`, stalkwise argument. -/
private theorem flat_stalk_injective {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (x : X) : Function.Injective (f.stalkMap x) := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Opposite TopologicalSpace in
/-- The ordinary structure map is injective on the stalk at an image point.
Source: the flat local-ring argument of Mathlib's `epi_of_flat_of_surjective`,
combined with `TopCat.Presheaf.germ_eq` and `Scheme.Hom.germ_stalkMap_apply`.
If two direct-image germs agree, their sections agree after restriction to a base
neighbourhood. Their images in the local ring upstairs agree, so faithful flatness
makes their base ring germs agree. A second restriction gives equality of the
underlying abelian germs. -/
private theorem structure_unit_stalk_injective {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] (x : X) : Function.Injective
      (Scheme.Modules.Hom.stalkLinearMap
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) (f x)) := by
  let M : S.Modules := SheafOfModules.unit S.ringCatSheaf
  let N : S.Modules := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  intro a b hab
  obtain ⟨U, hxU, a, rfl⟩ := M.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, b, rfl⟩ := M.presheaf.exists_germ_eq b
  rw [Scheme.Modules.Hom.stalkLinearMap_germ,
    Scheme.Modules.Hom.stalkLinearMap_germ] at hab
  obtain ⟨W, hxW, iU, iV, he⟩ := N.presheaf.germ_eq (f x) hxU hxV _ _ hab
  have he' : f.app W (S.presheaf.map iU.op a) =
      f.app W (S.presheaf.map iV.op b) := by
    change X.presheaf.map ((Opens.map f.base).map iU).op (f.app U a) =
      X.presheaf.map ((Opens.map f.base).map iV).op (f.app V b) at he
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← f.naturality iU.op, ← f.naturality iV.op] at he
    exact he
  have hg : S.presheaf.germ W (f x) hxW (S.presheaf.map iU.op a) =
      S.presheaf.germ W (f x) hxW (S.presheaf.map iV.op b) := by
    apply flat_stalk_injective f x
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, he']
  obtain ⟨T, hxT, jU, jV, ht⟩ := S.presheaf.germ_eq (f x) hxW hxW _ _ hg
  have ht' : M.presheaf.map (jU ≫ iU).op a =
      M.presheaf.map (jV ≫ iV).op b := by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact ht
  have := congrArg (fun t ↦ M.presheaf.germ T (f x) hxT t) ht'
  simpa only [TopCat.Presheaf.germ_res_apply] using this

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Injective part of the local proper-flat structure-sheaf criterion.
Source: Stacks Project, Tag 0E62, proof of `perfect-lemma-proper-flat-h0`, localized
at the fixed point. The shorter injectivity argument uses Mathlib's flat local-ring
argument in `epi_of_flat_of_surjective` and the structure-sheaf adjunction comparison
of Stacks Tags 0096 and 01CA.
(blueprint: lem-sc-proper-flat-structure-sheaf-stalk-injective).

Proof: The fibre is nonempty: otherwise its global sections are the zero ring,
contradicting injectivity of the assumed isomorphism from the residue field.
Choose a point x above s. The flat local homomorphism O_{S,s} → O_{X,x} is faithfully
flat and hence injective. Equality of germs in the ordinary direct image gives
sections equal after restricting to a neighbourhood of s. Taking germs at x and
using this ring injection gives equality of the input ring germs, hence of their
underlying abelian germs. Finally, `tensorPullbackObjUnitToUnit_isIso` identifies
the chosen adjunction unit followed by pushforward of the structure-sheaf comparison
with the ordinary structure map. Compose an equality under the chosen unit with
that comparison and apply the injectivity just proved. -/
theorem injective_structureSheafMap_stalk_of_proper_flat_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : S)
    (hs : IsIso (f.fiberToSpecResidueField s).appTop) :
    Function.Injective
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)).stalkLinearMap s) := by
  have hfiber : Nonempty (f.fiber s) := by
    by_contra h
    have : IsEmpty (f.fiber s) := not_nonempty_iff.mp h
    have ht : (⊤ : (f.fiber s).Opens) = ⊥ := by
      ext z
      exact isEmptyElim z
    have hz : (0 : Γ(f.fiber s, ⊤)) = 1 := by
      rw [ht]
      exact Subsingleton.elim _ _
    have hinj := (ConcreteCategory.bijective_of_isIso
      (f.fiberToSpecResidueField s).appTop).1
    exact zero_ne_one (hinj (by simpa using hz))
  obtain ⟨z⟩ := hfiber
  obtain ⟨x, hx⟩ := (f.fiberHomeo s z)
  have hfx : f x = s := hx
  subst s
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)
  let η := adj.unit.app (SheafOfModules.unit S.ringCatSheaf)
  let ε := (Scheme.Modules.pushforward f).map
    (Scheme.Modules.tensorPullbackObjUnitToUnit f)
  have he : η ≫ ε = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f).2
  intro a b hab
  apply structure_unit_stalk_injective f x
  rw [← he, Scheme.Modules.Hom.stalkLinearMap_apply,
    Scheme.Modules.Hom.stalkLinearMap_apply]
  change (TopCat.Presheaf.stalkFunctor Ab.{u} (f x)).map
      (η.mapPresheaf ≫ ε.mapPresheaf) a =
    (TopCat.Presheaf.stalkFunctor Ab.{u} (f x)).map
      (η.mapPresheaf ≫ ε.mapPresheaf) b
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  exact congrArg (fun t ↦
    (TopCat.Presheaf.stalkFunctor Ab.{u} (f x)).map ε.mapPresheaf t) hab

end AlgebraicGeometry
