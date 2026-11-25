/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Extension of the field of a geometric point

Source: Stacks Project, Tags 03PN and 03Q1.
(blueprint: lem-weil-pbc-geometric-point-field-extension).
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Precompose pointed étale lifts with a field extension. This is a map of points,
with the direction opposite to that of the fibre functors.
Source: Stacks Project, Tag 03PN.
(blueprint: lem-weil-pbc-geometric-point-field-extension). -/
noncomputable def pointSmallEtalePrecomp
    {S : Scheme.{u}} {k l : Type u} [Field k] [IsSepClosed k]
    [Field l] [IsSepClosed l] (s : Spec (.of k) ⟶ S)
    (a : Spec (.of l) ⟶ Spec (.of k)) :
    pointSmallEtale (a ≫ s) ⟶ pointSmallEtale s where
  hom :=
    { app := fun U ↦ ↾fun x ↦ Over.homMk (a ≫ x.left) (by
        rw [Category.assoc]
        exact congrArg (fun z ↦ a ≫ z) x.w)
      naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro x
        apply Over.OverMorphism.ext
        exact (Category.assoc _ _ _).symm }

/-- Enlargement of a separably closed point field induces an isomorphism on abelian
stalks. No algebraicity of the extension is required.
Source: Stacks Project, Tag 03PN, description of geometric stalks, and Tag 03Q1.
(blueprint: lem-weil-pbc-geometric-point-field-extension).

Proof: base change an étale neighbourhood to Spec k. Every point of this fibre has
finite separable residue field over k, hence residue field k. It is an open component
Spec k. A lift from Spec l lands in exactly one such component and factors uniquely
through it. Precomposition is consequently a bijection on lifts, natural in the
neighbourhood. These bijections form an isomorphism of the point fibre functors, and
thus of points. Applying the point sheaf-fibre functor gives the claimed isomorphism.
The argument includes inseparable extensions, non-quasi-compact neighbourhoods,
the zero sheaf, and arbitrary coefficient-group cardinality. -/
theorem isIso_pointSmallEtalePrecomp_sheafFiber
    {S : Scheme.{u}} {k l : Type u} [Field k] [IsSepClosed k]
    [Field l] [IsSepClosed l] (s : Spec (.of k) ⟶ S)
    (a : Spec (.of l) ⟶ Spec (.of k))
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((pointSmallEtalePrecomp s a).sheafFiber.app F)  := by
  have ha : Epi a := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective a
    algebraize [φ.hom]
    have : Module.FaithfullyFlat k l := inferInstance
    have hflat := (flat_and_surjective_SpecMap_iff φ).mpr
      (by rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.faithfullyFlat_algebraMap_iff]
          infer_instance)
    have : Flat (Spec.map φ) := hflat.1
    have : Surjective (Spec.map φ) := hflat.2
    exact Flat.epi_of_flat_of_surjective _
  have hbij (U : S.Etale) : Function.Bijective
      ((pointSmallEtalePrecomp s a).hom.app U) := by
    constructor
    · intro x y hxy
      apply Over.OverMorphism.ext
      apply (cancel_epi a).mp
      exact congrArg Over.Hom.left hxy
    · intro x
      let z : Spec (.of l) ⟶ pullback U.hom s := pullback.lift x.left a (by simpa using x.w)
      have hz : (pullback.snd U.hom s) (z default) = default := by
        change (z ≫ pullback.snd U.hom s) default = _
        simp only [z, pullback.lift_snd]
        exact Subsingleton.elim _ _
      obtain ⟨d, hd, hdz⟩ := exists_fac_of_etale_of_isSepClosed
        (pullback.snd U.hom s) (𝟙 (Spec (.of k))) (z default) (by simpa using hz)
      have : IsOpenImmersion (d ≫ pullback.snd U.hom s) := by rw [hd]; infer_instance
      have : IsOpenImmersion d := by
        apply FormallyUnramified.isOpenImmersion_of_comp (pullback.snd U.hom s) d
      have hr : Set.range z.base ⊆ Set.range d.base := by
        rintro _ ⟨w, rfl⟩
        obtain rfl : w = default := Subsingleton.elim _ _
        exact ⟨default, hdz⟩
      let c := IsOpenImmersion.lift d z hr
      have hc : c ≫ d = z := IsOpenImmersion.lift_fac d z hr
      have hca : c = a := by
        calc
          c = c ≫ d ≫ pullback.snd U.hom s := by rw [hd]; simp
          _ = a := by rw [← Category.assoc, hc]; exact pullback.lift_snd _ _ _
      refine ⟨Over.homMk (d ≫ pullback.fst U.hom s) ?_, ?_⟩
      · change (d ≫ pullback.fst U.hom s) ≫ U.hom = s
        rw [Category.assoc, pullback.condition, ← Category.assoc, hd, Category.id_comp]
      · apply Over.OverMorphism.ext
        change a ≫ (d ≫ pullback.fst U.hom s) = x.left
        calc
          a ≫ (d ≫ pullback.fst U.hom s) =
              c ≫ (d ≫ pullback.fst U.hom s) :=
            congrArg (fun w ↦ w ≫ (d ≫ pullback.fst U.hom s)) hca.symm
          _ = z ≫ pullback.fst U.hom s := by rw [← Category.assoc, hc]
          _ = x.left := pullback.lift_fst _ _ _
  have : IsIso (pointSmallEtalePrecomp s a).hom := by
    have (U : S.Etale) : IsIso ((pointSmallEtalePrecomp s a).hom.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hbij U)
    exact NatIso.isIso_of_isIso_app _
  let e := GrothendieckTopology.Point.isoMk (asIso (pointSmallEtalePrecomp s a).hom)
  change IsIso ((GrothendieckTopology.Point.sheafFiberIso e).hom.app F)
  infer_instance

end AlgebraicGeometry.Scheme
