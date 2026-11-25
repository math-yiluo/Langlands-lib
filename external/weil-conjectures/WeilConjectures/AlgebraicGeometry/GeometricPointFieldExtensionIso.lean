/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

module

public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Extension of the field of a geometric point, for arbitrary coefficients

Enlarging the separably closed field of a geometric point `s` of a scheme `S` along
`a : Spec l ⟶ Spec k` does not change the point of the small étale site: the morphism of
points `AlgebraicGeometry.Scheme.pointSmallEtalePrecomp s a` is an isomorphism. Hence the stalks
at `s` and at `a ≫ s` of a sheaf with values in any category agree. This is the
coefficient-free form of `AlgebraicGeometry.Scheme.isIso_pointSmallEtalePrecomp_sheafFiber`.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Precomposition with a field extension of separably closed fields is a bijection on the
lifts of a geometric point to an étale `S`-scheme, so `pointSmallEtalePrecomp s a` is an
isomorphism of points: an étale neighbourhood base changed to `Spec k` is a disjoint union
of copies of `Spec k`, and a lift from `Spec l` lands in, and factors uniquely through, one of
them. (blueprint: lem-weil-pbc-geometric-point-field-extension) -/
instance isIso_pointSmallEtalePrecomp_hom
    {S : Scheme.{u}} {k l : Type u} [Field k] [IsSepClosed k]
    [Field l] [IsSepClosed l] (s : Spec (.of k) ⟶ S)
    (a : Spec (.of l) ⟶ Spec (.of k)) :
    IsIso (pointSmallEtalePrecomp s a).hom := by
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
  have (U : S.Etale) : IsIso ((pointSmallEtalePrecomp s a).hom.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij U)
  exact NatIso.isIso_of_isIso_app _

/-- The stalks of a sheaf at a geometric point `s` and at its base change `a ≫ s` along an
extension of separably closed fields agree, for coefficients in any category. -/
noncomputable def sheafFiberPrecompIso {S : Scheme.{u}} {k l : Type u} [Field k]
    [IsSepClosed k] [Field l] [IsSepClosed l] (s : Spec (.of k) ⟶ S)
    (a : Spec (.of l) ⟶ Spec (.of k)) (A : Type*) [Category A]
    [HasColimitsOfSize.{u, u} A] :
    (pointSmallEtale s).sheafFiber (A := A) ≅ (pointSmallEtale (a ≫ s)).sheafFiber :=
  (GrothendieckTopology.Point.sheafFiberIso
    (GrothendieckTopology.Point.isoMk (asIso (pointSmallEtalePrecomp s a).hom)))

end AlgebraicGeometry.Scheme
