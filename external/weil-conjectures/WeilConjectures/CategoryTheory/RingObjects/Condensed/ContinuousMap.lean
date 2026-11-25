/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits

/-!

# The condensed ring of continuous maps into a topological ring

The *pro-étale site of a point* `*_proét` is the category `Profinite` of profinite sets with the
coherent topology, in which a finite family `{Sᵢ ⟶ S}` covers precisely when `∐ᵢ Sᵢ ⟶ S` is
surjective. A *condensed ring* is a sheaf of rings on this site.

Let `T` be a topological ring. This file defines the condensed ring `T̲` *by its sections*,
```
T̲(S) := C(S, T),
```
with restriction maps given by precomposition and the pointwise ring operations, following
Definition 2.2 of `WeilConjectures/RefactorInstruction.tex`. No limit, colimit or localization
enters this definition; such descriptions of particular coefficient rings are comparison
results, to be proved separately.

The sheaf axiom is checked directly (Proposition 2.3 of the notes): a covering is equivalent,
for the sheaf axiom, to a surjection `q : S' ⟶ S` of profinite sets, which is a topological
quotient map, so a continuous map `S' → T` descends along `q` exactly when it is constant on
the fibres of `q`. This is mathlib's `equalizerCondition_yonedaPresheaf`, and the finite
coproduct condition is formal.

A continuous ring homomorphism `T →+* T'` induces a morphism of condensed rings `T̲ ⟶ T̲'`, by
postcomposition (`Profinite.continuousMapRingSheafMap`). The underlying abelian sheaf of `T̲` is
a ring object of the category of abelian sheaves on `*_proét`
(`CategoryTheory.Sheaf.monObj_sheafCompose_obj`), commutative when `T` is.

## Main definitions

* `Profinite.continuousMapRingPresheaf`: the presheaf of rings `S ↦ C(S, T)` on `Profinite`.
* `Profinite.continuousMapRingSheaf`: the condensed ring `T̲`, a sheaf of rings for the coherent
  topology on `Profinite`, and `Profinite.continuousMapRingObj`: the underlying ring object of
  condensed abelian groups.
* `Profinite.continuousMapRingSheafMap`: the morphism of condensed rings induced by a continuous
  ring homomorphism `T →+* T'`.

## Universes

The category `Profinite.{u}` has `Hom`-types in `Type u` and objects in `Type (u + 1)`, so
sheaves on it take values in `RingCat.{u + 1}` and `Ab.{u + 1}`, matching the convention for the
small pro-étale site of a scheme `X : Scheme.{u}` in the `SixFunctors` folder. The sections
`C(S, T)`, which live in `Type u` for `T : Type`, are therefore lifted to `Type (u + 1)`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace Profinite

section Ring

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The presheaf of rings `S ↦ C(S, T)` of continuous maps into the topological ring `T` on the
category of profinite sets, with restriction by precomposition and the pointwise ring
operations, lifted to `Type (u + 1)`. -/
noncomputable def continuousMapRingPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj S := RingCat.of (ULift.{u + 1} C(S.unop, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma continuousMapRingPresheaf_obj (S : Profinite.{u}ᵒᵖ) :
    (continuousMapRingPresheaf T).obj S = RingCat.of (ULift.{u + 1} C(S.unop, T)) :=
  rfl

lemma continuousMapRingPresheaf_map_apply {S S' : Profinite.{u}ᵒᵖ} (f : S ⟶ S')
    (a : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingPresheaf T).map f a = ULift.up (a.down.comp f.unop.hom.hom) :=
  rfl

/-- The presheaf of types underlying `continuousMapRingPresheaf T` is mathlib's presheaf
`S ↦ C(S, T)` of continuous maps on `Profinite` (`ContinuousMap.yonedaPresheaf`), lifted by one
universe. -/
noncomputable def continuousMapRingPresheafForgetIso :
    continuousMapRingPresheaf.{u} T ⋙ forget RingCat.{u + 1} ≅
      ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

omit [Ring T] [IsTopologicalRing T] in
/-- The presheaf `S ↦ C(S, T)` of continuous maps is a sheaf for the coherent topology on
`Profinite`: continuous maps descend along surjections of profinite sets, which are quotient
maps, and the finite coproduct condition is formal. -/
lemma isSheaf_yonedaPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T) := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  refine ⟨inferInstance, ?_⟩
  apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} T
  intro Z B π hπ
  exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 1 3).mp hπ)
    π.hom.hom.continuous

/-- The presheaf `S ↦ C(S, T)` is a sheaf of rings for the coherent topology on `Profinite`. -/
lemma isSheaf_continuousMapRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (continuousMapRingPresheaf T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (continuousMapRingPresheafForgetIso T),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact isSheaf_yonedaPresheaf T

/-- The condensed ring `T̲` of continuous maps into the topological ring `T`: the sheaf of rings
`S ↦ C(S, T)` on the pro-étale site of a point, with restriction by precomposition and the
pointwise ring operations. -/
noncomputable def continuousMapRingSheaf :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨continuousMapRingPresheaf T, isSheaf_continuousMapRingPresheaf T⟩

lemma continuousMapRingSheaf_obj :
    (continuousMapRingSheaf.{u} T).obj = continuousMapRingPresheaf T :=
  rfl

/-- The condensed ring `T̲ = C(-, T)` as a ring object of condensed abelian groups: the abelian
sheaf underlying `continuousMapRingSheaf T`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev continuousMapRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousMapRingSheaf T)

variable {T} {T' : Type} [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']
  (φ : T →+* T') (hφ : Continuous φ)

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
presheaves of rings `C(-, T) ⟶ C(-, T')` on `Profinite`. -/
noncomputable def continuousMapRingPresheafMap :
    continuousMapRingPresheaf.{u} T ⟶ continuousMapRingPresheaf T' where
  app _ := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

lemma continuousMapRingPresheafMap_app_apply (S : Profinite.{u}ᵒᵖ)
    (a : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingPresheafMap φ hφ).app S a = ULift.up ((⟨φ, hφ⟩ : C(T, T')).comp a.down) :=
  rfl

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
condensed rings `T̲ ⟶ T̲'`. -/
noncomputable def continuousMapRingSheafMap :
    continuousMapRingSheaf.{u} T ⟶ continuousMapRingSheaf T' :=
  ⟨continuousMapRingPresheafMap φ hφ⟩

lemma continuousMapRingSheafMap_hom :
    (continuousMapRingSheafMap.{u} φ hφ).hom = continuousMapRingPresheafMap φ hφ :=
  rfl

/-- Postcomposition with the identity is the identity. -/
lemma continuousMapRingSheafMap_id :
    continuousMapRingSheafMap.{u} (RingHom.id T) continuous_id = 𝟙 _ :=
  rfl

/-- Postcomposition is compatible with composition of continuous ring homomorphisms. -/
lemma continuousMapRingSheafMap_comp {T'' : Type} [TopologicalSpace T''] [Ring T'']
    [IsTopologicalRing T''] (ψ : T' →+* T'') (hψ : Continuous ψ) :
    continuousMapRingSheafMap.{u} (ψ.comp φ) (hψ.comp hφ) =
      continuousMapRingSheafMap φ hφ ≫ continuousMapRingSheafMap ψ hψ :=
  rfl


end Ring

section CommRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The condensed ring of continuous maps into a commutative topological ring is a commutative
ring object of the category of abelian sheaves on `Profinite`. -/
instance isCommMonObj_continuousMapRingObj : IsCommMonObj (continuousMapRingObj.{u} T) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (continuousMapRingSheaf T) fun S (a b : ULift.{u + 1} C(S.unop, T)) ↦ mul_comm a b

end CommRing

end Profinite
