/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.CategoryTheory.Localization.Equivalence
import WeilConjectures.AlgebraicGeometry.QuasiCompactFiniteTorDimension
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.AffineTorAmplitudeCriterion
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor

/-! # Finite Tor amplitude of the affine module model

Source: Stacks Project, Tag 08EB (perfect-lemma-perfect-affine).
(blueprint: lem-pc-perfect-affine-module-preimage).
-/

@[expose] public section

universe u w wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

@[instance_reducible]
private noncomputable def derivedCategoryOfEquivalence
    {C D : Type u} [Category.{wA} C] [Category.{wA} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] (e : C ≌ D) : HasDerivedCategory.{w} D := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let ec := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := ec.inverse ⋙ DerivedCategory.Q
  have hL : L.IsLocalization (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) := by
    apply Functor.IsLocalization.of_equivalence_source DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) L
      (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ec
    · intro K K' f hf
      let : QuasiIso f := hf
      exact MorphismProperty.le_isoClosure _ _
        (HomologicalComplex.quasiIso_map_of_preservesHomology _ _)
    · exact e.inverse.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso _
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ec.unitIso.symm _ ≪≫ Functor.leftUnitor _
  exact { L := L }

/-- A perfect affine object has a pseudo-coherent finite-Tor preimage under the
associated-sheaf derived equivalence.
Source: Stacks Project, perfect.tex, Lemma perfect-lemma-perfect-affine (Tag 08EB).
(blueprint: lem-pc-perfect-affine-module-preimage)

Proof: Take the equivalence of lem-pc-affine-qcoh-derived-equivalence and a complex M
representing e.inverse.obj E using essential surjectivity of Q. Set C = Q.obj M.
Its representing isomorphism and the counit, followed by inclusion, give E ≅ e(C).
The comparison Q ⋙ e ⋙ inclusion ≅ tilde ⋙ Q identifies its associated sheaf S with E.
Transport perfectness to S using the exact over-site restriction functors.
The equivalence between over-site modules and modules on an open subscheme transports
the chosen derived localization to the latter, with the same morphism universe.
Perfectness gives pseudo-coherence and local finite Tor dimension by
lem-pc-perfect-pseudo-coherent-locally-finite-tor. A finite subcover of Spec A supplies
one interval: take the minimum of the finitely many lower bounds and the maximum of
upper bounds, enlarging to a nonempty interval if the spectrum is empty. Derived tensor
commutes with restriction, and vanishing on an open cover detects zero cohomology sheaves.
The finite-subcover argument is hasFiniteTorDimension_of_locallyFinite
(lem-pc-quasi-compact-finite-tor-dimension); it uses the fixed-interval locality theorem
lem-pc-tor-amplitude-open-local. Thus S has global finite Tor amplitude. Apply
lem-pc-affine-pseudo-coherent-criterion and lem-pc-affine-tor-amplitude-criterion to M.
For the zero ring the spectrum is empty and both derived categories are zero, so the
interval [0,0] works. This step constructs no bounded projective replacement. -/
theorem perfect_affine_module_preimage (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (hE : Scheme.IsPerfect (Spec (.of A)) E.obj) :
    ∃ e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)),
      ∃ C : DerivedCategory (ModuleCat.{u} A),
        DerivedCategory.IsPseudoCoherent C ∧
        (∃ a b : ℤ, a ≤ b ∧
          DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) a b C) ∧
        Nonempty (E.obj ≅ ((schemeDerivedQCohProperty (Spec (.of A))).ι).obj
          (e.functor.obj C)) ∧
        Nonempty (DerivedCategory.Q ⋙ e.functor ⋙
          (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
          @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
  classical
  let openDerived (U : (Spec (.of A)).Opens) :
      HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    derivedCategoryOfEquivalence (Scheme.Modules.overEquiv U)
  obtain ⟨e, ⟨cmp⟩, _⟩ := exists_affineQCohDerivedEquivalence A
  obtain ⟨M, ⟨miso⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q (e.inverse.obj E)
  let incl := (schemeDerivedQCohProperty (Spec (.of A))).ι
  let S := DerivedCategory.Q.obj
    ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
      (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M)
  let isoSE : S ≅ E.obj := (cmp.app M).symm ≪≫
    incl.mapIso (e.functor.mapIso miso) ≪≫ incl.mapIso (e.counitIso.app E)
  have hS : Scheme.IsPerfect (Spec (.of A)) S := by
    intro x
    obtain ⟨U, hx, K, hK, ⟨hk⟩⟩ := hE x
    exact ⟨U, hx, K, hK, ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.mapIso isoSE ≪≫
        hk⟩⟩
  obtain ⟨hpc, hlocal⟩ :=
    Scheme.perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension
      (Spec (.of A)) S hS
  obtain ⟨a, b, hab, htor⟩ :=
    Scheme.hasFiniteTorDimension_of_locallyFinite (Spec (.of A)) S hlocal
  refine ⟨e, DerivedCategory.Q.obj M, (isPseudoCoherent_affine_iff A M).mp hpc,
    ⟨a, b, hab, (affine_torAmplitude_iff A M a b hab).mp htor⟩, ?_, ⟨cmp⟩⟩
  exact ⟨(incl.mapIso (e.counitIso.app E)).symm ≪≫
    (incl.mapIso (e.functor.mapIso miso)).symm⟩

end AlgebraicGeometry
