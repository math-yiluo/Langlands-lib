/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore

/-! # Normalized affine cohomology edge maps -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Every component of a normalized affine edge morphism is invertible.
Source: Stacks Project, perfect.tex, lemma-affine-morphism-equivalence (Tag 0AVW),
and perfect.tex, lemma-application-nice-K-injective (Tag 08D4).
(blueprint: lem-pc-affine-pushforward-cohomology-edge-isIso).

Proof: For a complex C of A-modules, associated sheaves and their kernels, images
and cohomology are quasi-coherent. Affine higher-direct-image vanishing, with
bound one in the unbounded truncation comparison of Tag 08D4, shows that the
right-derived pushforward unit on T_A C induces an isomorphism in each degree.
Every other factor of q is an isomorphism (exact tilde and scalar restriction,
the Q/homology comparison, and σ), so q is invertible. The normalization equation
for the identity representative says q = (T_B res_phi)(b) followed by α at Q(T_A C).
Since b is an isomorphism, this component of α is invertible. Every object of
D_QCoh(Spec A) is isomorphic to Q(T_A C), by the affine derived equivalence of
Tag 06Z0. Naturality of α along this isomorphism expresses its remaining component
as a composite of invertible maps. Thus every component is invertible. This works
for unbounded C and for the zero ring; it does not require an arbitrary α to agree
with the normalized edge map without the displayed normalization hypothesis. -/
theorem affinePushforwardCohomologyEdge_isIso
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∀ (α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i),
    (∀ (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : schemeDerivedQCohCategory (Spec (.of A)))
      (t : DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj),
      (∃ h : DerivedCategory.Q.obj
          (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) = L.obj,
        t.hom = eqToHom h) →
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map t.hom) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C L.obj t i).hom) ≫ α.app L) →
    ∀ L, IsIso (α.app L) := by
  intro α hα L
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨E, ⟨e⟩, _, _⟩ := exists_affineQCohDerivedEquivalence_core A
  let C := DerivedCategory.Q.objPreimage (E.inverse.obj L)
  let t : DerivedCategory.Q.obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj :=
    (e.app C).symm ≪≫ (schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso
      (E.functor.mapIso (DerivedCategory.Q.objObjPreimageIso (E.inverse.obj L)) ≪≫
        E.counitIso.app L)
  have hC : schemeDerivedQCohProperty (Spec (.of A))
      (DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C)) := by
    intro n
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).mapIso t.symm)
      (L.property n)
  let L₀ : schemeDerivedQCohCategory (Spec (.of A)) := ⟨_, hC⟩
  have hq : IsIso (affinePushforwardCohomologyMapOfComparison A B φ σ C i) := by
    let D := ((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C
    let P := RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
    let : P.Additive := inferInstance
    let : P.PreservesZeroMorphisms := inferInstance
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) (.up ℤ)
    obtain ⟨J, hJ, s, _, hsi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective D
    have : J.IsKInjective := hJ
    have : QuasiIso s := hsi
    have hD (n : ℤ) : (D.X n).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) (C.X n)).IsQuasicoherent
      infer_instance
    have hPs : QuasiIso ((P.mapHomologicalComplex (.up ℤ)).map s) :=
      affinePushforward_resolution_quasiIso _ D J hD s
    have hs : IsIso (DerivedCategory.Qh.{w}.map (q.map s)) := by
      apply (DerivedCategory.isIso_Qh_map_iff _).mpr
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hsi
    have hPs' : IsIso (DerivedCategory.Qh.{w}.map
        ((P.mapHomotopyCategory (.up ℤ)).map (q.map s))) := by
      apply (DerivedCategory.isIso_Qh_map_iff _).mpr
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hPs
    have : IsIso ((DerivedCategory.Qh.{w} ⋙
        P.rightDerivedFunctor.{_, _, _, _, w, w}).map (q.map s)) := by
      change IsIso (P.rightDerivedFunctor.{_, _, _, _, w, w}.map
        (DerivedCategory.Qh.{w}.map (q.map s)))
      infer_instance
    have hu : IsIso (P.rightDerivedFunctorUnit.{_, _, _, _, w, w}.app (q.obj D)) := by
      have hn := P.rightDerivedFunctorUnit.{_, _, _, _, w, w}.naturality (q.map s)
      have : IsIso (P.rightDerivedFunctorUnit.{_, _, _, _, w, w}.app (q.obj D) ≫
          (DerivedCategory.Qh.{w} ⋙ P.rightDerivedFunctor.{_, _, _, _, w, w}).map (q.map s)) := by
        rw [← hn]
        dsimp only [Functor.comp_map]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((DerivedCategory.Qh.{w} ⋙ P.rightDerivedFunctor.{_, _, _, _, w, w}).map (q.map s))
    let : (affinePushforwardTilde B).Additive := by
      constructor
      intro M N f g
      exact tilde.map_add (R := .of B) f g
    let : (affinePushforwardTilde B).PreservesHomology := tilde_preservesHomology B
    let : PreservesFiniteLimits (affinePushforwardTilde B) :=
      Functor.preservesFiniteLimits_of_preservesHomology (affinePushforwardTilde B)
    let : PreservesFiniteColimits (affinePushforwardTilde B) :=
      Functor.preservesFiniteColimits_of_preservesHomology (affinePushforwardTilde B)
    let : (affinePushforwardTilde A).Additive := by
      constructor
      intro M N f g
      exact tilde.map_add (R := .of A) f g
    let : (affinePushforwardTilde A ⋙ P).Additive := inferInstance
    let : (affinePushforwardTilde A ⋙ P).PreservesZeroMorphisms :=
      ⟨fun X Y => by simp⟩
    let : (affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).PreservesZeroMorphisms :=
      ⟨fun X Y => by
        rw [Functor.comp_map, (affinePushforwardTilde A).map_zero]
        exact (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).map_zero _ _⟩
    have : IsIso ((σ.hom.mapHomologicalComplex (.up ℤ)).app C) :=
      ((NatIso.mapHomologicalComplex σ (.up ℤ)).app C).isIso_hom
    dsimp only [affinePushforwardCohomologyMapOfComparison]
    simp only [cast_eq]
    infer_instance
  have hn := hα C L₀ (Iso.refl _) ⟨rfl, rfl⟩
  simp only [Iso.refl_hom] at hn
  have hcomp : IsIso
      ((affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
        (affinePushforwardRepresentativeCohomologyIso A C L₀.obj (Iso.refl _) i).hom) ≫
          α.app L₀) := by
    rw [← hn]
    simpa using hq
  have : IsIso (α.app L₀) := IsIso.of_isIso_comp_left
    ((affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
      (affinePushforwardRepresentativeCohomologyIso A C L₀.obj (Iso.refl _) i).hom))
    (α.app L₀)
  exact (NatTrans.isIso_app_iff_of_iso α
    ((schemeDerivedQCohProperty (Spec (.of A))).isoMk t)).mp this

end AlgebraicGeometry
