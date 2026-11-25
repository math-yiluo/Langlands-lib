/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
import WeilConjectures.Algebra.Homology.AffineDerivedPushforwardSheafEdge
import WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity

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

/-- The affine edge morphism in tilde/Gamma coordinates exists naturally, before
asserting that it is invertible. The ordinary comparison σ is supplied, not chosen.
Source: Stacks Project, perfect.tex, lemma-affine-morphism-equivalence (Tag 0AVW),
and perfect.tex, lemma-application-nice-K-injective (Tag 08D4).
(blueprint: lem-pc-affine-pushforward-cohomology-edge-exists).

Proof: Resolve a quasi-coherent derived object by a K-injective complex. On inverse
images of affine opens use the cycle-to-cohomology-class map and the truncation
comparison of Tag 08D4 to form f_*H^i(L) → H^i(Rf_*L). These maps commute with
restriction and with morphisms of resolutions; therefore they glue and descend to
a natural transformation on D_QCoh(Spec A). Precompose with σ at Gamma_A H^i(L)
and f_* of the tilde/Gamma counit. For L = Q(T_A C), exactness of tilde identifies
H^i(L) with T_A H^i(C). Naturality of σ and the adjunction triangle identity cancel
the unit in b against the counit. The remaining composite is Q(σ_C), followed by
the right-derived unit, hence exactly q. If t.hom is eqToHom of an equality,
eliminate that equality and identify t with Iso.refl by extensionality. This proves
the stated identity normalization without an assertion about invertibility. -/
theorem exists_affinePushforwardCohomologyEdge
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∃ α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (C : CochainComplex (ModuleCat.{u} A) ℤ)
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
          (affinePushforwardRepresentativeCohomologyIso A C L.obj t i).hom) ≫ α.app L := by
  obtain ⟨α, hα⟩ := exists_affinePushforwardCohomologyEdge_identity A B φ i σ
  refine ⟨α, ?_⟩
  intro C L t ht
  rcases L with ⟨K, hK⟩
  obtain ⟨h, ht⟩ := ht
  cases h
  have ht' : t = Iso.refl _ := Iso.ext ht
  subst t
  simpa using hα C hK

end AlgebraicGeometry
