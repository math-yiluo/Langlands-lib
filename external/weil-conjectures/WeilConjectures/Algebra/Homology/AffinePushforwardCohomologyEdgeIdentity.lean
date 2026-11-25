/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
import WeilConjectures.Algebra.Homology.AffineDerivedPushforwardSheafEdge
import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonFactorization

/-! Identity-representative affine cohomology edge normalization. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine edge equation for the canonical representative. The proof is the
identity-representative part of the affine cohomology edge construction, using
Stacks Project, perfect.tex, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-pushforward-cohomology-edge-identity).

Proof: construct the edge transformation from the sheaf-level edge, the supplied
ordinary comparison, and the tilde/Gamma counit. Exactness of tilde identifies
cohomology of the canonical representative; naturality and the adjunction
triangle identity reduce the coordinate composite to the derived-unit edge.
This is the canonical-representative restriction of the full normalization. -/
theorem exists_affinePushforwardCohomologyEdge_identity
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
    ∀ (C : CochainComplex (ModuleCat A) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))),
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map
            (𝟙 _)) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C _ (Iso.refl _) i).hom) ≫
          α.app ⟨_, hK⟩ := by
  let T := affinePushforwardTilde A
  let P := RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let F := ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B
  let σ' : F ≅ T ⋙ P := by
    unfold P RingedSpace.moduleDirectImage
    exact σ
  let J := (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  let G := moduleSpecΓFunctor (R := .of A)
  obtain ⟨ε, hε⟩ := exists_affineDerivedPushforwardSheafEdge A B φ i
  let α := Functor.whiskerLeft (J ⋙ G) σ'.hom ≫
    Functor.whiskerLeft J (Functor.whiskerRight (tilde.adjunction (R := .of A)).counit P) ≫ ε
  refine ⟨α, ?_⟩
  intro C hK
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : T.PreservesHomology := tilde_preservesHomology A
  let : (affinePushforwardTilde B).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : (affinePushforwardTilde B).PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits (affinePushforwardTilde B) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (affinePushforwardTilde B) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let : (T ⋙ P).PreservesZeroMorphisms := ⟨fun X Y => by simp⟩
  let : PreservesFiniteLimits (T ⋙ P) := preservesFiniteLimits_of_natIso σ'
  let : PreservesFiniteColimits (T ⋙ P) := preservesFiniteColimits_of_natIso σ'
  have hn := hε T (fun M => by
    change (tilde (R := .of A) M).IsQuasicoherent
    infer_instance) C hK
  let K := DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj C)
  let HA := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  let k : T.obj (C.homology i) ⟶ HA.obj K :=
    ((C.sc i).mapHomologyIso T).inv ≫
      ((DerivedCategory.homologyFunctorFactors _ i).app
        ((T.mapHomologicalComplex (.up ℤ)).obj C)).inv
  let b := (affinePushforwardRepresentativeCohomologyIso A C K (Iso.refl _) i).hom
  have hb : T.map b ≫ (tilde.adjunction (R := .of A)).counit.app (HA.obj K) = k := by
    dsimp only [b, affinePushforwardRepresentativeCohomologyIso, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom]
    erw [HA.map_id, Category.comp_id]
    change T.map ((tilde.adjunction (R := .of A)).unit.app (C.homology i) ≫
      G.map k) ≫ (tilde.adjunction (R := .of A)).counit.app (HA.obj K) = k
    rw [Functor.map_comp, Category.assoc]
    erw [(tilde.adjunction (R := .of A)).counit.naturality k]
    erw [← Category.assoc, (tilde.adjunction (R := .of A)).left_triangle_components]
    exact Category.id_comp k
  let HB := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
  let R := schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))
  change affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫ HB.map (R.map (𝟙 K)) =
    F.map b ≫ σ'.hom.app (G.obj (HA.obj K)) ≫
      P.map ((tilde.adjunction (R := .of A)).counit.app (HA.obj K)) ≫ ε.app ⟨K, hK⟩
  rw [R.map_id, HB.map_id, Category.comp_id]
  rw [σ'.hom.naturality_assoc b]
  change _ = σ'.hom.app (C.homology i) ≫ P.map (T.map b) ≫
    P.map ((tilde.adjunction (R := .of A)).counit.app (HA.obj K)) ≫ ε.app ⟨K, hK⟩
  rw [← P.map_comp_assoc, hb]
  rw [hn]
  exact affinePushforwardComparison_factorization A B φ i σ C

end AlgebraicGeometry
