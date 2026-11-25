/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical direct-image transport to affine spectrum coordinates

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: def-pc-affine-spectrum-direct-image-coordinates).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The inverse spectrum pullback equivalence, constructed from the selected composition
and identity comparisons. Source: Stacks Project, Tag 0D5S.
(blueprint: def-pc-affine-spectrum-direct-image-coordinates). -/
def affineSpectrumInversePullbackEquivalence (X : Scheme.{u}) [IsAffine X] :
    schemeDerivedCategory X ≌ schemeDerivedCategory (Spec Γ(X, ⊤)) := by
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  exact CategoryTheory.Equivalence.mk
    (C := schemeDerivedCategory X) (D := schemeDerivedCategory (Spec Γ(X, ⊤)))
    (derivedPullback X.isoSpec.inv) (derivedPullback X.isoSpec.hom)
    (c X.isoSpec.hom X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫ i X).symm
    (c X.isoSpec.inv X.isoSpec.hom ≪≫
      eqToIso (congrArg (fun k : Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤) ↦ derivedPullback k)
        X.isoSpec.inv_hom_id) ≪≫
        i (Spec Γ(X, ⊤)))

/-- The direct-image coordinate isomorphism is the conjugate of the selected pullback
coordinate comparison. Its data are constructed, with no existence witness for an
arbitrary coordinate isomorphism. Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: def-pc-affine-spectrum-direct-image-coordinates). -/
def affineSpectrumDerivedDirectImageIso {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    schemeDerivedDirectImage f ≅
      derivedPullback X.isoSpec.inv ⋙
        schemeDerivedDirectImage (Spec.map f.appTop) ⋙ derivedPullback S.toSpecΓ := by
  let adj : ∀ {P Q : Scheme.{u}} (k : P ⟶ Q),
      derivedPullback k ⊣ schemeDerivedDirectImage k := fun k ↦
    Classical.choose (exists_schemeDerivedAdjunction k
      (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) k))
  let ex := affineSpectrumInversePullbackEquivalence X
  let es := affineSpectrumInversePullbackEquivalence S
  let d : derivedPullback X.isoSpec.hom ⋙ schemeDerivedDirectImage f ≅
      schemeDerivedDirectImage (Spec.map f.appTop) ⋙ derivedPullback S.isoSpec.hom :=
    conjugateIsoEquiv ((adj f).comp ex.toAdjunction)
      (es.toAdjunction.comp (adj (Spec.map f.appTop)))
      (affineSpectrumDerivedPullbackIso f)
  exact (Functor.leftUnitor (schemeDerivedDirectImage f)).symm ≪≫
    Functor.isoWhiskerRight ex.unitIso (schemeDerivedDirectImage f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPullback X.isoSpec.inv) d

/-- Forward spectrum pullback comparison, using naturality of the spectrum map.
Source: Stacks Project, Tag 0D5S.
(blueprint: def-pc-affine-spectrum-direct-image-coordinates). -/
def affineSpectrumForwardPullbackIso {S S' : Scheme.{u}}
    [IsAffine S] [IsAffine S'] (g : S' ⟶ S) :
    derivedPullback S.toSpecΓ ⋙ derivedPullback g ≅
      derivedPullback (Spec.map g.appTop) ⋙ derivedPullback S'.toSpecΓ := by
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  exact c g S.toSpecΓ ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.toSpecΓ_naturality g)) ≪≫
      (c S'.toSpecΓ (Spec.map g.appTop)).symm

/-- The source coordinate isomorphism, obtained by applying pullback to the canonical
right-adjoint coordinate isomorphism. Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: def-pc-affine-spectrum-direct-image-coordinates). -/
def affineSpectrumBaseChangeSourceIso {X S S' : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsAffine S'] (f : X ⟶ S) (g : S' ⟶ S) :
    schemeDerivedDirectImage f ⋙ derivedPullback g ≅
      derivedPullback X.isoSpec.inv ⋙ schemeDerivedDirectImage (Spec.map f.appTop) ⋙
        derivedPullback (Spec.map g.appTop) ⋙ derivedPullback S'.toSpecΓ :=
  Functor.isoWhiskerRight (affineSpectrumDerivedDirectImageIso f) (derivedPullback g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPullback X.isoSpec.inv)
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (schemeDerivedDirectImage (Spec.map f.appTop))
          (affineSpectrumForwardPullbackIso g))

end AlgebraicGeometry
