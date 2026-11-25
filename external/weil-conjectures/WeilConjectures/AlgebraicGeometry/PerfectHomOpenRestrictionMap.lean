/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Unshifted restriction of a representing pullback Hom cocone

Source: Stacks Project, Cohomology, Tags 079W and 08FE; perfect.tex, Tag 09RE.
(blueprint: def-pc-perfect-hom-open-restriction-map).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

variable {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
  [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The cartesian map induced by the open inclusion, constructed by pullback.map.
Source: Stacks Tag 09RE (blueprint: def-pc-perfect-hom-open-restriction-map). -/
def perfectHomOpenBaseChangeMap : pullback (B.ι ≫ s) r ⟶ pullback s r :=
  pullback.map (B.ι ≫ s) r s r B.ι (𝟙 T) (𝟙 S) (by simp) (by simp)

/-- The pullback comparison on the cartesian open square, fixed by the supplied
open pullback adjunction and the existing counit-pinned composition comparisons.
Source: Stacks Tags 079W and 09RE (blueprint: def-pc-perfect-hom-open-restriction-map). -/
def perfectHomOpenPullbackComparison
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) :
    derivedPullback (pullback.fst s r) ⋙ derivedPullback (perfectHomOpenBaseChangeMap s B r) ≅
      schemeMVDerivedRestriction Y B ⋙ derivedPullback (pullback.fst (B.ι ≫ s) r) := by
  let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
    (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  have he : perfectHomOpenBaseChangeMap s B r ≫ pullback.fst s r =
      pullback.fst (B.ι ≫ s) r ≫ B.ι := by
    simp [perfectHomOpenBaseChangeMap, pullback.map]
  exact perfectHomComposition (perfectHomOpenBaseChangeMap s B r) (pullback.fst s r) ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
    (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
    Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))

/-- Restrict a pullback Hom along the explicit cartesian map and conjugate it by
perfectHomOpenPullbackComparison. No existence witness is selected here.
Source: Stacks Tag 09RE (blueprint: def-pc-perfect-hom-open-restriction-map). -/
def perfectHomOpenRestrictionMap
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {M Q : schemeDerivedCategory Y}
    (f : (derivedPullback (pullback.fst s r)).obj M ⟶
      (derivedPullback (pullback.fst s r)).obj Q) :
    (derivedPullback (pullback.fst (B.ι ≫ s) r)).obj
        ((schemeMVDerivedRestriction Y B).obj M) ⟶
      (derivedPullback (pullback.fst (B.ι ≫ s) r)).obj
        ((schemeMVDerivedRestriction Y B).obj Q) :=
  (perfectHomOpenPullbackComparison s B r a).inv.app M ≫
    (derivedPullback (perfectHomOpenBaseChangeMap s B r)).map f ≫
    (perfectHomOpenPullbackComparison s B r a).hom.app Q

end
end AlgebraicGeometry
