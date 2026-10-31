import Langlands.AlgebraicGeometry.Modules.DerivedRestrictionLineBundle
import Langlands.Cohomology.PerfectScalarDerivedTargetSource
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-!
# Base change of perfect models and closed restriction

For a line bundle `L` on `X`, a morphism `f : X ⟶ Spec R`, a strictly perfect complex `K` of
`R`-modules and a derived morphism `a : K ⟶ RΓ_R(X, L)`, and a pullback square
`IsPullback p f' f (Spec.map φ)` with `φ : R ⟶ T`, the `T`-linear adjunct of `a` followed by
the derived base change map is a derived morphism `T ⊗_R K ⟶ RΓ_T(X', p^* L)`
(`perfectModelBaseChange`).

For a closed immersion `g : Y ⟶ X`, a further pullback square `IsPullback q g' g p` and a
derived morphism `a' : K' ⟶ RΓ_R(Y, g^* L)`, the same construction for the outer square,
followed by the isomorphisms `q^* g^* L ≅ g'^* p^* L` and
`RΓ_T(Y', g'^* p^* L) ≅ RΓ_T(X', g'_* g'^* p^* L)`, gives a derived morphism
`T ⊗_R K' ⟶ RΓ_T(X', g'_* g'^* p^* L)` (`perfectModelRestrictionBaseChange`).

If a chain map `ψ : K ⟶ K'` represents derived restriction along `g` in the sense that
`Q ψ ≫ a' = a ≫ derivedRestrictionMap g f L`, then the scalar extension of `ψ` represents the
map induced by the adjunction unit `p^* L ⟶ g'_* g'^* p^* L`
(`perfectModelBaseChange_restriction`).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {X X' Y Y' : Scheme.{u}} {R T : CommRingCat.{u}} {φ : R ⟶ T} {f : X ⟶ Spec R}
  {f' : X' ⟶ Spec T} {p : X' ⟶ X} (hp : IsPullback p f' f (Spec.map φ))
  {g : Y ⟶ X} {q : Y' ⟶ Y} {g' : Y' ⟶ X'} (hq : IsPullback q g' g p)

/-- The `T`-linear adjunct of a derived morphism `a : K ⟶ RΓ_R(X, L)` from a strictly perfect
complex, followed by derived base change along the pullback square `hp`: a derived morphism
from the scalar extension `T ⊗_R K` to `RΓ_T(X', p^* L)`. -/
def perfectModelBaseChange (L : LineBundle X) {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) :
    DerivedCategory.Q.obj ((ModuleComplex.baseChange φ.hom).obj K) ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
        ((Scheme.Modules.pullback p).obj L.obj) :=
  (ModuleComplex.perfectScalarDerivedTargetHomEquiv φ.hom K hK _).symm
    (a ≫ derivedBaseChangeMapLineBundle hp L)

/-- `perfectModelBaseChange` is the adjunct of `a ≫ derivedBaseChangeMapLineBundle hp L`. -/
lemma perfectScalarDerivedTargetHomEquiv_perfectModelBaseChange (L : LineBundle X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) :
    ModuleComplex.perfectScalarDerivedTargetHomEquiv φ.hom K hK _
        (perfectModelBaseChange hp L hK a) =
      a ≫ derivedBaseChangeMapLineBundle hp L :=
  Equiv.apply_symm_apply _ _

/-- For a closed immersion `g`, the scalar-extension adjunct of `a' : K' ⟶ RΓ_R(Y, g^* L)`
along the outer pullback square `q ≫ g ≫ f = g' ≫ f' ≫ Spec.map φ`, followed by
`RΓ_T(Y', q^* g^* L) ≅ RΓ_T(Y', g'^* p^* L) ≅ RΓ_T(X', g'_* g'^* p^* L)`. -/
def perfectModelRestrictionBaseChange [IsClosedImmersion g] (L : LineBundle X)
    {K' : CochainComplex (ModuleCat.{u} R) ℤ} (hK' : ModuleComplex.IsStrictlyPerfect K')
    (a' : DerivedCategory.Q.obj K' ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections (g ≫ f)) ⋙ DerivedCategory.Plus.ι).obj
        ((Scheme.Modules.pullback g).obj L.obj)) :
    DerivedCategory.Q.obj ((ModuleComplex.baseChange φ.hom).obj K') ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
        ((Scheme.Modules.pushforward g').obj ((Scheme.Modules.pullback g').obj
          ((Scheme.Modules.pullback p).obj L.obj))) :=
  haveI := isClosedImmersion_of_isPullback hq
  perfectModelBaseChange (hq.paste_vert hp) ((LineBundle.pullback g).obj L) hK' a' ≫
    (DerivedPlus.derivedComplex (relativeGlobalSections (g' ≫ f')) ⋙
      DerivedCategory.Plus.ι).map ((pullbackSquareIso p g g' q hq.w).hom.app L.obj) ≫
    (derivedPushforwardComparisonIso g' f' _
      (isZero_higherDirectImage_of_isClosedImmersion g' _)).hom

set_option backward.isDefEq.respectTransparency false in
/-- `perfectModelRestrictionBaseChange` is an isomorphism exactly when the scalar-extension
adjunct for the outer square is. -/
lemma isIso_perfectModelRestrictionBaseChange_iff [IsClosedImmersion g] (L : LineBundle X)
    {K' : CochainComplex (ModuleCat.{u} R) ℤ} (hK' : ModuleComplex.IsStrictlyPerfect K')
    (a' : DerivedCategory.Q.obj K' ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections (g ≫ f)) ⋙ DerivedCategory.Plus.ι).obj
        ((Scheme.Modules.pullback g).obj L.obj)) :
    IsIso (perfectModelRestrictionBaseChange hp hq L hK' a') ↔
      IsIso (perfectModelBaseChange (hq.paste_vert hp) ((LineBundle.pullback g).obj L) hK' a') := by
  have := isClosedImmersion_of_isPullback hq
  unfold perfectModelRestrictionBaseChange
  rw [← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

set_option backward.isDefEq.respectTransparency false in
/-- If a chain map `ψ : K ⟶ K'` between strictly perfect complexes represents derived
restriction along the closed immersion `g`, then its scalar extension represents the map
induced on `RΓ_T(X', -)` by the adjunction unit `p^* L ⟶ g'_* g'^* p^* L`. -/
theorem perfectModelBaseChange_restriction [IsClosedImmersion g] (L : LineBundle X)
    {K K' : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (hK' : ModuleComplex.IsStrictlyPerfect K') (ψ : K ⟶ K')
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj)
    (a' : DerivedCategory.Q.obj K' ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections (g ≫ f)) ⋙ DerivedCategory.Plus.ι).obj
        ((Scheme.Modules.pullback g).obj L.obj))
    (h : DerivedCategory.Q.map ψ ≫ a' = a ≫ derivedRestrictionMap g f L.obj) :
    DerivedCategory.Q.map ((ModuleComplex.baseChange φ.hom).map ψ) ≫
        perfectModelRestrictionBaseChange hp hq L hK' a' =
      perfectModelBaseChange hp L hK a ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
            ((Scheme.Modules.pullback p).obj L.obj)) := by
  have := isClosedImmersion_of_isPullback hq
  apply (ModuleComplex.perfectScalarDerivedTargetHomEquiv φ.hom K hK _).injective
  rw [ModuleComplex.perfectScalarDerivedTargetHomEquiv_naturality_source φ.hom hK hK',
    ModuleComplex.perfectScalarDerivedTargetHomEquiv_naturality,
    perfectScalarDerivedTargetHomEquiv_perfectModelBaseChange]
  unfold perfectModelRestrictionBaseChange
  rw [ModuleComplex.perfectScalarDerivedTargetHomEquiv_naturality,
    perfectScalarDerivedTargetHomEquiv_perfectModelBaseChange, Category.assoc,
    reassoc_of% h]
  have key := derivedRestrictionMap_comp_derivedBaseChangeMap_lineBundle_of_isPullback hp hq L
  have hρ : derivedRestrictionMap g' f' ((Scheme.Modules.pullback p).obj L.obj) ≫
      (derivedPushforwardComparisonIso g' f' _
        (isZero_higherDirectImage_of_isClosedImmersion g' _)).hom =
      (DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
          ((Scheme.Modules.pullback p).obj L.obj)) := by
    simp only [derivedRestrictionMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hρ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% key]
  rfl

end Langlands.AlgebraicGeometry.Modules.DerivedSections
