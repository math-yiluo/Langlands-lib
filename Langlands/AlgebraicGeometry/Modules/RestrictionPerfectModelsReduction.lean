import Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsStatement
import Langlands.AlgebraicGeometry.Modules.PerfectModelRestriction
import Langlands.Cohomology.PerfectScalarAdjunctionProof

/-!
# Restriction-compatible perfect models from universal perfect models

A *universal perfect model* of `RΓ_R(X, L)` is a strictly perfect complex `K` with a derived
isomorphism `a : K ≅ RΓ_R(X, L)` whose scalar-extension adjunct followed by derived base change
(`perfectModelBaseChange`) is an isomorphism for every pullback square of `f` along a map of
affine schemes. If every line bundle on every smooth proper family over an affine base has such
a model, then `RestrictionPerfectModelsStatement` holds: a chain map between the models of `L`
and of `g^* L` lifts derived restriction, and its scalar extensions represent restriction after
every base change.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

open DerivedSections

/-- A universal perfect model of `RΓ_R(X, L)`: a strictly perfect complex `K` and a derived
isomorphism `a : K ⟶ RΓ_R(X, L)` whose base change `perfectModelBaseChange hp L hK a` is an
isomorphism along every pullback square `hp` of `f` along `Spec.map φ`. -/
def UniversalPerfectModel {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (L : LineBundle X) : Prop :=
  ∃ (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj),
    IsIso a ∧
      ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (X' : Scheme.{u}) (p : X' ⟶ X)
        (f' : X' ⟶ Spec T) (hp : IsPullback p f' f (Spec.map φ)),
        IsIso (perfectModelBaseChange hp L hK a)

/-- A derived morphism out of a strictly perfect complex is the image of a chain map. -/
lemma exists_chainMap_of_isStrictlyPerfect {R : CommRingCat.{u}}
    {K K' : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (x : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj K') :
    ∃ ψ : K ⟶ K', DerivedCategory.Q.map ψ = x := by
  have := ModuleComplex.isKProjective_of_isStrictlyPerfect hK
  obtain ⟨y, hy⟩ := (kProjectiveDerivedHomEquiv K K').surjective x
  obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective y
  rw [kProjectiveDerivedHomEquiv_quotient_map] at hy
  exact ⟨ψ, hy⟩

/-- Universal perfect models for all line bundles on all smooth proper families over affine
bases give restriction-compatible perfect models. -/
theorem restrictionPerfectModels_of_universalPerfectModel
    (H : ∀ (R : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec R), Smooth f → IsProper f →
      ∀ L : LineBundle X, UniversalPerfectModel f L) :
    RestrictionPerfectModelsStatement.{u} := by
  intro R X f hfs hfp L
  obtain ⟨K, hK, a, ha, hbc⟩ := H R X f hfs hfp L
  refine ⟨K, hK, fun T φ X' p f' hp => ?_, ?_⟩
  · have := hbc T φ X' p f' hp
    exact asIso (perfectModelBaseChange hp L hK a)
  intro Y g hg hgf
  have := hfp
  have := hg
  have : IsProper (g ≫ f) := inferInstance
  obtain ⟨K', hK', a', ha', hbc'⟩ :=
    H R Y (g ≫ f) hgf inferInstance ((LineBundle.pullback g).obj L)
  let e : DerivedCategory.Q.obj K' ≅
      (DerivedPlus.derivedComplex (relativeGlobalSections (g ≫ f)) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pullback g).obj L.obj) :=
    @asIso _ _ _ _ a' ha'
  obtain ⟨ψ, hψ⟩ := exists_chainMap_of_isStrictlyPerfect hK
    (a ≫ derivedRestrictionMap g f L.obj ≫ e.inv)
  have h : DerivedCategory.Q.map ψ ≫ a' = a ≫ derivedRestrictionMap g f L.obj := by
    change DerivedCategory.Q.map ψ ≫ e.hom = _
    rw [hψ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨K', hK', ψ, fun T φ X' p f' hp Y' q g' hq => ?_, ?_⟩
  · have := hbc' T φ Y' q (g' ≫ f') (hq.paste_vert hp)
    have := (isIso_perfectModelRestrictionBaseChange_iff hp hq L hK' a').2 inferInstance
    exact asIso (perfectModelRestrictionBaseChange hp hq L hK' a')
  intro T φ X' p f' hp Y' q g' hq
  exact perfectModelBaseChange_restriction hp hq L hK hK' ψ a a' h

end Langlands.AlgebraicGeometry.Modules
