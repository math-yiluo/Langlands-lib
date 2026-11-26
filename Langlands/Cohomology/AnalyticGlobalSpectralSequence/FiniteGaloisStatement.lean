import Langlands.Cohomology.AnalyticGaloisSiteCover
import Langlands.Cohomology.AnalyticGlobalSpectralSequence.Statement

/-!
# Finite Galois covering spectral sequence on the analytic étale site

The ordinary finite-cover Hochschild–Serre construction on actual
étale objects of an analytic space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL w uC vC

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology

namespace GaloisCovering

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  {Γ : Type w} [Group Γ] {V' V : C} (g : GaloisCovering J Γ V' V)
  (R : Type w) [CommRing R]

/-- Evaluation on the cover with its actual deck action, functorial in
every sheaf morphism. -/
def sectionsWithDeck : Sheaf J (ModuleCat.{w} R) ⥤ Rep.{w} R Γ where
  obj F := g.rep F
  map {F F'} a := Rep.ofHom
    ⟨(a.hom.app (op V')).hom, fun γ => by
      ext x
      exact NatTrans.naturality_apply a.hom (g.deck γ⁻¹).op x⟩
  map_id F := by
    ext x
    rfl
  map_comp a b := by
    ext x
    rfl

instance : (sectionsWithDeck g R).Additive where
  map_add := rfl

end GaloisCovering

namespace AnalyticGlobalSpectralSequence

universe wRep

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (X : LocalizedCategory.{u, v, v} (K := K))
  {Γ : Type (max u (v + 1) uL)} [Group Γ]
  {V' V : EtaleSite X} (p : V' ⟶ V) (c : AnalyticGaloisCover Γ p.left)
  (R : Type (max u (v + 1) uL)) [CommRing R]

/-- For a finite analytic Galois covering in the étale site, the
specified covariant hyperext spectral sequence has the derived
deck invariants on page two and converges to the cohomology of the
covered object. -/
def AnalyticEtaleFiniteGaloisSpectralSequenceStatement [Finite Γ] : Prop :=
  ∀ [HasDerivedCategory.{wRep} (Rep.{max u (v + 1) uL} R Γ)]
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)),
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  letI : HasExt.{wRep} (Rep.{max u (v + 1) uL} R Γ) := hasExt_of_hasDerivedCategory _
  let T := (c.toEtaleSiteCover p).sectionsWithDeck R
  let D := DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex T).obj F)
  let A := Rep.trivial (G := Γ) R R
  (∀ i j : ℕ, Nonempty (((spectralSequence D A).page 2).X ((i : ℤ), (j : ℤ)) ≃+
    Abelian.Ext.{wRep} A ((T.rightDerived j).obj F) i)) ∧
  FirstQuadrantAbutmentStatement D A
    (fun n => AddCommGrpCat.of ((sectionsDerived (etaleTopology X) R V n).obj F))

end AnalyticGlobalSpectralSequence
end Langlands.Cohomology
