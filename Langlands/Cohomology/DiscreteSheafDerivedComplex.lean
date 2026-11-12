import Langlands.Sheaf.Equivariant.TwistedCompactComparison
import Langlands.Cohomology.DerivedPlus

/-!
# Derived section complexes of discrete sheaves on sites

The right derived functors of sections of discrete module sheaves, packaged as
single objects of bounded below derived categories: sections over an object with
an admissible local action, as a complex of smooth representations of the acting
open subgroup; smooth compactly supported global sections on a twisted site, as a
complex of smooth representations of `G`, and their `G`-invariants, as a complex
of modules; and compactly supported sections of module sheaves on a site with
points, as a complex of modules. Their cohomology in each degree `q ≥ 0` is the
corresponding derived functor, and it vanishes in negative degrees.
-/

noncomputable section

namespace Langlands.Cohomology.DiscreteSheafDerivedComplex

open CategoryTheory CategoryTheory.Limits
open Langlands.Sheaf.Equivariant Langlands.Sheaf.PointSupport

universe w w' w'' v u uG uR uI

section Sections

variable {T : Type u} [Category.{v} T]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (R : Type uR) [CommRing R] (L : LocalActionSystem T G) (J : GrothendieckTopology T)
variable [HasSheafify J (ModuleCat.{w} R)] [L.HasFiniteEquivariantRefinements J]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w'} (L.DiscreteSheaf (ModuleCat.{w} R) J)]
variable {U : T} {H : OpenSubgroup G} {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ}
variable [HasDerivedCategory.{w''} (SmoothRep.{uR, uG, w} R (H : Subgroup G))]

/-- The derived section complex over an object with an admissible local action of
`H`, on discrete module sheaves, in the bounded below derived category of smooth
representations of `H`. -/
def sectionsComplex (ha : L.IsAdmissible U H a) :
    L.DiscreteSheaf (ModuleCat.{w} R) J ⥤
      DerivedCategory.Plus (SmoothRep.{uR, uG, w} R (H : Subgroup G)) :=
  DerivedPlus.derivedComplex (discreteSectionsSmooth R L J ha)

/-- Cohomology of the derived section complex in degree `q` is
`discreteDerived R L J ha q`. -/
def sectionsComplexHomologyIso (ha : L.IsAdmissible U H a)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) J) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (SmoothRep.{uR, uG, w} R (H : Subgroup G)) q).obj
        ((sectionsComplex R L J ha).obj F) ≅
      (discreteDerived R L J ha q).obj F :=
  DerivedPlus.homologyIso (discreteSectionsSmooth R L J ha) (injectiveResolution F) q

theorem isZero_sectionsComplex_homology (ha : L.IsAdmissible U H a)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) J) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (SmoothRep.{uR, uG, w} R (H : Subgroup G)) n).obj ((sectionsComplex R L J ha).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (discreteSectionsSmooth R L J ha) F hn

end Sections

section SheafCompact

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {I : Type uI} (Φ : I → J.Point.{w}) [TopologicalSpace I]
variable (R : Type w) [CommRing R]
variable [LocallySmall.{w} C] [HasSheafify J (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w'} (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w''} (ModuleCat.{w} R)]

/-- The derived compactly supported section complex over `X₀` of module sheaves on
a site with points, in the bounded below derived category of modules. -/
def sheafCompactComplex (X₀ : C) :
    Sheaf J (ModuleCat.{w} R) ⥤ DerivedCategory.Plus (ModuleCat.{w} R) :=
  DerivedPlus.derivedComplex (sheafCompactSections J Φ R X₀)

/-- Cohomology of the derived compactly supported section complex in degree `q` is
`compactDerived J Φ R X₀ q`. -/
def sheafCompactComplexHomologyIso (X₀ : C) (F : Sheaf J (ModuleCat.{w} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) q).obj
        ((sheafCompactComplex J Φ R X₀).obj F) ≅
      (compactDerived J Φ R X₀ q).obj F :=
  DerivedPlus.homologyIso (sheafCompactSections J Φ R X₀) (injectiveResolution F) q

omit [LocallySmall.{w} C] in
theorem isZero_sheafCompactComplex_homology (X₀ : C) (F : Sheaf J (ModuleCat.{w} R))
    {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) n).obj
      ((sheafCompactComplex J Φ R X₀).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (sheafCompactSections J Φ R X₀) F hn

end SheafCompact

section TwistedCompact

open Langlands.Sheaf.Equivariant.TwistedOver

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable (J : GrothendieckTopology (P.Over ⊤ X))
variable {I : Type uI} [MulAction G I] {Φ : I → J.Point.{w}}
variable [P.ContainsIdentities] (R : Type w) [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)]
variable [TopologicalSpace I] [ContinuousConstSMul G I]
variable [IsTranslationInvariant (ρ := ρ) J]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w'} (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))]

section Smooth

variable [HasDerivedCategory.{w''} (SmoothRep.{w, uG, w} R G)]

/-- The derived complex of smooth compactly supported global sections of discrete
module sheaves on the twisted site, in the bounded below derived category of
smooth representations of `G`. -/
def compactComplex (E : PointEquivariance ρ Φ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤
      DerivedCategory.Plus (SmoothRep.{w, uG, w} R G) :=
  DerivedPlus.derivedComplex (discreteCompactSections J R L E)

/-- Cohomology of the derived compact section complex in degree `q` is
`discreteCompactDerived J R L E q`. -/
def compactComplexHomologyIso (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (SmoothRep.{w, uG, w} R G) q).obj
        ((compactComplex J R L E).obj F) ≅
      (discreteCompactDerived J R L E q).obj F :=
  DerivedPlus.homologyIso (discreteCompactSections J R L E) (injectiveResolution F) q

theorem isZero_compactComplex_homology (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (SmoothRep.{w, uG, w} R G) n).obj
      ((compactComplex J R L E).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (discreteCompactSections J R L E) F hn

end Smooth

section Invariant

variable [HasDerivedCategory.{w''} (ModuleCat.{w} R)]

/-- The derived complex of `G`-invariant compactly supported global sections of
discrete module sheaves on the twisted site, in the bounded below derived
category of modules. -/
def invariantCompactComplex (E : PointEquivariance ρ Φ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤
      DerivedCategory.Plus (ModuleCat.{w} R) :=
  DerivedPlus.derivedComplex (discreteInvariantCompactSections J R L E)

/-- Cohomology of the derived invariant compact section complex in degree `q` is
`discreteInvariantCompactDerived J R L E q`. -/
def invariantCompactComplexHomologyIso (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) q).obj
        ((invariantCompactComplex J R L E).obj F) ≅
      (discreteInvariantCompactDerived J R L E q).obj F :=
  DerivedPlus.homologyIso (discreteInvariantCompactSections J R L E) (injectiveResolution F) q

theorem isZero_invariantCompactComplex_homology (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) n).obj
      ((invariantCompactComplex J R L E).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (discreteInvariantCompactSections J R L E) F hn

end Invariant

end TwistedCompact

end Langlands.Cohomology.DiscreteSheafDerivedComplex
