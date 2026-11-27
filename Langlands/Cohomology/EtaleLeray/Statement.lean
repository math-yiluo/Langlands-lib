import Langlands.Cohomology.AnalyticGlobalSpectralSequence.Statement
import Langlands.Geometry.EtaleDerivedDirectImage

/-!
# The Leray spectral sequence on the small étale site

Milne, *Étale Cohomology*, III.1, Theorem 1.18(a), for actual scheme
morphisms with coefficients in a constant commutative ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry EtaleDerivedSections EtaleDerivedDirectImage

set_option autoImplicit false

universe u wS wX

namespace Langlands.Cohomology.EtaleLeray

open AnalyticGlobalSpectralSequence

variable {X S : Scheme.{u}} (f : X ⟶ S) (R : Type u) [CommRing R]

/-- The sheaf representing sections is the constant regular module. -/
def sectionRepresenter : ModuleSheaf S R :=
  (constantSheaf S.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)

variable [hS : HasDerivedCategory.{wS} (ModuleSheaf S R)]
variable [hX : HasDerivedCategory.{wX} (ModuleSheaf X R)]

include hS hX

/-- The geometric direct image in the ordinary derived category. -/
def geometricDirectImage (F : ModuleSheaf X R) : DerivedCategory (ModuleSheaf S R) :=
  DerivedCategory.Plus.ι.obj
    ((derivedDirectImage.{u, wS, wX} f R).obj F)

/-- The actual covariant hyperext sequence from the constant regular sheaf
into the derived geometric direct image. -/
def leraySpectralSequence (F : ModuleSheaf X R) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{wS} :=
  spectralSequence (geometricDirectImage.{u, wS, wX} f R F)
    (sectionRepresenter (S := S) R)

/-- The Leray sequence has `H^i(S, R^j f_* F)` on page two and abuts to
`H^(i+j)(X, F)` with the finite first-quadrant filtration. -/
def EtaleLerayStatement (F : ModuleSheaf X R) : Prop :=
  (∀ i j : ℕ, Nonempty (((leraySpectralSequence.{u, wS, wX} f R F).page 2).X
    ((i : ℤ), (j : ℤ)) ≃+ (cohomology S R i).obj ((higherDirectImage f R j).obj F))) ∧
  FirstQuadrantAbutmentStatement
    (geometricDirectImage.{u, wS, wX} f R F) (sectionRepresenter (S := S) R)
    (fun n => AddCommGrpCat.of ((cohomology X R n).obj F))

end Langlands.Cohomology.EtaleLeray
