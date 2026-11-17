import Langlands.Representation.Families.RenardFamilyConstituents
import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.CuspidalSupport.RationalInertiaCoproducts
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # The Bernstein component set under coefficient spans and direct sums -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme Langlands.CuspidalSupport
open Langlands.Jacquet.CoefficientRestriction
open scoped CategoryTheory.MonObj

namespace Langlands.SmoothRep

universe uG uV

/-- An irreducible smooth representation is finitely generated over its
group algebra, since its actual group-algebra module is simple. -/
theorem finite_asModule_of_irreducible
    {G : Type uG} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsIrreducible) :
    Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule := by
  have : IsSimpleModule (MonoidAlgebra ℂ G) A.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hA
  infer_instance

end Langlands.SmoothRep

namespace Langlands.Renard.AlgebraicFamily

universe uF uV uB

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance componentSetTopology : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The actual set of inertial supports occurring among irreducible
subquotients, exactly as in the published finite-type characterizations. -/
def bernsteinComponentSet
    (A : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    Set (BernsteinInertialClass.{uF, max uF uV} i ν family) :=
  {s | ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
    SmoothRep.IsSubquotient π A ∧ IsBernsteinInertialSupport i ν family s π}

/-- Actual subquotients can only decrease the component set. -/
theorem bernsteinComponentSet_mono
    {A D : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (hDA : SmoothRep.IsSubquotient D A) :
    bernsteinComponentSet i ν family D ⊆ bernsteinComponentSet i ν family A := by
  rintro s ⟨π, hπ, hs⟩
  exact ⟨π, Langlands.smoothSubquotientTransitivity ℂ (rationalPoints G)
    _ _ _ hπ hDA, hs⟩

/-- A countable sum of actual subquotients has no component outside the
component set of its ambient representation. -/
theorem bernsteinComponentSet_directSum_subset
    (A : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (D : ℕ → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hD : ∀ n, SmoothRep.IsSubquotient (D n) A) :
    bernsteinComponentSet i ν family (SmoothRep.directSum D) ⊆
      bernsteinComponentSet i ν family A := by
  rintro s ⟨π, hπ, hs⟩
  have hπirr : π.IsIrreducible := by
    obtain ⟨a, _, ha⟩ := hs
    exact ha.1
  obtain ⟨n, hn⟩ := SmoothRep.irreducibleSubquotient_directSum D hπirr hπ
  exact bernsteinComponentSet_mono i ν family (hD n) ⟨π, hn, hs⟩

/-- The underlying family and an actual complex subrepresentation spanning
it over the coefficient algebra have exactly the same component set. -/
theorem bernsteinComponentSet_eq_of_coefficient_span
    {B : Type uB} [CommRing B] [Algebra ℂ B]
    {V : Type (max uF uV)} [AddCommGroup V] [Module B V] [Module ℂ V]
    [IsScalarTower ℂ B V]
    (ρ : Representation B (rationalPoints G) V) (hρ : IsSmooth ρ)
    (S : Subrepresentation (complexRepresentation ρ))
    (hspan : Submodule.span B (S : Set V) = ⊤) :
    let A := SmoothRep.of (complexRepresentation ρ)
      ((isSmooth_complexRepresentation ρ).mpr hρ)
    bernsteinComponentSet i ν family A =
      bernsteinComponentSet i ν family (SmoothRep.subrepresentation A S) := by
  dsimp only
  apply Set.Subset.antisymm
  · rintro s ⟨π, hπ, hs⟩
    have hπirr : π.IsIrreducible := by
      obtain ⟨a, _, ha⟩ := hs
      exact ha.1
    exact ⟨π, irreducibleSubquotient_of_coefficient_span ρ hρ S hspan π hπirr hπ, hs⟩
  · exact bernsteinComponentSet_mono i ν family
      (SmoothRep.subrepresentation_isSubrepresentation
        (A := SmoothRep.of (complexRepresentation ρ)
          ((isSmooth_complexRepresentation ρ).mpr hρ)) S).isSubquotient

end Langlands.Renard.AlgebraicFamily
