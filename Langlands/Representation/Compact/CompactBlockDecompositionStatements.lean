import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.SubrepresentationLattice
import Langlands.CategoryTheory.RenardCategoryDecomposition
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Projectivity, injectivity and block decompositions for compact representations
(Renard IV.1.6–IV.1.7)

For a unimodular t.d. group countable at infinity: every irreducible compact representation is
projective and injective in `M(G)`; the full subcategory `M(G)_c` of representations all of whose
irreducible subquotients are compact is semisimple, and its simple objects are projective and
injective in it; for finitely many irreducible compact classes `τ₁, …, τᵣ`,
`M(G) = ∏ᵢ M(G)_{τᵢ} × [M(G) \ τ₁, …, τᵣ]`; and `M(G)_c = ∏_{τ ∈ Irr(G)_c} M(G)_τ`.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- Renard IV.1.6, notation `M(G)_c`: smooth representations all of whose irreducible
subquotients have compactly supported smooth coefficients. -/
def compactPart : ObjectProperty (SmoothRep.{0, u, v} ℂ G) := fun V =>
  ∀ π : SmoothRep.{0, u, v} ℂ G, π.IsIrreducible → SmoothRep.IsSubquotient π V →
    HasCompactSmoothDualCoefficients π.representation

/-- Renard IV.1.6, notation `M(G)_τ`, for the class `c` of `τ`: `V` is the internal direct sum
of a family of subrepresentations, each irreducible with compact coefficients and of class `c`. -/
def isotypicPart (c : CompactCoefficientClass.{u, v} G) :
    ObjectProperty (SmoothRep.{0, u, v} ℂ G) := fun V =>
  ∃ (ι : Type v) (W : ι → Subrepresentation V.representation),
    iSupIndep W ∧ iSup W = ⊤ ∧
      ∀ i, ∃ h : irreducibleCompactCoefficientProperty G (SmoothRep.subrepresentation V (W i)),
        CompactCoefficientClass.ofRep ⟨SmoothRep.subrepresentation V (W i), h⟩ = c

/-- Renard IV.1.6, notation `[M(G) \ τ₁, …, τᵣ]`, for the set `S` of the classes of the `τᵢ`:
no irreducible subquotient of `V` is isomorphic to some `τᵢ`. -/
def avoidingPart (S : Set (CompactCoefficientClass.{u, v} G)) :
    ObjectProperty (SmoothRep.{0, u, v} ℂ G) := fun V =>
  ∀ (π : SmoothRep.{0, u, v} ℂ G) (h : irreducibleCompactCoefficientProperty G π),
    SmoothRep.IsSubquotient π V → CompactCoefficientClass.ofRep ⟨π, h⟩ ∉ S

/-- Renard IV.1.6, Proposition: every irreducible compact representation `τ` is projective and
injective in `M(G)`. -/
def CompactProjectiveInjectiveStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant] (τ : SmoothRep.{0, u, v} ℂ G),
    τ.IsIrreducible → HasCompactSmoothDualCoefficients τ.representation →
      Projective τ ∧ Injective τ

/-- Renard IV.1.6, sentence before the Proposition: `M(G)_c` is semisimple (every object is a
semisimple representation), and every simple object of `M(G)_c` is projective and injective in
`M(G)_c`. -/
def CompactPartSemisimpleStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant],
    (∀ V : SmoothRep.{0, u, v} ℂ G, compactPart G V →
        Representation.IsSemisimpleRepresentation V.representation) ∧
      ∀ (V : SmoothRep.{0, u, v} ℂ G) (hV : compactPart G V), V.IsIrreducible →
        Projective (C := (compactPart.{u, v} G).FullSubcategory) ⟨V, hV⟩ ∧
          Injective (C := (compactPart.{u, v} G).FullSubcategory) ⟨V, hV⟩

/-- Renard IV.1.7, first display: for an irreducible compact `τ` of class `c`,
`M(G) = M(G)_τ × [M(G) \ τ]` in the sense of A.IX. -/
def IsotypicSplittingStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant] (c : CompactCoefficientClass.{u, v} G),
    Renard.IsCategoryDecomposition
      (fun b : Bool => if b then isotypicPart G c else avoidingPart G {c})

/-- Renard IV.1.7, second display: for pairwise non-isomorphic irreducible compact
`τ₁, …, τᵣ`, given by the finite set `S` of their classes,
`M(G) = ∏ᵢ M(G)_{τᵢ} × [M(G) \ τ₁, …, τᵣ]` in the sense of A.IX; the index `none` is the last
factor. -/
def FiniteIsotypicSplittingStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant] (S : Finset (CompactCoefficientClass.{u, v} G)),
    Renard.IsCategoryDecomposition
      (fun i : Option S => i.elim (avoidingPart G (S : Set (CompactCoefficientClass.{u, v} G)))
        (fun c => isotypicPart G c))

/-- Renard IV.1.7, third display: `M(G)_c = ∏_{τ ∈ Irr(G)_c} M(G)_τ` in the sense of A.IX, inside
the full subcategory `M(G)_c`. -/
def CompactPartDecompositionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant],
    Renard.IsCategoryDecomposition (C := (compactPart.{u, v} G).FullSubcategory)
      (fun (c : CompactCoefficientClass.{u, v} G) X => isotypicPart G c X.obj)

/-- Renard IV.1.6–IV.1.7: the conjunction of the five statements above. -/
def CompactBlockDecompositionStatements : Prop :=
  CompactProjectiveInjectiveStatement.{u, v} ∧ CompactPartSemisimpleStatement.{u, v} ∧
    IsotypicSplittingStatement.{u, v} ∧ FiniteIsotypicSplittingStatement.{u, v} ∧
      CompactPartDecompositionStatement.{u, v}

end Langlands.Renard.CompactRepresentation
