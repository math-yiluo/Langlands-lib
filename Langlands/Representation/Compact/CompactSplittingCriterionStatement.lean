import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Category.Subquotients
import Langlands.CategoryTheory.RenardCategoryDecomposition
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # The compact part splits off exactly under (KF) (Renard IV.1.7, Proposition)

For a unimodular t.d. group countable at infinity, the category of smooth representations
decomposes as the product of the full subcategory of representations all of whose irreducible
subquotients are compact and the full subcategory of those with no compact irreducible
subquotient, if and only if every compact open subgroup has nonzero fixed vectors in only
finitely many isomorphism classes of irreducible compact representations.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.7, Proposition: let `G` be a Hausdorff, locally compact, totally disconnected
group, countable at infinity, with a regular Haar measure that is also right invariant
(unimodular). Let `M(G)_c` be the full subcategory of smooth representations (carriers in
`Type v`) all of whose irreducible subquotients have compactly supported smooth coefficients,
and `M(G)_nc` that of smooth representations none of whose irreducible subquotients has this
property. Then `M(G) = M(G)_c × M(G)_nc` in the sense of A.IX if and only if (KF) holds: for
every compact open subgroup `K`, only finitely many isomorphism classes of irreducible smooth
representations with compactly supported smooth coefficients have a nonzero `K`-fixed vector. -/
def CompactSplittingCriterionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant],
    let compactPart : ObjectProperty (SmoothRep.{0, u, v} ℂ G) := fun V =>
      ∀ π : SmoothRep.{0, u, v} ℂ G, π.IsIrreducible → SmoothRep.IsSubquotient π V →
        HasCompactSmoothDualCoefficients π.representation
    let noncompactPart : ObjectProperty (SmoothRep.{0, u, v} ℂ G) := fun V =>
      ∀ π : SmoothRep.{0, u, v} ℂ G, π.IsIrreducible → SmoothRep.IsSubquotient π V →
        ¬ HasCompactSmoothDualCoefficients π.representation
    Renard.IsCategoryDecomposition
        (fun b : Bool => if b then compactPart else noncompactPart) ↔
      ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
        {c : CompactCoefficientClass.{u, v} G |
          CompactCoefficientClass.HasFixedVector (K : Subgroup G) c}.Finite

end Langlands.Renard.CompactRepresentation
