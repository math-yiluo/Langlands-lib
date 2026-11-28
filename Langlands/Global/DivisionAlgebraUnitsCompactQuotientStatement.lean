import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicSplitCenterQuotient
import Langlands.Global.AdelicGroupQuotient
import Langlands.GroupScheme.FiniteAlgebraUnits

/-! # Compactness of the adelic quotients of the units of a central division algebra

For a finite-dimensional central division algebra `A` over a number field `E`, with unit group
scheme `G = GL₁(A)`, the norm-one quotient `G(E) \ G(𝔸_E)¹` and the canonical quotient
`[G] = A_G G(E) \ G(𝔸_E)` are compact. So is the quotient of `G(𝔸_E)` by the positive real
points of `T` and the rational points, for each central homomorphism `i : T ⟶ G` from a split
torus `T` whose character restriction is injective with finite-index range (Fujisaki's lemma;
Godement's compactness criterion for anisotropic groups).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus

/-- Let `A` be a finite-dimensional central division algebra over a number field `E` (a
nontrivial ring all of whose nonzero elements are units), and let `G` be the group scheme of
units of `A`, built from the chosen basis `Module.finBasis E A`, assumed connected reductive.
Then three adelic quotients of `G` are compact: the norm-one rational quotient
`G(E) \ G(𝔸_E)¹`; the canonical quotient `A_G G(E) \ G(𝔸_E)`; and, for every central
homomorphism `i : T ⟶ G` from a split torus `T` whose character restriction is injective with
finite-index range, the quotient of `G(𝔸_E)` by the positive real points of `T` and the rational
points. -/
def DivisionAlgebraUnitsCompactQuotientStatement : Prop :=
  ∀ (E A : Type) [Field E] [NumberField E] [Ring A] [Nontrivial A] [Algebra E A]
    [FiniteDimensional E A] [Algebra.IsCentral E A],
    (∀ a : A, a ≠ 0 → IsUnit a) →
    let G := FiniteAlgebraUnits.groupScheme (Module.finBasis E A)
    IsConnectedReductive G →
    CompactSpace (NormOneRationalQuotient E G) ∧
    CompactSpace (RestrictionSplitCentre.CanonicalQuotient E G) ∧
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of E))) (i : T.toGrp ⟶ G),
      Function.Injective (characterRestrict i) →
      ∀ [(characterRestrict i).range.FiniteIndex]
        (I : Type) [Fintype I] (_e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of E)) I),
        IsCentral i → CompactSpace (PositiveRationalQuotient E G T i)

end Langlands.Global
