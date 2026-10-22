import Langlands.Representation.Geometric.WeylDefinitions

/-! Concrete GL specializations of the Weyl and Bruhat prerequisites of BZ77. -/

namespace Langlands.Geometric

open GeneralLinear

universe uF

/-- Every Weyl double coset has exactly one representative satisfying both
actual within-block positivity conditions. -/
def WeylMinimalRepresentativeTheorem : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (B C : BlockShape n),
    Function.Bijective (weylDoubleCoset B C)

/-- The actual inverse permutation matrices parametrize parabolic double
cosets for every finite extension of a p-adic field. -/
def PadicParabolicBruhatTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n),
      Function.Bijective (parabolicDoubleCoset F.Carrier B C)

/-- The two actual intersection triples are standard parabolic triples in
their product Levis. Their refinements consist of actual positive blocks. -/
def PadicStandardIntersectionsTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
      (w : MinimalRepresentatives B C),
      (∃ S : BlockRefinement B,
        sourceParabolic F.Carrier B C w.val = refinedParabolic F.Carrier B S ∧
        sourceLevi F.Carrier B C w.val = refinedLevi F.Carrier B S ∧
        sourceUnipotent F.Carrier B C w.val = refinedUnipotent F.Carrier B S) ∧
      (∃ T : BlockRefinement C,
        sourceParabolic F.Carrier C B w.val⁻¹ = refinedParabolic F.Carrier C T ∧
        sourceLevi F.Carrier C B w.val⁻¹ = refinedLevi F.Carrier C T ∧
        sourceUnipotent F.Carrier C B w.val⁻¹ = refinedUnipotent F.Carrier C T)

/-- The three concrete Weyl, Bruhat and intersection prerequisites.
The definition assumes no truth of any clause. -/
def PadicGeometricWeylTheorems : Prop :=
  WeylMinimalRepresentativeTheorem ∧ PadicParabolicBruhatTheorem.{uF} ∧
    PadicStandardIntersectionsTheorem.{uF}

end Langlands.Geometric
