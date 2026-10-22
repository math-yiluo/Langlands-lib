import Langlands.ClassFieldTheory.Local.UnramifiedInvariant
import Langlands.ClassFieldTheory.Local.Invariants

/-! # Compatibility targets for the explicit finite unramified invariant -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Arithmetic finite unramified invariants agree under the actual inflation map. -/
def UnramifiedInvariantInflationCompatibility : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F L M : PadicField.{u} p)
    [Algebra F.Carrier L.Carrier] [Algebra F.Carrier M.Carrier]
    [Algebra L.Carrier M.Carrier]
    [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [IsScalarTower F.Carrier L.Carrier M.Carrier]
    [FiniteDimensional F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier M.Carrier]
    [IsGalois F.Carrier L.Carrier] [IsGalois F.Carrier M.Carrier]
    (hFL : F.canonicalTopologicalData.ramificationIndex =
      L.canonicalTopologicalData.ramificationIndex)
    (hFM : F.canonicalTopologicalData.ramificationIndex =
      M.canonicalTopologicalData.ramificationIndex),
    letI : NeZero (Module.finrank F.Carrier L.Carrier) := ⟨Module.finrank_pos.ne'⟩
    letI : NeZero (Module.finrank F.Carrier M.Carrier) := ⟨Module.finrank_pos.ne'⟩
    ∀ (χL : Gal(L.Carrier/F.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank F.Carrier L.Carrier)))
      (χM : Gal(M.Carrier/F.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank F.Carrier M.Carrier))),
      IsArithmeticUnramifiedCoordinate F L.Carrier χL →
      IsArithmeticUnramifiedCoordinate F M.Carrier χM →
      ∀ x : relativeCohomology F.Carrier L.Carrier 2,
        unramifiedH2Invariant F M hFM χM
            (relativeInflation F.Carrier L.Carrier M.Carrier 2 x) =
          unramifiedH2Invariant F L hFL χL x

/-- Finite unramified invariants multiply by the base degree under actual
inflation followed by restriction in a compatible square of fields. -/
def UnramifiedInvariantBaseChangeCompatibility : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F E L M : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier] [Algebra F.Carrier L.Carrier]
    [Algebra F.Carrier M.Carrier] [Algebra E.Carrier M.Carrier]
    [Algebra L.Carrier M.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [IsScalarTower (Padic p) E.Carrier M.Carrier]
    [IsScalarTower F.Carrier E.Carrier M.Carrier]
    [IsScalarTower F.Carrier L.Carrier M.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier L.Carrier]
    [FiniteDimensional E.Carrier M.Carrier]
    [IsGalois F.Carrier L.Carrier] [IsGalois E.Carrier M.Carrier]
    (hFL : F.canonicalTopologicalData.ramificationIndex =
      L.canonicalTopologicalData.ramificationIndex)
    (hEM : E.canonicalTopologicalData.ramificationIndex =
      M.canonicalTopologicalData.ramificationIndex),
    letI : NeZero (Module.finrank F.Carrier L.Carrier) := ⟨Module.finrank_pos.ne'⟩
    letI : NeZero (Module.finrank E.Carrier M.Carrier) := ⟨Module.finrank_pos.ne'⟩
    ∀ (χL : Gal(L.Carrier/F.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank F.Carrier L.Carrier)))
      (χM : Gal(M.Carrier/E.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank E.Carrier M.Carrier))),
      IsArithmeticUnramifiedCoordinate F L.Carrier χL →
      IsArithmeticUnramifiedCoordinate E M.Carrier χM →
      ∀ x : relativeCohomology F.Carrier L.Carrier 2,
        unramifiedH2Invariant E M hEM χM
            (relativeRestriction F.Carrier E.Carrier M.Carrier 2
              (relativeInflation F.Carrier L.Carrier M.Carrier 2 x)) =
          Module.finrank F.Carrier E.Carrier •
            unramifiedH2Invariant F L hFL χL x

end Langlands.ClassFieldTheory.Local
