import Langlands.ClassFieldTheory.Local.UnramifiedInvariant
import Langlands.ClassFieldTheory.Local.Invariants
import Langlands.Weil.Local.ExtensionResidue

/-! # Restriction of arithmetic Frobenius coordinates in finite base-change squares -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- In a compatible square of finite p-adic fields, the positive arithmetic
generator of an unramified `M/E` restricts to `L` with `L/F`-coordinate equal
to the relative residue degree of `E/F`. -/
def UnramifiedBaseChangeCoordinateCompatibility : Prop :=
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
    (_hFL : F.canonicalTopologicalData.ramificationIndex =
      L.canonicalTopologicalData.ramificationIndex)
    (_hEM : E.canonicalTopologicalData.ramificationIndex =
      M.canonicalTopologicalData.ramificationIndex),
    letI : NeZero (Module.finrank F.Carrier L.Carrier) := ⟨Module.finrank_pos.ne'⟩
    letI : NeZero (Module.finrank E.Carrier M.Carrier) := ⟨Module.finrank_pos.ne'⟩
    ∀ (χL : Gal(L.Carrier/F.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank F.Carrier L.Carrier)))
      (χM : Gal(M.Carrier/E.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank E.Carrier M.Carrier))),
      IsArithmeticUnramifiedCoordinate F L.Carrier χL →
      IsArithmeticUnramifiedCoordinate E M.Carrier χM →
        χL (((cyclicCoordinateGenerator χM).restrictScalars F.Carrier).restrictNormal
            L.Carrier) =
          Multiplicative.ofAdd
            ((Langlands.Weil.Local.extensionResidueDegree F E
              (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier) :
                ZMod (Module.finrank F.Carrier L.Carrier)))

end Langlands.ClassFieldTheory.Local
