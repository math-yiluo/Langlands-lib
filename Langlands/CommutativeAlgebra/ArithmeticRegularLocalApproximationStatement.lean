import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Arithmetic regular local approximation of a strictly Henselian trait -/

universe u v w

open IsLocalRing

namespace Langlands.CommutativeAlgebra

/-- Finite-type factorization through the complement of a regular parameter on a Henselian
local chart. The trait extension preserves the uniformizer and is purely inseparable on residue
fields. This is a finite-data consequence of Deligne, SGA 7 I, Exposé I, §0.5.1–0.5.3 and
Variante 1.3. -/
def ArithmeticRegularLocalApproximationStatement : Prop :=
  ∀ (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    (L : Type v) [Field L] [Algebra W L] [IsFractionRing W L]
    (π : W) (C : Type w) [CommRing C] [Algebra.FiniteType ℤ C]
    (f : C →+* L), Irreducible π →
    ∃ (W' : Type u) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : HenselianLocalRing W') (_ : IsSepClosed (ResidueField W'))
      (i : W →+* W') (_ : IsLocalHom i),
      Irreducible (i π) ∧
      (letI : Algebra (ResidueField W) (ResidueField W') := (ResidueField.map i).toAlgebra
       IsPurelyInseparable (ResidueField W) (ResidueField W')) ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsRegularLocalRing B)
        (_ : HenselianLocalRing B) (t : B) (j : B →+* W') (_ : IsLocalHom j),
        t ∈ maximalIdeal B ∧ t ∉ maximalIdeal B ^ 2 ∧
        IsRegularLocalRing (B ⧸ Ideal.span {t}) ∧ Irreducible (j t) ∧
        (∃ k : Subfield (ResidueField B), Field.FG k ∧ IsPurelyInseparable k (ResidueField B)) ∧
        ∃ (iFrac : L →+* FractionRing W') (jAway : Localization.Away t →+* FractionRing W')
          (g : C →+* Localization.Away t),
          iFrac.comp (algebraMap W L) = (algebraMap W' (FractionRing W')).comp i ∧
          jAway.comp (algebraMap B (Localization.Away t)) =
            (algebraMap W' (FractionRing W')).comp j ∧
          jAway.comp g = iFrac.comp f

end Langlands.CommutativeAlgebra
