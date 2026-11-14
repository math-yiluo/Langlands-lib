import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyStatement

/-!
# From packaged local fields to the published mirabolic nondegeneracy statement

The all-field proof of Theorem 4.9 of Bernstein and Zelevinsky (1977) is stated for a
packaged field `F : LocalFieldPackage` with explicit `F.TopologicalData`. This module
shows that such a theorem, for every package and every topological datum, implies the
published statement `LocalFieldMirabolicNondegeneracyStatement`, which quantifies over
ambient `Field`, `ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField`
instances.
-/

namespace Langlands.Whittaker.LocalFieldMirabolicNondegeneracyBridge

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.AllFieldBZ

universe uF uV

/-- The packaged form of BZ77 Theorem 4.9, for every packaged field and topological
datum, implies the published statement at the same universes. The packaged field is
`LocalFieldPackage.ofField F` and the datum is `LocalFieldData.ofInstances F`; both
reduce definitionally to the ambient instances. -/
theorem localFieldMirabolicNondegeneracy_of_packaged
    (h : ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
      (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      letI := T.topology
      IsGeneric ψ n π →
      ∀ U : Subrepresentation (π.comp (mirabolic n F.Carrier).subtype),
        Subsingleton
          (Jacquet.Localization.Coinvariants U.toRepresentation
            (Mirabolic.upperUnipotent n F.Carrier)
            ((standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom)) →
        U = ⊥) :
    LocalFieldMirabolicNondegeneracyStatement.{uF, uV} := by
  intro F _ _ _ _ n ψ V _ _ π hgen U hU
  exact h (LocalFieldPackage.ofField F) (LocalFieldData.ofInstances F) ψ n π hgen U hU

end Langlands.Whittaker.LocalFieldMirabolicNondegeneracyBridge
