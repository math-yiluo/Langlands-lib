import Langlands.AllFieldBZ.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.AllFieldBZ.Representation.Geometric.RefinementFunctors
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementComposition
import Langlands.Representation.Parabolic.NaturalJacquetDualityStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.NaturalJacquetDualityStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.NaturalJacquetDualityStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding StandardNaturalJacquetDualityClause
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

/-- Natural upper/opposite Jacquet duality for actual standard GL parabolics. -/
def StandardNaturalJacquetDualityClause : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      ∃ E : ∀ (π : Rep.{uV} ℂ (GeneralLinear n F.Carrier)), IsAdmissible π.ρ →
          Representation.Equiv
            (T.normalizedJacquet B (smoothContragredient π.ρ))
            (smoothContragredient (CuspidalJacquetMultiplicity.oppositeJacquet T B π).ρ),
        ∀ (π τ : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
          (hπ : IsAdmissible π.ρ) (hτ : IsAdmissible τ.ρ)
          (a : π.ρ.IntertwiningMap τ.ρ)
          (x : B.JacquetModule (smoothContragredient τ.ρ))
          (y : Jacquet.Coinvariants π.ρ (B.oppositeUnipotentSubgroup F.Carrier)),
          (E π hπ (T.normalizedJacquetMap B (contragredientMap a) x)).1 y =
            (E τ hτ x).1
              (Jacquet.map (B.oppositeUnipotentSubgroup F.Carrier)
                (B.leviSubgroup F.Carrier)
                (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier) a y)

end Langlands.AllFieldBZ.Parabolic
