import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Natural upper/opposite normalized Jacquet duality

Coherent families from upper Jacquet of the smooth dual to the smooth dual
of opposite Jacquet, natural on actual intertwiners.
-/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- Natural upper/opposite Jacquet duality for actual standard GL parabolics. -/
def StandardNaturalJacquetDualityClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
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

/-- Natural upper/opposite Jacquet duality for arbitrary product-Levi inputs. -/
def RefinedNaturalJacquetDualityClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
      letI := T.leviTopologicalGroup B
      ∃ E : ∀ (π : Rep.{uV} ℂ (B.Levi F.Carrier)), IsAdmissible π.ρ →
          Representation.Equiv
            (T.normalizedRefinedJacquet B S (smoothContragredient π.ρ))
            (smoothContragredient (T.normalizedRefinedOppositeJacquet B S π.ρ)),
        ∀ (π τ : Rep.{uV} ℂ (B.Levi F.Carrier))
          (hπ : IsAdmissible π.ρ) (hτ : IsAdmissible τ.ρ)
          (a : π.ρ.IntertwiningMap τ.ρ)
          (x : RefinedJacquetModule B S (smoothContragredient τ.ρ))
          (y : RefinedOppositeJacquetModule B S π.ρ),
          (E π hπ (T.normalizedRefinedJacquetMap B S (contragredientMap a) x)).1 y =
            (E τ hτ x).1 (T.normalizedRefinedOppositeJacquetMap B S a y)

/-- The standard and refined natural upper/opposite normalized Jacquet families. -/
def NaturalNormalizedJacquetDualityStatement : Prop :=
  StandardNaturalJacquetDualityClause.{uF, uV} ∧
    RefinedNaturalJacquetDualityClause.{uF, uV}

end Langlands.Parabolic
