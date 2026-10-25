import Langlands.Representation.CyclicSpan
import Langlands.Representation.Smooth.Factorization.RestrictedProductExistenceStatement
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Cyclic local factors inside a two-factor representation -/

namespace Langlands

universe uG₁ uG₂ uV

/-- A prescribed nonzero vector can be refined inside its first-factor orbit span
so that its new first-factor cyclic subrepresentation is admissible irreducible. -/
def FirstFactorCyclicRefinementStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (G₁ × G₂) V),
    IsAdmissible π → π.IsIrreducible →
    ∀ x : V, x ≠ 0 →
    ∃ y : V, y ∈ Cyclic.orbitSpan (π.comp (MonoidHom.inl G₁ G₂)) x ∧ y ≠ 0 ∧
      IsAdmissible (Cyclic.orbitSpan (π.comp (MonoidHom.inl G₁ G₂)) y).toRepresentation ∧
      (Cyclic.orbitSpan (π.comp (MonoidHom.inl G₁ G₂)) y).toRepresentation.IsIrreducible

/-- A nonzero vector fixed by a compact open subgroup with commutative spherical
Hecke algebra already generates an admissible irreducible first-factor
subrepresentation, and its subgroup-fixed space is a line. -/
def SphericalFirstFactorCyclicStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
    [MeasurableSpace G₁] [BorelSpace G₁]
    (μ : MeasureTheory.Measure G₁) [MeasureTheory.Measure.IsHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ]
    (H : OpenSubgroup G₁) (_hH : IsCompact (H : Set G₁))
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (G₁ × G₂) V),
    SphericalHeckeCommutative μ H.toSubgroup → IsAdmissible π → π.IsIrreducible →
    ∀ x : V, x ≠ 0 → x ∈ fixedVectors (π.comp (MonoidHom.inl G₁ G₂)) H.toSubgroup →
      IsAdmissible (Cyclic.orbitSpan (π.comp (MonoidHom.inl G₁ G₂)) x).toRepresentation ∧
      (Cyclic.orbitSpan (π.comp (MonoidHom.inl G₁ G₂)) x).toRepresentation.IsIrreducible ∧
      Module.finrank ℂ
        (fixedVectors (Cyclic.orbitSpan (π.comp (MonoidHom.inl G₁ G₂)) x).toRepresentation
          H.toSubgroup) = 1

/-- The two local cyclic extraction inputs for constructing restricted-product factors. -/
def TwoFactorCyclicExtractionStatement : Prop :=
  FirstFactorCyclicRefinementStatement.{uG₁, uG₂, uV} ∧
    SphericalFirstFactorCyclicStatement.{uG₁, uG₂, uV}

end Langlands
