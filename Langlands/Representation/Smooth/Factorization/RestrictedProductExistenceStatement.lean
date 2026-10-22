import Langlands.Representation.RestrictedTensor.Smooth
import Langlands.Representation.Hecke.Convolution
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Existence of restricted tensor factorizations

Flath's Theorem 2 with its almost-everywhere spherical Hecke commutativity
hypothesis expressed through the actual published convolution multiplication.
-/

namespace Langlands

open RestrictedTensor MeasureTheory

universe uI uG uV

/-- Actual convolution commutes on the functions invariant on both sides by
the indicated subgroup. The factorization statement applies this predicate
only to compact open subgroups and genuine regular left Haar measures. -/
def SphericalHeckeCommutative {G : Type uG} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (H : Subgroup G) : Prop :=
  ∀ f g : Hecke.HeckeAlgebra μ,
    Hecke.HeckeAlgebra.toTestFunction μ f ∈ Hecke.TestFunction.biInvariant H H →
    Hecke.HeckeAlgebra.toTestFunction μ g ∈ Hecke.TestFunction.biInvariant H H →
    f * g = g * f

/-- Every admissible irreducible representation of the actual restricted
product factors when the reference spherical Hecke algebras commute almost
everywhere. The local carriers can lie in the universe of the original carrier. -/
def FlathRestrictedProductExistenceStatement : Prop :=
  ∀ (ι : Type uI) (G : ι → Type uG) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, Measure.IsHaarMeasure (μ i)]
    [∀ i, Measure.Regular (μ i)]
    (H : ∀ i, Subgroup (G i))
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (RestrictedGroup G H) V),
    (∀ i, IsOpen (H i : Set (G i)) ∧ IsCompact (H i : Set (G i))) →
    (∀ᶠ i in Filter.cofinite, SphericalHeckeCommutative (μ i) (H i)) →
    IsAdmissible π → π.IsIrreducible →
    ∃ (W : ι → ModuleCat.{uV} ℂ) (ρ : ∀ i, Representation ℂ (G i) (W i)),
      (∀ i, IsAdmissible (ρ i) ∧ (ρ i).IsIrreducible) ∧
      ∃ (E : Finset ι) (r : ReferenceVectors (fun i => W i) E)
        (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i,
          ρ i g (r.vector i hi) = r.vector i hi),
        (∀ i ∉ E, Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1) ∧
        Nonempty (π.Equiv (productRepresentation H ρ E r hr))

end Langlands
