import Langlands.Geometry.Analytic.GeneralizedAffinoid.PureLaurentRadiusExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentFieldCoverDescent

/-! # Finite pure Laurent reduction of a full affinoid domain -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) (U : Domain K A)

/-- Actual domain data after finitely many independent Laurent field extensions,
with original presentation radii and descent along the composed Gauss section. -/
structure LaurentReduction where
  extension : PureLaurentExtension K
  ambient : PresentedAffinoidAlgebra extension.L
  domain : Domain extension.L ambient
  ambient_arity : ambient.arity = A.arity
  ambient_radius : ∀ i, ambient.polyradius i =
    A.polyradius (Fin.cast ambient_arity i)
  domain_arity : domain.algebra.arity = U.algebra.arity
  domain_radius : ∀ i, domain.algebra.polyradius i =
    U.algebra.polyradius (Fin.cast domain_arity i)
  sectionMap : C(U.locus, domain.locus)
  descendNeighborhood : ∀ x : U.locus,
    FiniteRationalNeighborhood domain (sectionMap x) → FiniteRationalNeighborhood U x
  descendCover : FiniteRationalCover domain → FiniteRationalCover U

namespace LaurentReduction

variable {K A U}

/-- No extension changes any algebra, locus or neighborhood. -/
def self : LaurentReduction K A U where
  extension := PureLaurentExtension.self
  ambient := A
  domain := U
  ambient_arity := rfl
  ambient_radius _ := rfl
  domain_arity := rfl
  domain_radius _ := rfl
  sectionMap := ContinuousMap.id _
  descendNeighborhood _ N := N
  descendCover c := c

/-- Append an actual independent Laurent step to both algebras, composing the
continuous domain section and the finite-neighborhood and cover descents. -/
def adjoin (D : LaurentReduction K A U) (t : ℝ) [Fact (0 < t)]
    (H : ∀ (a : D.extension.L) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n) :
    LaurentReduction K A U := by
  letI : Fact (∀ (a : D.extension.L) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n) := ⟨H⟩
  exact
    { extension := D.extension.adjoin t H
      ambient := RelativeLaurentAnnulus.ScalarExtension.presentation D.extension.L D.ambient t
      domain := RelativeLaurentAnnulus.ScalarExtension.fieldDomain D.extension.L t D.domain
      ambient_arity := D.ambient_arity
      ambient_radius := D.ambient_radius
      domain_arity := D.domain_arity
      domain_radius := D.domain_radius
      sectionMap := (RelativeLaurentAnnulus.ScalarExtension.fieldDomainGaussSection
        D.extension.L t D.domain).comp D.sectionMap
      descendNeighborhood x N := D.descendNeighborhood x
        (RelativeLaurentAnnulus.ScalarExtension.fieldFiniteRationalNeighborhoodDescent
          D.extension.L t D.domain (D.sectionMap x) N)
      descendCover c := D.descendCover
        (RelativeLaurentAnnulus.ScalarExtension.fieldFiniteRationalCoverDescent
          D.extension.L t D.domain c) }

/-- Adjoin only radii still outside the radical value group. Every step carries
the actual full domain, its Gauss section and rational-neighborhood descent. -/
theorem exists_for_radii :
    ∀ (N : ℕ) (t : Fin N → ℝ), (∀ i, 0 < t i) →
      ∃ D : LaurentReduction K A U,
        ∀ i, RadiusInRadicalValueGroup D.extension.L (t i)
  | 0, _, _ => ⟨self, fun i => Fin.elim0 i⟩
  | N + 1, t, ht => by
    obtain ⟨D, hD⟩ := exists_for_radii N (Fin.tail t) (fun i => ht i.succ)
    by_cases h : RadiusInRadicalValueGroup D.extension.L (t 0)
    · exact ⟨D, fun i => Fin.cases h (fun j => hD j) i⟩
    · let : Fact (0 < t 0) := ⟨ht 0⟩
      let H := PureLaurentExtension.independent_of_not_radiusInRadicalValueGroup h
      let := CompletedGaussLaurent.normedField H
      let E := D.adjoin (t 0) H
      refine ⟨E, fun i => Fin.cases ?_ (fun j => ?_) i⟩
      · exact ⟨CompletedGaussLaurent.X, 1, by omega, by
          change ‖(CompletedGaussLaurent.X :
            CompletedGaussLaurent D.extension.L (t 0))‖ = t 0 ^ 1
          simpa only [pow_one] using
            (CompletedGaussLaurent.norm_X (K := D.extension.L) (t := t 0))⟩
      · exact PureLaurentExtension.radiusInRadicalValueGroup_map
          (CompletedGaussLaurent.ι (K := D.extension.L) (t := t 0))
          CompletedGaussLaurent.norm_ι (hD j)

/-- Including radius two makes the final field nontrivially valued. -/
theorem exists_nontrivial_for_radii (N : ℕ) (t : Fin N → ℝ)
    (ht : ∀ i, 0 < t i) :
    ∃ D : LaurentReduction K A U,
      (∃ a : D.extension.L, 1 < ‖a‖) ∧
        ∀ i, RadiusInRadicalValueGroup D.extension.L (t i) := by
  obtain ⟨D, hD⟩ := exists_for_radii (K := K) (A := A) (U := U)
    (N + 1) (Fin.cons 2 t) (fun i => Fin.cases (by norm_num) ht i)
  refine ⟨D, ?_, fun i => by simpa using hD i.succ⟩
  obtain ⟨a, n, hn, ha⟩ := hD 0
  refine ⟨a, ?_⟩
  rw [ha]
  change 1 < (2 : ℝ) ^ n
  exact one_lt_pow₀ (by norm_num) hn.ne'

/-- Simultaneously make the original ambient and domain-algebra radii radical,
over a nontrivially valued complete pure Laurent field in the original universe. -/
theorem exists_strictifiable :
    ∃ D : LaurentReduction K A U,
      (∃ a : D.extension.L, 1 < ‖a‖) ∧
      (∀ i, RadiusInRadicalValueGroup D.extension.L (D.ambient.polyradius i)) ∧
      (∀ i, RadiusInRadicalValueGroup D.extension.L (D.domain.algebra.polyradius i)) := by
  let t : Fin (A.arity + U.algebra.arity) → ℝ :=
    Fin.addCases A.polyradius U.algebra.polyradius
  have ht : ∀ i, 0 < t i := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [t, Fin.addCases_left] using A.polyradius.positive j
    · simpa only [t, Fin.addCases_right] using U.algebra.polyradius.positive j
  obtain ⟨D, hn, hD⟩ := exists_nontrivial_for_radii (K := K) (A := A) (U := U)
    _ t ht
  refine ⟨D, hn, fun i => ?_, fun i => ?_⟩
  · rw [D.ambient_radius]
    simpa only [t, Fin.addCases_left] using
      hD (Fin.castAdd U.algebra.arity (Fin.cast D.ambient_arity i))
  · rw [D.domain_radius]
    simpa only [t, Fin.addCases_right] using
      hD (Fin.natAdd A.arity (Fin.cast D.domain_arity i))

end LaurentReduction

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
