import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationQuotient
import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationFiniteOrbit

/-! # Finite projective ring relations on finite closed orbit quotients -/

universe u

open TopologicalSpace

namespace Langlands.AlgebraicGeometry

namespace RingEtaleEquivalenceRelation

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
  {t : B →+* C}

/-- The source of an Artinian quotient relation is finite and projective for
the canonical quotient algebra structure. -/
lemma quotientSource_finite_projective (hE : RingEtaleEquivalenceRelation t)
    (I : Ideal B) [IsArtinianRing (B ⧸ I)] :
    Module.Finite (B ⧸ I) (C ⧸ I.map (algebraMap B C)) ∧
      Module.Projective (B ⧸ I) (C ⧸ I.map (algebraMap B C)) := by
  let : Algebra.Etale (B ⧸ I) (C ⧸ I.map (algebraMap B C)) :=
    RingHom.etale_algebraMap.mp (hE.etale_quotientSource I)
  exact GroupoidCoactionFiniteAlgebra.finite_projective_of_artinian _ _

/-- The target of an Artinian quotient relation is finite and projective for
the scalar structure induced by the actual target quotient map. -/
lemma quotientTarget_finite_projective (hE : RingEtaleEquivalenceRelation t)
    (I : Ideal B) (hI : I.map (algebraMap B C) = I.map t)
    [IsArtinianRing (B ⧸ I)] :
    let := (quotientTarget I hI).toAlgebra
    Module.Finite (B ⧸ I) (C ⧸ I.map (algebraMap B C)) ∧
      Module.Projective (B ⧸ I) (C ⧸ I.map (algebraMap B C)) := by
  let := (quotientTarget I hI).toAlgebra
  let := (hE.etale_quotientTarget I hI).toAlgebra
  exact GroupoidCoactionFiniteAlgebra.finite_projective_of_artinian _ _

variable [IsNoetherianRing B]

/-- The target map of the relation on the chosen finite closed orbit. -/
noncomputable def finiteOrbitQuotientTarget (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    B ⧸ hE.finiteOrbitIdeal S hne hS →+*
      C ⧸ (hE.finiteOrbitIdeal S hne hS).map (algebraMap B C) :=
  quotientTarget _ (hE.finiteOrbitIdeal_spec S hne hS).2.2.2.1

lemma finiteOrbitQuotient_relation (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    RingEtaleEquivalenceRelation (hE.finiteOrbitQuotientTarget S hne hS) :=
  hE.quotient _ _

/-- On the finite orbit quotient, the actual source map is finite projective. -/
lemma finiteOrbitQuotient_source_finite_projective (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    let I := hE.finiteOrbitIdeal S hne hS
    Module.Finite (B ⧸ I) (C ⧸ I.map (algebraMap B C)) ∧
      Module.Projective (B ⧸ I) (C ⧸ I.map (algebraMap B C)) := by
  let := (hE.finiteOrbitIdeal_quotient S hne hS).2.2
  exact hE.quotientSource_finite_projective _

/-- On the finite orbit quotient, the actual target map is finite projective. -/
lemma finiteOrbitQuotient_target_finite_projective (hE : RingEtaleEquivalenceRelation t)
    (S : Closeds (PrimeSpectrum B)) (hne : (S : Set (PrimeSpectrum B)).Nonempty)
    (hS : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B))) :
    let I := hE.finiteOrbitIdeal S hne hS
    let := (hE.finiteOrbitQuotientTarget S hne hS).toAlgebra
    Module.Finite (B ⧸ I) (C ⧸ I.map (algebraMap B C)) ∧
      Module.Projective (B ⧸ I) (C ⧸ I.map (algebraMap B C)) := by
  let := (hE.finiteOrbitIdeal_quotient S hne hS).2.2
  exact hE.quotientTarget_finite_projective _ _

end RingEtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
