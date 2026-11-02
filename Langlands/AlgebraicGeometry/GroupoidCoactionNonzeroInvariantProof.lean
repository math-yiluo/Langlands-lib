import Langlands.AlgebraicGeometry.GroupoidCoactionCore
import Langlands.AlgebraicGeometry.GroupoidCoactionFinitePresentation
import Langlands.AlgebraicGeometry.GroupoidCoactionFiniteAlgebra
import Langlands.AlgebraicGeometry.GroupoidCoactionTensorDescent
import Langlands.AlgebraicGeometry.GroupoidCoactionSupport
import Langlands.AlgebraicGeometry.GroupoidCoactionIdealQuotient
import Langlands.AlgebraicGeometry.GroupoidCoactionIdealRestriction
import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationFiniteOrbit
import Langlands.AlgebraicGeometry.GroupoidCoactionNonzeroInvariantStatement

/-! # Nonzero invariants for Noetherian affine étale equivalence relations -/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry

namespace GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type u} [AddCommGroup M] [Module B M]

lemma exists_nonzero_invariant_of_finite_subcoactions [IsNoetherianRing B]
    [Nontrivial M] (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M)
    (hfinite : ∀ (N : Type u) [AddCommGroup N] [Module B N]
      [Module.Finite B N] [Nontrivial N] (θN : GroupoidCoaction t N),
      ∃ n ∈ θN.invariants, n ≠ 0) :
    ∃ m ∈ θ.invariants, m ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨H, θH, hH, hmH, hhom⟩ := exists_finite_subcoaction hE θ m
  let : Module.Finite B H := hH
  let : Nontrivial H := ⟨⟨⟨m, hmH⟩, 0, fun h => hm (congrArg Subtype.val h)⟩⟩
  obtain ⟨n, hn, hn0⟩ := hfinite H θH
  exact ⟨n, hhom.mapsTo_invariants hn, fun h => hn0 (Subtype.ext h)⟩

lemma exists_nonzero_invariant_of_finite_projective [Module.Finite B C]
    [Module.Projective B C] [Nontrivial M]
    (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M)
    (ht : letI := t.toAlgebra; Module.Finite B C)
    (ht' : letI := t.toAlgebra; Module.Projective B C) :
    ∃ m ∈ θ.invariants, m ≠ 0 := by
  let : Module.FaithfullyFlat (invariantRing t) B :=
    (hE.finiteProjective_invariantRing_quotient ht ht').2.2.1
  let : Algebra (invariantRing t) C :=
    ((algebraMap B C).comp (algebraMap (invariantRing t) B)).toAlgebra
  let : IsScalarTower (invariantRing t) B C :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact exists_nonzero_invariant_of_flat_presentation (A := invariantRing t) hE θ
    (hE.finiteProjectiveTensorEquiv ht ht')
    (hE.finiteProjectiveTensorEquiv_target ht ht')

lemma exists_nonzero_invariant_of_artinian [IsArtinianRing B] [Nontrivial M]
    (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M) :
    ∃ m ∈ θ.invariants, m ≠ 0 := by
  let : Algebra.Etale B C := RingHom.etale_algebraMap.mp hE.etale_algebraMap
  obtain ⟨hfin, hproj⟩ := GroupoidCoactionFiniteAlgebra.finite_projective_of_artinian B C
  let : Module.Finite B C := hfin
  let : Module.Projective B C := hproj
  have ht_etale := hE.etale_t
  have ht : letI := t.toAlgebra; Module.Finite B C ∧ Module.Projective B C := by
    let := t.toAlgebra
    let : @Algebra.Etale B C _ _ t.toAlgebra := ht_etale
    exact GroupoidCoactionFiniteAlgebra.finite_projective_of_artinian B C
  exact exists_nonzero_invariant_of_finite_projective hE θ ht.1 ht.2

lemma exists_artinian_ideal_nontrivial_quotient [IsNoetherianRing B]
    [Module.Finite B M] [Nontrivial M]
    (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M) :
    ∃ I : Ideal B, I.map (algebraMap B C) = I.map t ∧
      IsArtinianRing (B ⧸ I) ∧ Nontrivial (M ⧸ (I • ⊤ : Submodule B M)) := by
  let S : TopologicalSpace.Closeds (PrimeSpectrum B) :=
    ⟨Module.support B M, by
      rw [Module.support_eq_zeroLocus]
      exact PrimeSpectrum.isClosed_zeroLocus _⟩
  have hne : (S : Set (PrimeSpectrum B)).Nonempty :=
    Module.nonempty_support_of_nontrivial
  have hinv : PrimeSpectrum.comap (algebraMap B C) ⁻¹' (S : Set (PrimeSpectrum B)) =
      PrimeSpectrum.comap t ⁻¹' (S : Set (PrimeSpectrum B)) :=
    support_preimage_eq hE θ
  let I := hE.finiteOrbitIdeal S hne hinv
  obtain ⟨_, _, _, hI, _⟩ := hE.finiteOrbitIdeal_spec S hne hinv
  obtain ⟨hle, hpne, _⟩ := hE.finiteClosedOrbit_spec S hne hinv
  obtain ⟨p, hp⟩ := hpne
  have hIp : I ≤ p.asIdeal := by
    intro b hb
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hb p hp
  exact ⟨I, hI, (hE.finiteOrbitIdeal_quotient S hne hinv).2.2,
    idealQuotient_nontrivial_of_mem_support I p (hle hp) hIp⟩

lemma exists_nonzero_invariant_of_finite [IsNoetherianRing B]
    [Module.Finite B M] [Nontrivial M]
    (hE : RingEtaleEquivalenceRelation t)
    (hacyclic : ∀ (K : Type u) [AddCommGroup K] [Module B K]
      (θK : GroupoidCoaction t K), θK.IsAcyclic)
    (θ : GroupoidCoaction t M) :
    ∃ m ∈ θ.invariants, m ≠ 0 := by
  obtain ⟨I, hI, hArt, hN⟩ := exists_artinian_ideal_nontrivial_quotient hE θ
  let : IsArtinianRing (B ⧸ I) := hArt
  let : Nontrivial (M ⧸ (I • ⊤ : Submodule B M)) := hN
  obtain ⟨q, hq, hq0⟩ := exists_nonzero_invariant_of_artinian
    (hE.quotient I hI) (θ.idealRestriction I hI)
  exact exists_nonzero_invariant_of_idealQuotient hE hacyclic θ I hI.ge
    ⟨q, (idealRestriction_mem_invariants_iff θ I hI q).mp hq, hq0⟩

end GroupoidCoaction

/-- Every nontrivial coaction for a Noetherian affine étale equivalence relation
with all coactions acyclic has a nonzero invariant. -/
theorem groupoidCoactionNonzeroInvariant : GroupoidCoactionNonzeroInvariantStatement.{u} := by
  intro B C _ _ _ t hE hnoeth hacyclic M _ _ _ θ
  let : IsNoetherianRing B := hnoeth
  apply GroupoidCoaction.exists_nonzero_invariant_of_finite_subcoactions hE θ
  intro N _ _ _ _ θN
  exact GroupoidCoaction.exists_nonzero_invariant_of_finite hE hacyclic θN

end Langlands.AlgebraicGeometry
