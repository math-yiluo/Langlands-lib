import Langlands.ClassField.Global.IdeleInvariantAssembly
import Langlands.ClassField.Global.IdeleCyclicCoverage
import Langlands.ClassField.Global.IdeleArchimedeanSum
import Langlands.ClassField.Global.GlobalReciprocityProof

/-! # The total local invariant as a family on actual idele cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local FundamentalClass

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)

/-- The actual finite local sum at the existing chosen upper places, plus the
canonical archimedean sum, for every Galois number-field extension. -/
def totalIdeleInvariantMaps : IdeleInvariantMaps.{u} :=
  fun _F _ _ E _ _ _ _ =>
    finiteIdeleInvariantSum I hI (placeAbove E) + canonicalArchimedeanIdeleInvariantSum

section Values

variable (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]

private def infinitePlacesForTotal :
    ∀ v : InfinitePlace F, InfinitePlacesAbove E v :=
  fun v => by
    haveI : v.LiesOver v := ⟨by ext x; rfl⟩
    exact ⟨(InfinitePlace.comap_surjective (k := F) (K := E) v).choose,
      Reciprocity.liesOver_of_comap_eq
        (InfinitePlace.comap_surjective (k := F) (K := E) v).choose_spec v⟩

/-- The family agrees with the published total invariant for every choice of
infinite places, using its fixed finite choices. -/
theorem totalIdeleInvariantMaps_eq
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    totalIdeleInvariantMaps I hI F E = totalIdeleInvariant I hI (placeAbove E) wi := by
  change finiteIdeleInvariantSum I hI (placeAbove E) + canonicalArchimedeanIdeleInvariantSum =
    finiteIdeleInvariantSum I hI (placeAbove E) + archimedeanIdeleInvariantSum wi
  rw [canonicalArchimedeanIdeleInvariantSum_eq wi]

/-- Every value is killed by the global extension degree. -/
theorem totalIdeleInvariantMaps_mem_denominator (a : relativeIdeleCohomology F E 2) :
    totalIdeleInvariantMaps I hI F E a ∈ denominatorSubgroup (Module.finrank F E) := by
  rw [totalIdeleInvariantMaps_eq I hI F E (infinitePlacesForTotal F E)]
  exact totalIdeleInvariant_mem_denominator I hI _ _ a

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

/-- A section at one of the chosen finite places has exactly its local invariant. -/
theorem totalIdeleInvariantMaps_ideleLocalSection
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (placeAbove E v).1).range)]
    (a : relativeCohomology (padicField v).Carrier ((placeAbove E v).1.adicCompletion E) 2) :
    totalIdeleInvariantMaps I hI F E (ideleLocalSection v (placeAbove E v).1 2 a) =
      (I (residuePrime v)).relative (padicField v) ((placeAbove E v).1.adicCompletion E) a := by
  rw [totalIdeleInvariantMaps_eq I hI F E (infinitePlacesForTotal F E)]
  exact totalIdeleInvariant_ideleLocalSection I hI _ _ v a

end Values

/-- Prime-power local-degree existence supplies the cyclic range required by
the regular-class assembly. -/
theorem totalIdeleInvariantMaps_cyclicRange
    (hlocal : Langlands.Global.CyclicPrimePowerLocalDegreeStatement.{u, u}) :
    (totalIdeleInvariantMaps I hI).CyclicRange := by
  intro F _ _ E _ _ _ _ _
  rw [totalIdeleInvariantMaps_eq I hI F E (infinitePlacesForTotal F E)]
  exact totalIdeleInvariant_range_of_primePowerLocalDegreeCoverage I hI _ _
    (primePowerLocalDegreeCoverage_of_cyclic hlocal _)

/-- The global reciprocity statement makes the family vanish on the actual
idele-to-idele-class quotient kernel. -/
theorem totalIdeleInvariantMaps_killsQuotientKernel
    (hrec : GlobalReciprocity.{u})
    (hCF : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) :
    (totalIdeleInvariantMaps I hI).KillsQuotientKernel := by
  intro F _ _ E _ _ _ _ a ha
  rw [totalIdeleInvariantMaps_eq I hI F E (infinitePlacesForTotal F E)]
  exact totalIdeleInvariant_eq_zero_of_ideleQuotient_eq_zero I hI _ _
    (hrec I hCF F E) a ha

/-- The published conditional reciprocity proof reduces kernel vanishing to
actual idele-class `H¹` vanishing and the supplied local hypotheses. -/
theorem totalIdeleInvariantMaps_killsQuotientKernel_of_h1
    (hH1 : IdeleClassH1Vanishing.{u})
    (hCF : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) :
    (totalIdeleInvariantMaps I hI).KillsQuotientKernel :=
  totalIdeleInvariantMaps_killsQuotientKernel I hI (globalReciprocity_of hH1) hCF

end Langlands.ClassField.Global
