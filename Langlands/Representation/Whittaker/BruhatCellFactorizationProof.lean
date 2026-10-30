import Langlands.Representation.Whittaker.BruhatCellFactorizationStatement
import Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof
import Langlands.Representation.Whittaker.BruhatCompatibleSupportProof
import Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Proof of the factorization of a bi-equivariant cell distribution

Proves `Langlands.Whittaker.BruhatCellFactorizationStatement`. Product translation on
`M = U × (H × U)` commutes with the fiber action, so the raw fiber average intertwines it
with translation on the cell; pullback by a fiber action leaves the raw average unchanged
for a left-invariant measure. Surjectivity of the torus multiplication map, from the
published coordinate section, turns both pointwise identities into identities for every
linear map `I` with the evaluation formula. The published generic character-average
factorization then gives the unique torus distribution, and the published compatible
support theorem places it on the compatible torus. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis MeasureTheory

universe uK uF

namespace BruhatCellFactorization

section Generic

variable {n : ℕ} {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalRing K] {w : Equiv.Perm (Fin (n + 1))}

/-- The fiber action commutes with left translation of the first coordinate and
right translation of the last coordinate. -/
theorem fiberAct_productTranslate
    (a b : upperUnipotent (n + 1) K)
    (u : permutationUnipotentPlus (n + 1) K w)
    (m : upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K) :
    bruhatFiberAct (n + 1) K w u
        (((Homeomorph.mulLeft a).prodCongr
          ((Homeomorph.refl (Fin (n + 1) → Kˣ)).prodCongr (Homeomorph.mulRight b))) m) =
      ((Homeomorph.mulLeft a).prodCongr
        ((Homeomorph.refl (Fin (n + 1) → Kˣ)).prodCongr (Homeomorph.mulRight b)))
          (bruhatFiberAct (n + 1) K w u m) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext rfl (Subtype.ext ?_))
  · change (a.val * m.1.val) * permutation (n + 1) K w *
        Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ * (Iwasawa.diagonalUnits m.2.1)⁻¹ *
          (permutation (n + 1) K w)⁻¹ =
      a.val * (m.1.val * permutation (n + 1) K w * Iwasawa.diagonalUnits m.2.1 *
        u.val⁻¹ * (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation (n + 1) K w)⁻¹)
    simp only [mul_assoc]
  · change u.val * (m.2.2.val * b.val) = (u.val * m.2.2.val) * b.val
    exact (mul_assoc _ _ _).symm

/-- The actual multiplication map intertwines product translation and cell
translation. -/
theorem torusMap_productTranslate
    (a b : upperUnipotent (n + 1) K)
    (m : upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K) :
    upperBruhatTorusMap (n + 1) w
        (((Homeomorph.mulLeft a).prodCongr
          ((Homeomorph.refl (Fin (n + 1) → Kˣ)).prodCongr (Homeomorph.mulRight b))) m) =
      bruhatCellBiTranslate n K w a b (upperBruhatTorusMap (n + 1) w m) := by
  apply Subtype.ext
  change (a.val * m.1.val) * permutation (n + 1) K w *
        Iwasawa.diagonalUnits m.2.1 * (m.2.2.val * b.val) =
      a.val * (m.1.val * permutation (n + 1) K w *
        Iwasawa.diagonalUnits m.2.1 * m.2.2.val) * b.val
  simp only [mul_assoc]

variable [T2Space K]
  (ν : letI := borel (permutationUnipotentPlus (n + 1) K w)
  Measure (permutationUnipotentPlus (n + 1) K w)) [IsFiniteMeasureOnCompacts ν]

/-- Translating the test function translates the raw fiber average at its
argument; this identity requires no change of variables in the measure. -/
theorem fiberAverage_pullback_productTranslate
    (a b : upperUnipotent (n + 1) K)
    (α : SchwartzBruhat
      (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K))
    (m : upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K) :
    bruhatFiberAverage (n + 1) K w ν
        (Hecke.TestFunction.pullback ((Homeomorph.mulLeft a).prodCongr
          ((Homeomorph.refl (Fin (n + 1) → Kˣ)).prodCongr (Homeomorph.mulRight b))) α) m =
      bruhatFiberAverage (n + 1) K w ν α
        (((Homeomorph.mulLeft a).prodCongr
          ((Homeomorph.refl (Fin (n + 1) → Kˣ)).prodCongr (Homeomorph.mulRight b))) m) := by
  rw [bruhatFiberAverage_apply, bruhatFiberAverage_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u =>
    congrArg α (fiberAct_productTranslate a b u m).symm

/-- Pullback by a fiber action leaves the raw average unchanged for a left
invariant measure. This uses left multiplication on the integration variable. -/
theorem fiberAverage_pullback_fiberAct
    (hν : letI := borel (permutationUnipotentPlus (n + 1) K w); ν.IsMulLeftInvariant)
    (u : permutationUnipotentPlus (n + 1) K w)
    (α : SchwartzBruhat
      (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K))
    (m : upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K) :
    bruhatFiberAverage (n + 1) K w ν
        (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) K w u) α) m =
      bruhatFiberAverage (n + 1) K w ν α m := by
  let := borel (permutationUnipotentPlus (n + 1) K w)
  have : BorelSpace (permutationUnipotentPlus (n + 1) K w) := ⟨rfl⟩
  have := hν
  rw [bruhatFiberAverage_apply, bruhatFiberAverage_apply]
  change (∫ v, α (bruhatFiberAct (n + 1) K w u
    (bruhatFiberAct (n + 1) K w v m)) ∂ν) = _
  simp only [bruhatFiberAct_bruhatFiberAct]
  exact integral_mul_left_eq_self (fun v => α (bruhatFiberAct (n + 1) K w v m)) u

variable
  (I : SchwartzBruhat
      (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K) →ₗ[ℂ]
    SchwartzBruhat (UpperBruhatCell (n + 1) K w))
  (hI : ∀ α m, I α (upperBruhatTorusMap (n + 1) w m) =
    bruhatFiberAverage (n + 1) K w ν α m)
  (hπ : Function.Surjective (upperBruhatTorusMap (n + 1) (K := K) w))

include hI hπ

/-- A linear map with the evaluation formula intertwines product translation and cell
translation. -/
theorem orbitalIntegral_pullback_productTranslate
    (a b : upperUnipotent (n + 1) K)
    (α : SchwartzBruhat
      (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K)) :
    I (Hecke.TestFunction.pullback ((Homeomorph.mulLeft a).prodCongr
        ((Homeomorph.refl (Fin (n + 1) → Kˣ)).prodCongr (Homeomorph.mulRight b))) α) =
      Hecke.TestFunction.pullback (bruhatCellBiTranslate n K w a b) (I α) := by
  ext c
  obtain ⟨m, rfl⟩ := hπ c
  rw [hI, fiberAverage_pullback_productTranslate, ← hI, torusMap_productTranslate]
  rfl

/-- A linear map with the evaluation formula is invariant under pullback by the actual
fiber action. -/
theorem orbitalIntegral_pullback_fiberAct
    (hν : letI := borel (permutationUnipotentPlus (n + 1) K w); ν.IsMulLeftInvariant)
    (u : permutationUnipotentPlus (n + 1) K w)
    (α : SchwartzBruhat
      (upperUnipotent (n + 1) K × (Fin (n + 1) → Kˣ) × upperUnipotent (n + 1) K)) :
    I (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) K w u) α) =
      I α := by
  ext c
  obtain ⟨m, rfl⟩ := hπ c
  rw [hI, hI, fiberAverage_pullback_fiberAct ν hν]

end Generic

section Coordinates

variable {r : ℕ} {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] (w : Equiv.Perm (Fin r))

/-- Surjectivity of the actual torus multiplication map follows from the
published coordinate homeomorphism and its continuous section. -/
theorem torusMap_surjective :
    Function.Surjective (upperBruhatTorusMap r (K := K) w) := by
  obtain ⟨eT, heT⟩ := (upperBruhatCoordinates K r w).2
  exact fun c => ⟨cellSection eT c, upperBruhatTorusMap_cellSection heT c⟩

end Coordinates

end BruhatCellFactorization

open BruhatCellFactorization in
/-- A bi-equivariant cell distribution, pulled back through any linear map with the
orbital evaluation formula, factors uniquely through the weighted character average by a
torus distribution supported on the compatible torus. -/
theorem bruhatCellFactorization : BruhatCellFactorizationStatement.{uF} := by
  intro p hp F
  let := F.canonicalNormedField
  intro n ψ w U P H M C
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  let := borel P
  intro μ _ _ _ ν _ _ I hI D hD
  have : IsTopologicalGroup U := F.canonicalUpperUnipotentTopologicalGroup (n + 1)
  have : T2Space U := F.canonicalUpperUnipotentT2Space (n + 1)
  have : LocallyCompactSpace U := F.canonicalUpperUnipotentLocallyCompactSpace (n + 1)
  have : NonarchimedeanGroup U := F.canonicalUpperUnipotentNonarchimedean (n + 1)
  let := F.canonicalNormedAlgebra
  have : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier
  have : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  have : TotallyDisconnectedSpace F.Carrierˣ :=
    Units.isEmbedding_val₀.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  have : LocallyCompactSpace H := inferInstance
  have : T2Space H := inferInstance
  have : TotallyDisconnectedSpace H := inferInstance
  have hπ := torusMap_surjective (K := F.Carrier) w
  obtain ⟨τ, hτ, hunique⟩ :=
    Distribution.characterAverageFactorization U H (standardCharacterContinuous ψ n) μ
      (D.comp I) (by
        intro a b α
        change D (I (Hecke.TestFunction.pullback _ α)) = _
        rw [orbitalIntegral_pullback_productTranslate ν I hI hπ]
        exact hD a b (I α))
  refine ⟨τ, ⟨?_, hτ⟩, ?_⟩
  · apply bruhatCompatibleSupport p hp F n ψ w μ τ
    intro u α
    rw [hτ]
    change D (I (Hecke.TestFunction.pullback _ α)) = D (I α)
    rw [orbitalIntegral_pullback_fiberAct ν I hI hπ
      (inferInstance : ν.IsMulLeftInvariant)]
  · intro τ' hτ'
    exact hunique τ' hτ'.2

end Langlands.Whittaker
