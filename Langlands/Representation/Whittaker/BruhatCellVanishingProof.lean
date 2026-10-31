import Langlands.Representation.Whittaker.BruhatCellVanishingStatement
import Langlands.Representation.Whittaker.BruhatCellFactorizationProof
import Langlands.Representation.Whittaker.BruhatHaarMeasureProof
import Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof

/-!
# Proof of vanishing on character-incompatible Bruhat cells

Proves `Langlands.Whittaker.BruhatCellVanishingStatement`. The published Haar theorem
supplies Haar measures on the upper unipotent group and on the Bruhat fiber subgroup, and
the published orbital-integration theorem a surjective orbital integral `I`. The published
factorization theorem gives a torus distribution supported on the compatible torus whose
character-average dual is `D ∘ I`. When the compatible torus is empty, that torus
distribution is zero by the definition of support, so `D ∘ I = 0`, and surjectivity of `I`
gives `D = 0`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis MeasureTheory

universe uF

/-- A bi-equivariant algebraic distribution on an upper Bruhat cell whose compatible
torus is empty is zero. -/
theorem bruhatCellVanishing : BruhatCellVanishingStatement.{uF} := by
  intro p hp F
  let := F.canonicalNormedField
  intro n ψ w hempty D hD
  let U := upperUnipotent (n + 1) F.Carrier
  let P := permutationUnipotentPlus (n + 1) F.Carrier w
  let H := Fin (n + 1) → F.Carrierˣ
  let M := U × (H × U)
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  let := borel P
  obtain ⟨μ, hμ⟩ := (bruhatHaarMeasure p hp F n).1
  have := hμ
  obtain ⟨hσ, hr, -⟩ := (bruhatHaarMeasure p hp F n).2.1 μ
  have := hσ
  have := hr
  obtain ⟨ν, hν⟩ := ((bruhatHaarMeasure p hp F n).2.2 w).1
  have := hν
  have := (((bruhatHaarMeasure p hp F n).2.2 w).2 ν).2
  obtain ⟨I, ⟨hI, hsurj, -⟩, -⟩ := bruhatOrbitalIntegration p hp F n w ν
  obtain ⟨τ, ⟨hsupp, hτ⟩, -⟩ := bruhatCellFactorization p hp F n ψ w μ ν I hI D hD
  have hzero : τ = 0 := by
    ext f
    apply (Distribution.mem_supportedOn_iff _ _).mp hsupp f
    intro d hd
    exact (hempty ⟨d, hd⟩).elim
  have hcomp : D.comp I = 0 := by
    rw [← hτ, hzero, map_zero]
  ext f
  obtain ⟨α, rfl⟩ := hsurj f
  exact congrArg (fun E : Distribution M => E α) hcomp

end Langlands.Whittaker
