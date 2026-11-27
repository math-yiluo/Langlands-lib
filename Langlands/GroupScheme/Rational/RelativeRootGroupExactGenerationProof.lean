import Langlands.GroupScheme.Rational.RelativeRootGroupExactGenerationStatement
import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationProof
import Langlands.GroupScheme.Rational.RelativeRootAbsoluteRestrictionProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootMultiples

/-! # Exact absolute generation for a nonmultipliable relative root -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- When `2 • a` is absent, generation by positive multiples of `a`
is generation by the roots that restrict to `a` itself. -/
theorem relativeRootGroupExactGeneration : RelativeRootGroupExactGenerationStatement.{u} := by
  intro k K _ _ _ G hG S i hi T j f hj hf hTK
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom _)
    infer_instance
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  dsimp only
  intro a ha h2a
  obtain ⟨hc, hm⟩ := relativeRootGroupAbsoluteGeneration k K G hG S i hi T j f hj hf hTK a ha
  refine ⟨fun β hβ h => hc β hβ ⟨1, Nat.one_pos, by simpa only [one_nsmul] using h⟩, ?_⟩
  intro H h hh hroots
  apply hm H h hh
  intro β hβ hmult
  obtain ⟨n, hn, hEq⟩ := hmult
  have hna : n • a ≠ 0 := hi.1.1.nsmul_ne_zero ha.1 hn.ne'
  have hroot : n • a ∈ relativeRoots i :=
    (relativeRootAbsoluteRestriction k K G hG S i hi T j f hj hf hTK (n • a)).mpr
      ⟨hna, β, hβ, by simpa only [map_nsmul] using hEq⟩
  have hR := relativeRootSystem k G hG S i hi
  have hone : n = 1 := hR.eq_one_of_nsmul_mem_of_two_not_mem ha h2a hroot
  exact hroots β hβ (by simpa only [hone, one_nsmul] using hEq)

end Langlands.GroupScheme
