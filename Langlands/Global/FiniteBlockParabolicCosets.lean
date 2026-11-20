import Langlands.Global.AdelicBlockParabolic
import Langlands.Global.AdelicGLIwasawa
import Langlands.Group.LeftQuotientInversion
import Langlands.Representation.Induction.CompactQuotientProof

/-! Standard compact representatives for the actual finite block parabolic. -/

noncomputable section
set_option autoImplicit false

universe u

namespace Langlands.Global

open GeneralLinear Induction

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

/-- Finite adelic Iwasawa gives a compact quotient by the standard block parabolic. -/
theorem compactSpace_finiteBlockParabolicQuotient :
    CompactSpace (LeftQuotient (B.parabolic (FiniteAdeles F))) :=
  compactSpace_leftQuotient_of_compact_representatives (B.parabolic (FiniteAdeles F))
    (FiniteAdelicGL.isCompact_standardIntegral F n) fun g => by
      obtain ⟨b, k, hg, hb, hk⟩ := PrimitiveAdelicHeight.exists_finite_iwasawa F n g
      exact ⟨b, B.mem_parabolic_of_isUpperTriangular b hb, k, hk, hg⟩

/-- Every open right stabilizer gives a finite double-coset cover. -/
theorem exists_finiteBlockParabolicDoubleCosetCover (L : OpenSubgroup (FiniteAdelicGL F n)) :
    ∃ s : Finset (FiniteAdelicGL F n), ∀ g : FiniteAdelicGL F n,
      ∃ a ∈ s, ∃ p : AdelicBlockParabolic.Finite F B, ∃ l : L, g = p.val * a * l.val := by
  let := compactSpace_finiteBlockParabolicQuotient F B
  obtain ⟨s, hs⟩ := exists_finset_doubleCoset_cover (B.parabolic (FiniteAdeles F)) L
  refine ⟨s, fun g => ?_⟩
  obtain ⟨a, ha, p, hp, l, hl, hg⟩ := hs g
  exact ⟨a, ha, ⟨p, hp⟩, ⟨l, hl⟩, hg⟩

/-- Representatives that cover the finite adelic group by parabolic double cosets. -/
def finiteBlockParabolicDoubleCosetReps (L : OpenSubgroup (FiniteAdelicGL F n)) :
    Finset (FiniteAdelicGL F n) :=
  (exists_finiteBlockParabolicDoubleCosetCover F B L).choose

theorem finiteBlockParabolicDoubleCosetReps_cover (L : OpenSubgroup (FiniteAdelicGL F n))
    (g : FiniteAdelicGL F n) :
    ∃ a ∈ finiteBlockParabolicDoubleCosetReps F B L,
      ∃ p : AdelicBlockParabolic.Finite F B, ∃ l : L, g = p.val * a * l.val :=
  (exists_finiteBlockParabolicDoubleCosetCover F B L).choose_spec g

end Langlands.Global
