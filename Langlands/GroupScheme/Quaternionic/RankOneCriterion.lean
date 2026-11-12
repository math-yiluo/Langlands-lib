import Langlands.GroupScheme.Quaternionic.TorusWittBound
import Langlands.GroupScheme.Rational.NontrivialCocharacterRank

/-! # Rank one from a Witt upper bound and a nontrivial cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {n : Type} [Fintype n] [DecidableEq n]
  (σ : FirstKindInvolution K D) (H : Matrix n n D)

/-- A nontrivial base-field cocharacter closes the lower bound for any
affine group embedded in an isometry group of Witt index at most one. -/
theorem splitRank_eq_one_of_mono_unitary (hH : σ.wittIndex H ≤ 1)
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (q : G ⟶ σ.unitaryGroup H) [Mono q.hom.hom.left]
    (hG : HasNontrivialCocharacter G) : splitRank G = 1 :=
  le_antisymm (σ.splitRank_le_one_of_mono_unitary H hH q) hG.one_le_splitRank

/-- In the reduced-norm-one symplectic case, the upper bound is already
proved, so only existence of a nontrivial cocharacter is supplied here. -/
theorem splitRank_symplecticGroup_eq_one_of_nontrivialCocharacter
    [Algebra.IsCentral K D] [Nonempty n]
    (hH : σ.wittIndex H ≤ 1)
    (hG : HasNontrivialCocharacter (σ.symplecticGroup H)) :
    splitRank (σ.symplecticGroup H) = 1 := by
  have : IsAffineHom (σ.unitaryGroup H).X.hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  have : IsAffineHom (σ.symplecticGroup H).X.hom := by
    have : IsClosedImmersion (σ.symplecticGroupι H).hom.hom.left := by
      change IsClosedImmersion (kernelι _).hom.hom.left
      infer_instance
    rw [← Over.w (σ.symplecticGroupι H).hom.hom]
    infer_instance
  exact le_antisymm (σ.splitRank_symplecticGroup_le_one H hH) hG.one_le_splitRank

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
