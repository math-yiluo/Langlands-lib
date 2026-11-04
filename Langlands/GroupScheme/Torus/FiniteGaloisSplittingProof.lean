import Langlands.GroupScheme.Torus.FiniteGaloisSplittingStatement
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.FiniteSeparableSplitting
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Finite Galois splitting of every actual field torus -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.GroupScheme.SplittingAssembly

/-- Separably closed splitting and finite-stage descent suffice for the exact
published finite Galois splitting proposition. -/
theorem finiteGaloisSplitting_of_sepClosedSplitting_of_finiteStage
    (hSplit : ∀ (k : Type u) [Field k] [IsSepClosed k]
      (T : GroupScheme (Spec (CommRingCat.of k))), IsTorus T → IsSplitTorus T)
    (hFinite : ∀ (k : Type u) [Field k]
      (T : GroupScheme (Spec (CommRingCat.of k)))
      [QuasiCompact T.X.hom] [QuasiSeparated T.X.hom],
      IsSplitTorus ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))).obj T) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
        FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
        IsSplitTorus ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    TorusFiniteGaloisSplittingStatement.{u} := by
  intro k _ T hT
  have : QuasiCompact T.X.hom := hT.quasiCompact
  have : QuasiSeparated T.X.hom := hT.quasiSeparated
  have hS : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))).obj T) :=
    hSplit (SeparableClosure k) _
      (IsTorus.baseChange_of_isAlgebraic k (SeparableClosure k) T hT)
  obtain ⟨L, hL, hA, hfin, hsep, h⟩ := hFinite k T hS
  exact IsSplitTorus.exists_finiteGalois_of_finiteSeparable k L T h

/-- The pure-coalgebra descent proposition suffices for the exact finite Galois
splitting target, with finite-stage descent supplied by its proved theorem. -/
theorem finiteGaloisSplitting_of_groupLikeSpanningDescent
    (hDescent : Langlands.CoalgebraDescent.SeparablyClosedGroupLikeSpanningStatement.{u,u,u}) :
    TorusFiniteGaloisSplittingStatement.{u} := by
  apply finiteGaloisSplitting_of_sepClosedSplitting_of_finiteStage
  · intro k _ _ T hT
    exact isSplit_of_isSepClosed_of_prerequisites hDescent T hT
  · intro k _ T _ _ h
    exact h.exists_finiteSeparable_of_separableClosure k T

end Langlands.GroupScheme.SplittingAssembly

namespace Langlands.GroupScheme

/-- Every actual field torus splits over a finite Galois extension. -/
theorem torusFiniteGaloisSplitting : TorusFiniteGaloisSplittingStatement.{u} :=
  SplittingAssembly.finiteGaloisSplitting_of_groupLikeSpanningDescent
    Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning.{u,u,u}

end Langlands.GroupScheme
