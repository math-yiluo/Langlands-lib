import Langlands.GroupScheme.RosenlichtSplitStatement
import Langlands.GroupScheme.SplitSolvableSmoothExtension
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverReduction
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Rational.SplitTorusDominatedSolvableQuotientReduction
import Langlands.GroupScheme.Rational.TorusGeneratedSplitGeometricRadicalAssembly
import Langlands.GroupScheme.Rational.SplitTorusDominationOperations
import Langlands.GroupScheme.Rational.SplitTorusDominationProof
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Torus.SplitOfDomination

/-! # Rosenlicht's criterion for split solvable groups (Milne 16.58): proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A dominant morphism of schemes over `k` from a split torus to a group, not
necessarily preserving identities, becomes a pointed dominant parametrization
after right translation by the inverse of the image of the identity. -/
theorem hasPointedSplitTorusDomination_of_dominant
    {G P : GroupScheme (Spec (CommRingCat.of k))} (hP : IsSplitTorus P)
    (φ : P.X ⟶ G.X) (hφ : IsDominant φ.left) :
    HasPointedSplitTorusDomination G := by
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ φ
  let e := G.rightTranslationIso g⁻¹
  have : IsDominant φ.left := hφ
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  refine ⟨P, φ ≫ e.hom, hP, ?_, ?_⟩
  · change IsDominant (φ.left ≫ e.hom.left)
    infer_instance
  · rw [← Category.assoc]
    change g ≫ G.rightTranslation g⁻¹ = 1
    rw [G.comp_rightTranslation, G.constantPoint_self, mul_inv_cancel]

/-- **Rosenlicht's criterion** (Milne 2017, Theorem 16.58). A smooth affine
solvable group over a field that is dominated by the underlying scheme of a
split torus is split solvable. -/
theorem rosenlichtSplitSolvable : RosenlichtSplitSolvableStatement.{u} := by
  intro k _ G _ _ hsolv ⟨n, φ, hφ⟩
  have hdom : HasPointedSplitTorusDomination G :=
    hasPointedSplitTorusDomination_of_dominant
      (isSplitTorus_splitTorus (ULift.{u} (Fin n))) φ hφ
  have : ConnectedSpace G.X.left := hdom.hasPointedTorusDomination.connectedSpace
  obtain ⟨U, D, i, q, hi, hs, hc, hu, hq, hD⟩ :=
    splitTorusDominatedSolvableQuotient_of_solvableTorusQuotient solvableTorusQuotient
      k G hsolv hdom
  have hsU : RelativeRoot.IsSplitUnipotent U :=
    TorusKernelDomination.representative_isSplitUnipotent_of_stableVector
      unipotentSplitTorusDomination RelativeRoot.splitUnipotentStableVectorSubgroup
      i hi hs hc hu q hq hD hdom
  have : Surjective q.hom.hom.left := hq.2.1
  have hDs : IsSplitTorus D := (hdom.postcomp q).isSplitTorus hD
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Smooth U.X.hom := hs
  have : ConnectedSpace U.X.left := hc
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient
    i q hi hq hsolv hsU hDs

end Langlands.GroupScheme
