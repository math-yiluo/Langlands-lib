import Langlands.GroupScheme.Torus.HermitianUniversalMatrix
import Langlands.GroupScheme.Rational.SplitTorus

/-! # The split-rank upper bound for actual Hermitian matrix representations -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open FiniteAlgebraUnits

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {N : ℕ} {G : GroupScheme (Spec (CommRingCat.of K))}
  (H : HermitianMatrix.Form (SU3Root.fieldInvolution K L) (Fin N))
  (ρ : ∀ T : Over (Spec (CommRingCat.of K)),
    (T ⟶ G.X) →* Matrix.GeneralLinearGroup (Fin N)
      (SpecialLinear.WeilRoot.tensorAlgebra K L T))
  (hρinj : ∀ T, Function.Injective (ρ T))
  (hρnat : ∀ {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T) (x : T ⟶ G.X),
    (ρ T' (a ≫ x) : Matrix (Fin N) (Fin N)
      (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
    (ρ T x : Matrix (Fin N) (Fin N)
      (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
        (SpecialLinear.WeilRoot.tensorMap K L a))
  (hρH : ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X),
    ((ρ T x : Matrix (Fin N) (Fin N)
      (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
        (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
      (H.gram : Matrix (Fin N) (Fin N) L).map
        (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
      (ρ T x : Matrix (Fin N) (Fin N)
        (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
      (H.gram : Matrix (Fin N) (Fin N) L).map
        (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)))

include hρinj hρnat hρH in
/-- Every closed split torus is bounded by the actual form's attained Witt index. -/
theorem splitRank_le_wittIndex_of_matrixRepresentation :
    splitRank G ≤ (H.wittIndex : ℕ∞) := by
  classical
  let b := Module.finBasis K (Matrix (Fin N) (Fin N) L)
  let f : G ⟶ groupScheme b := WeilMatrixPoints.hom (b := b) ρ hρnat
  have hf : Mono f.hom.hom.left :=
    WeilMatrixPoints.mono_hom_left (b := b) ρ hρnat hρinj
  let := hf
  unfold splitRank
  refine iSup_le fun I => iSup_le fun hI => iSup_le fun t => iSup_le fun ht => ?_
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  have : IsClosedImmersion t.hom.hom.left := ht
  have hmono : Mono (t ≫ f).hom.hom.left := by
    change Mono (t.hom.hom.left ≫ f.hom.hom.left)
    infer_instance
  have hbound := FiniteMatrixAlgebraTorusWeights.card_le_wittIndex_of_allTest_isometry
    (t ≫ f) hmono H (fun T x => by
      simpa only [show (t ≫ f).hom.hom = t.hom.hom ≫ f.hom.hom from rfl,
        ← Category.assoc, f, WeilMatrixPoints.tensorMatrixEquiv_hom] using
          hρH T (x ≫ t.hom.hom))
  simpa only [Nat.card_eq_fintype_card] using
    (show (Fintype.card I : ℕ∞) ≤ (H.wittIndex : ℕ∞) by exact_mod_cast hbound)

end Langlands.GroupScheme
