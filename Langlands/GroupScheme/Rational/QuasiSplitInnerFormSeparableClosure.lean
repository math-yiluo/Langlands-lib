import Langlands.GroupScheme.Descent.FiniteStageLocalIsoRecovery
import Langlands.GroupScheme.Rational.InnerDiscrepancyRefinement

/-! # Finite-Galois presentations from separable-closure innerness -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Descent.FiniteStage

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
  {G H A : GroupScheme (Spec (CommRingCat.of k))}
  {e : (baseChange (algebraBaseMap k Ω)).obj G ≅
    (baseChange (algebraBaseMap k Ω)).obj H}

/-- Inner discrepancy of the specified larger-field family descends to its finite model. -/
theorem IsoModel.hasInnerDiscrepancy (D : IsoModel k Ω e)
    (a : AutomorphicAction A G) (ha : a.IsFaithful)
    (he : (LocalGroupIso.ofBaseChangeIso
      (U := Over.mk (algebraBaseMap k Ω)) e).HasInnerDiscrepancy a) :
    D.localIso.HasInnerDiscrepancy a := by
  let r := QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val
  obtain ⟨hs, hf, hq⟩ :=
    QuasiSplitInnerForm.coverRefinement_fpqc D.fieldOfDefinition.1.val
  let : Surjective r.left := hs
  let : Flat r.left := hf
  let : QuasiCompact r.left := hq
  apply LocalGroupIso.HasInnerDiscrepancy.of_refine r ha
  change (D.localIso.refine
    (QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val)).HasInnerDiscrepancy a
  rw [D.localIso_refine]
  exact he

/-- Construct the natural finite-stage cocycle from innerness over the larger field. -/
def IsoModel.innerCocycle (D : IsoModel k Ω e)
    (a : AutomorphicAction A G) (ha : a.IsFaithful)
    (he : (LocalGroupIso.ofBaseChangeIso
      (U := Over.mk (algebraBaseMap k Ω)) e).HasInnerDiscrepancy a) :
    Langlands.GroupScheme.Cocycle A (Over.mk (algebraBaseMap k D.fieldOfDefinition.1)) :=
  D.localIso.innerCocycle a ha (D.hasInnerDiscrepancy a ha he)

/-- The constructed cocycle gives the finite model's actual all-test discrepancy. -/
theorem IsoModel.innerCocycle_hasDiscrepancy (D : IsoModel k Ω e)
    (a : AutomorphicAction A G) (ha : a.IsFaithful)
    (he : (LocalGroupIso.ofBaseChangeIso
      (U := Over.mk (algebraBaseMap k Ω)) e).HasInnerDiscrepancy a) :
    D.localIso.HasDiscrepancy a (D.innerCocycle a ha he) :=
  D.localIso.innerCocycle_hasDiscrepancy a ha (D.hasInnerDiscrepancy a ha he)

/-- Extending the finite cocycle recovers the canonical cocycle of the specified family. -/
theorem IsoModel.innerCocycle_refine (D : IsoModel k Ω e)
    (a : AutomorphicAction A G) (ha : a.IsFaithful)
    (he : (LocalGroupIso.ofBaseChangeIso
      (U := Over.mk (algebraBaseMap k Ω)) e).HasInnerDiscrepancy a) :
    (D.innerCocycle a ha he).refine
        (QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val) =
      (LocalGroupIso.ofBaseChangeIso
        (U := Over.mk (algebraBaseMap k Ω)) e).innerCocycle a ha he := by
  apply (LocalGroupIso.ofBaseChangeIso
    (U := Over.mk (algebraBaseMap k Ω)) e).innerCocycle_unique a ha he
  have h :
      (D.localIso.refine
        (QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val)).HasDiscrepancy a
        ((D.innerCocycle a ha he).refine
          (QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val)) :=
    LocalGroupIso.HasDiscrepancy.refine (D.innerCocycle_hasDiscrepancy a ha he)
      (QuasiSplitInnerForm.coverRefinement D.fieldOfDefinition.1.val)
  rw [D.localIso_refine] at h
  exact @h

end Descent.FiniteStage

namespace QuasiSplitInnerForm

variable {k : Type u} [Field k]
  {G H A : GroupScheme (Spec (CommRingCat.of k))}

/-- Build an actual finite-Galois inner-form presentation from structural data and
innerness of a specified isomorphism over the separable closure. -/
def ofSeparableClosure (hG : IsConnectedReductive G) (hH : IsQuasiSplit H)
    (q : H ⟶ A) (hq : IsAdjointQuotient q) (hA : IsQuasiSplit A)
    (e : (baseChange (algebraBaseMap k (SeparableClosure k))).obj H ≅
      (baseChange (algebraBaseMap k (SeparableClosure k))).obj G)
    (he : (LocalGroupIso.ofBaseChangeIso
      (U := Over.mk (algebraBaseMap k (SeparableClosure k))) e).HasInnerDiscrepancy
        hq.innerAction) :
    QuasiSplitInnerForm G := by
  let : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let D := Descent.FiniteStage.isoModel k (SeparableClosure k) e
  let : FiniteDimensional k D.fieldOfDefinition.1 := D.fieldOfDefinition.2
  exact ofFiniteSeparable H hH A q hq hA D.localIso
    (D.innerCocycle hq.innerAction hq.innerAction_isFaithful he)
    (D.innerCocycle_hasDiscrepancy hq.innerAction hq.innerAction_isFaithful he)

end QuasiSplitInnerForm

end Langlands.GroupScheme
