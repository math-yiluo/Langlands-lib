import Langlands.GroupScheme.IdentityJetLieDeterminant
import Langlands.AlgebraicGeometry.Picard.DisjointOpenCoverAmple
import Langlands.GroupScheme.Lie.DeterminantLineBundle

/-! # Variable-rank reduction of actual Lie determinant-dual positivity -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Actual finite cotangent frames used solely to define the clopen rank loci. -/
def cotangentRankFrames : FiniteLocalFrames G.cotangentAtIdentity :=
  FiniteLocalFrames.choose (G.cotangentAtIdentity_hasFiniteLocalBasis ‹Smooth G.X.hom›)

/-- The actual group scheme pulled back to one clopen cotangent rank locus. -/
def rankBaseGroup (k : ℕ) : GroupScheme ((cotangentRankFrames G).rankOpen k).toScheme :=
  (baseChange ((cotangentRankFrames G).rankOpen k).ι).obj G

local instance rankBaseGroup_affine (k : ℕ) : IsAffineHom (rankBaseGroup G k).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom ((cotangentRankFrames G).rankOpen k).ι)
  exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

local instance rankBaseGroup_smooth (k : ℕ) : Smooth (rankBaseGroup G k).X.hom := by
  change Smooth
    (CategoryTheory.Limits.pullback.snd G.X.hom ((cotangentRankFrames G).rankOpen k).ι)
  infer_instance

omit [IsAffineHom G.X.hom] in
/-- The actual cotangent sheaf of the rank-restricted group admits an affine
frame cover with one fixed finite index. -/
theorem rankBaseGroup_exists_affineCover (k : ℕ) :
    ∃ (J : Type u) (U : J → ((cotangentRankFrames G).rankOpen k).toScheme.affineOpens),
      (⨆ j, (U j).1) = ⊤ ∧ Nonempty
        (∀ j, SheafOfModules.free
          (R := ((cotangentRankFrames G).rankOpen k).toScheme.ringCatSheaf.over (U j).1)
          (ULift.{u} (Fin k)) ≅ (rankBaseGroup G k).cotangentAtIdentity.over (U j).1) := by
  obtain ⟨J, U, hU, ⟨e⟩⟩ := (cotangentRankFrames G).exists_affineCover_rankOpen k
  let b := ((cotangentRankFrames G).rankOpen k).ι
  let : IsIso (cotangentBaseChangeMap b G) := cotangentBaseChangeIsIso _ _ b G
  let E := asIso (cotangentBaseChangeMap b G)
  exact ⟨J, U, hU, ⟨fun j => e j ≪≫
    (SheafOfModules.overFunctor
      ((cotangentRankFrames G).rankOpen k).toScheme.ringCatSheaf (U j).1).mapIso E⟩⟩

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- Positivity of positive-order actual jets on the clopen rank loci implies
positivity of the original actual Lie determinant dual, with no rank premise. -/
theorem lieDeterminantDual_isAmple_of_rankJets
    (hJ : ∀ k, ∃ n, 0 < n ∧ (determinant (rankBaseGroup G k) n).IsAmple) :
    (smoothLieDeterminant G ‹Smooth G.X.hom›).dual.IsAmple := by
  apply (cotangentRankFrames G).isAmple_of_rankOpen
    (smoothLieDeterminant G ‹Smooth G.X.hom›).dual
  intro k
  obtain ⟨J, U, hU, ⟨e⟩⟩ := rankBaseGroup_exists_affineCover G k
  obtain ⟨n, hn, hJn⟩ := hJ k
  have hL : (smoothLieDeterminant (rankBaseGroup G k) (rankBaseGroup_smooth G k)).dual.IsAmple :=
    lieDeterminantDual_isAmple_of_jet (rankBaseGroup G k) U hU e n hn hJn
  let b := ((cotangentRankFrames G).rankOpen k).ι
  let E :
      (LineBundle.pullback b).obj (smoothLieDeterminant G ‹Smooth G.X.hom›).dual ≅
        (smoothLieDeterminant (rankBaseGroup G k) (rankBaseGroup_smooth G k)).dual :=
    LineBundle.dualPullbackIso b (smoothLieDeterminant G ‹Smooth G.X.hom›) ≪≫
      LineBundle.dualIso (smoothLieDeterminantBaseChangeIso b G ‹Smooth G.X.hom›)
  exact hL.of_iso ((LineBundle.forget _).mapIso E.symm)

omit [IsAffineHom G.X.hom] [CompactSpace S] [QuasiSeparatedSpace S] in
private theorem rankOpen_isClosedImmersion (k : ℕ) :
    IsClosedImmersion ((cotangentRankFrames G).rankOpen k).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact ((cotangentRankFrames G).rankOpen_isClopen k).1)

/-- Original actual jet positivity gives Lie determinant-dual positivity once
actual jet module base change is supplied on the clopen rank inclusions. -/
theorem lieDeterminantDual_isAmple_of_jet_rankBaseChange (n : ℕ) (hn : 0 < n)
    (hJ : (determinant G n).IsAmple)
    (hbase : ∀ k, Nonempty
      ((Scheme.Modules.pullback ((cotangentRankFrames G).rankOpen k).ι).obj (module G n) ≅
        module (rankBaseGroup G k) n)) :
    (smoothLieDeterminant G ‹Smooth G.X.hom›).dual.IsAmple := by
  apply lieDeterminantDual_isAmple_of_rankJets G
  intro k
  let b := ((cotangentRankFrames G).rankOpen k).ι
  let : IsClosedImmersion b := rankOpen_isClosedImmersion G k
  obtain ⟨e⟩ := hbase k
  let E : (LineBundle.pullback b).obj (determinant G n) ≅ determinant (rankBaseGroup G k) n :=
    finiteLocallyFreeDeterminantPullbackIso (hasFiniteLocalBasis G n) b ≪≫
      finiteLocallyFreeDeterminantIso ((hasFiniteLocalBasis G n).pullback b)
        (hasFiniteLocalBasis (rankBaseGroup G k) n) e
  exact ⟨n, hn, (hJ.pullback_of_isAffineHom b).of_iso ((LineBundle.forget _).mapIso E)⟩

end Langlands.GroupScheme.IdentityJet
