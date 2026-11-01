import Langlands.Representation.CuspidalSupport.TripleInductionMaps
import Langlands.Representation.Induction.ThreeFactorProductPresentation
import Langlands.Representation.Tensor.SmoothSubquotients
import Langlands.Group.GL.RankReindex

/-! Actual injection transport between the two triple bracketings. -/

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Parabolic

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual normalized product map that fixes the first factor and maps
the second factor by its supplied intertwiner. -/
def leftProductMap {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (C : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      {B B' : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)},
      B.representation.IntertwiningMap B'.representation →
      (T.normalizedProductInduced (Shahidi.twoBlocks a b ha hb)
        (fun k => (twoBlockFactors ha hb C B k).representation)).IntertwiningMap
      (T.normalizedProductInduced (Shahidi.twoBlocks a b ha hb)
        (fun k => (twoBlockFactors ha hb C B' k).representation)) := by
  let := T.topology
  intro C B B' f
  exact T.normalizedParabolicInducedMap (Shahidi.twoBlocks a b ha hb)
    (FiniteTensor.externalMap (Fin.cases
      (Representation.IntertwiningMap.id C.representation) (Fin.cases f finZeroElim)))

/-- An actual injection in the second factor stays injective under the
normalized product with a fixed first factor. -/
theorem leftProductMap_injective {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (C : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      {B B' : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)}
      (f : B.representation.IntertwiningMap B'.representation),
      Function.Injective f → Function.Injective (leftProductMap F T ha hb C f) := by
  let := T.topology
  intro C B B' f hf
  let factors : ∀ i,
      (twoBlockFactors ha hb C B i).representation.IntertwiningMap
        (twoBlockFactors ha hb C B' i).representation :=
    Fin.cases (Representation.IntertwiningMap.id C.representation) (Fin.cases f finZeroElim)
  have htm : Function.Injective (FiniteTensor.externalMap factors) := by
    change Function.Injective (PiTensorProduct.map (fun i => (factors i).toLinearMap))
    exact FiniteTensor.piTensorMap_injective _
      (Fin.cases Function.injective_id (Fin.cases hf finZeroElim))
  exact T.normalizedParabolicInducedMap_injective _ (FiniteTensor.externalMap factors) htm

end Langlands.Parabolic

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Pullback along the entry-preserving group reindexing of equal ranks,
on the same representation carrier. -/
def rankPullback {m n : ℕ} (h : m=n) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier) →
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier) :=
  letI := T.topology
  fun E => SmoothRep.of
    (E.representation.comp (reindex (R := F.Carrier) (finCongr h)).toMonoidHom)
    (isSmooth_comp _ (continuous_reindex_finCongr h) E.isSmooth)

/-- Rank pullback preserves irreducibility. -/
theorem rankPullback_irreducible {m n : ℕ} (h : m=n) :
    letI := T.topology
    ∀ E : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier),
      E.IsIrreducible → (rankPullback F T h E).IsIrreducible := by
  subst h
  let := T.topology
  intro E hE
  change Representation.IsIrreducible (E.representation.comp
    (reindex (R := F.Carrier) (finCongr (rfl : m=m))).toMonoidHom)
  rw [reindex_finCongr_rfl]
  exact hE

/-- The same linear map intertwines after rank pullback. -/
def rankPullbackMap {m n : ℕ} (h : m=n) :
    letI := T.topology
    ∀ {E Z : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)},
      E.representation.IntertwiningMap Z.representation →
      (rankPullback F T h E).representation.IntertwiningMap
        (rankPullback F T h Z).representation := by
  let := T.topology
  intro E Z f
  exact { toLinearMap := f.toLinearMap
          isIntertwining' := fun g => f.isIntertwining'
            (reindex (R := F.Carrier) (finCongr h) g) }

/-- Reflect an actual intertwiner through equality-based rank pullback. -/
def rankPullbackMapReflect {m n : ℕ} (h : m=n) :
    letI := T.topology
    ∀ {E Z : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)},
      (rankPullback F T h E).representation.IntertwiningMap
        (rankPullback F T h Z).representation →
      E.representation.IntertwiningMap Z.representation := by
  let := T.topology
  intro E Z f
  change Representation.IntertwiningMap
    (E.representation.comp (reindex (R := F.Carrier) (finCongr h)).toMonoidHom)
    (Z.representation.comp (reindex (R := F.Carrier) (finCongr h)).toMonoidHom) at f
  refine { toLinearMap := f.toLinearMap, isIntertwining' := ?_ }
  intro g
  have hg := f.isIntertwining' ((reindex (R := F.Carrier) (finCongr h)).symm g)
  change f.toLinearMap.comp
      (E.representation ((reindex (R := F.Carrier) (finCongr h))
        ((reindex (R := F.Carrier) (finCongr h)).symm g))) =
    (Z.representation ((reindex (R := F.Carrier) (finCongr h))
      ((reindex (R := F.Carrier) (finCongr h)).symm g))).comp f.toLinearMap at hg
  simpa only [MulEquiv.apply_symm_apply] using hg

/-- Reflection preserves the supplied injection. -/
theorem rankPullbackMapReflect_injective {m n : ℕ} (h : m=n) :
    letI := T.topology
    ∀ {E Z : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)}
      (f : (rankPullback F T h E).representation.IntertwiningMap
        (rankPullback F T h Z).representation),
      Function.Injective f → Function.Injective (rankPullbackMapReflect F T h f) := by
  let := T.topology
  intro E Z f hf
  change Function.Injective (fun v : E => (f v : Z)) at hf ⊢
  exact hf

/-- The uniform and literal right-bracketed three-block inductions agree
after the entry-preserving associativity rank pullback. -/
def uniformRightInductionEquiv {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (A B C : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d F.Carrier)),
      (rankPullback F T (Nat.add_assoc d d d)
        ((T.normalizedProductInductionFunctor (threeBlocks d d d hd hd hd)).obj
          (threeBlockSmoothFamily A B C))).representation.Equiv
      ((T.normalizedProductInductionFunctor (threeBlocksRight d d d hd hd hd)).obj
        (threeBlockSmoothFamily A B C)).representation := by
  let := T.topology
  intro A B C
  exact threeBlockRankCastEquiv.{uF,uV} T d d d hd hd hd A B C

/-- An injection into the literal right-bracketed induction yields the
actual uniform triple Jacquet occurrence over the original ambient rank. -/
theorem uniformTripleOccurrence_of_rightInductionInjection {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ (E : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (d+(d+d)) F.Carrier))
      (A B C : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
      E.IsIrreducible →
      ∀ f : (rankPullback F T (Nat.add_assoc d d d) E).representation.IntertwiningMap
        ((T.normalizedProductInductionFunctor (threeBlocksRight d d d hd hd hd)).obj
          (threeBlockSmoothFamily A.obj B.obj C.obj)).representation,
        Function.Injective f →
        SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj C.obj)
          ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) := by
  let := T.topology
  intro E A B C hE f hf
  let Z := (T.normalizedProductInductionFunctor (threeBlocks d d d hd hd hd)).obj
    (threeBlockSmoothFamily A.obj B.obj C.obj)
  let e := uniformRightInductionEquiv F T hd A.obj B.obj C.obj
  let g : (rankPullback F T (Nat.add_assoc d d d) E).representation.IntertwiningMap
      (rankPullback F T (Nat.add_assoc d d d) Z).representation :=
    e.symm.toIntertwiningMap.comp f
  have hg : Function.Injective g := e.symm.injective.comp hf
  exact uniformTripleOccurrence_of_inductionInjection.{uF,uV} F T hd E A B C hE
    (rankPullbackMapReflect F T (Nat.add_assoc d d d) (E := E) (Z := Z) g)
    (rankPullbackMapReflect_injective F T (Nat.add_assoc d d d) g hg)

end Langlands.CuspidalSupport
