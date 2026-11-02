import Langlands.AlgebraicGeometry.PointManifold.RegularCharts
import Langlands.AlgebraicGeometry.PointTopology.AffineOpenEmbeddingProofs
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Transport of regular charts through principal affine opens -/

noncomputable section

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology

variable (k : Type) [RCLike k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]

local instance principalChartBasicOpen_isAffine (f : AffineCoordinateRing k X) :
    IsAffine (X.left.basicOpen (U := ⊤) f) :=
  (isAffineOpen_top X.left).basicOpen f

local instance affineOpenCoordinateAlgebra (U : X.left.Opens) [IsAffine U] :
    Algebra (AffineCoordinateRing k X) (AffineCoordinateRing k (openOver k X U)) :=
  inferInstanceAs (Algebra Γ(X.left, ⊤) Γ(U, ⊤))

local instance affineOpenCoordinateTower (U : X.left.Opens) [IsAffine U] :
    IsScalarTower k (AffineCoordinateRing k X)
      (AffineCoordinateRing k (openOver k X U)) :=
  IsScalarTower.of_algebraMap_eq' (affineCoordinateMap_natural k (openOverι k X U)).symm

local instance basicOpenCoordinateLocalization (f : AffineCoordinateRing k X) :
    IsLocalization.Away f
      (AffineCoordinateRing k (openOver k X (X.left.basicOpen (U := ⊤) f))) :=
  Γ_restrict_isLocalization X.left (show Γ(X.left, ⊤) from f)

/-- On an affine open, evaluation of an original section is evaluation of its restriction. -/
theorem regularEvaluation_openPointMap_algebraMap (U : X.left.Opens) [IsAffine U]
    (q : RingPoint k (openOver k X U) k) (a : AffineCoordinateRing k X) :
    regularEvaluation (openPointMap k X k U q) a =
      regularEvaluation q (algebraMap (AffineCoordinateRing k X)
        (AffineCoordinateRing k (openOver k X U)) a) :=
  regularEvaluation_postcomp (openOverι k X U) q a

/-- The section defining a principal open is nonzero at each point of that open. -/
theorem regularEvaluation_basicOpen_ne_zero (f : AffineCoordinateRing k X)
    (q : RingPoint k (openOver k X (X.left.basicOpen (U := ⊤) f)) k) :
    regularEvaluation (openPointMap k X k (X.left.basicOpen (U := ⊤) f) q) f ≠ 0 := by
  rw [regularEvaluation_openPointMap_algebraMap]
  exact isUnit_iff_ne_zero.mp ((IsLocalization.Away.algebraMap_isUnit
    (S := AffineCoordinateRing k (openOver k X (X.left.basicOpen (U := ⊤) f))) f).map
      (regularEvaluation q).toRingHom)

namespace RegularChart

variable {k X} {d : ℕ}

/-- A regular chart on a principal affine open gives a regular chart on the original
actual point space, with denominators cleared into its global coordinate ring. -/
def ofBasicOpen (f : AffineCoordinateRing k X)
    (C : RegularChart k (openOver k X (X.left.basicOpen (U := ⊤) f)) d) :
    RegularChart k X d := by
  classical
  let U := X.left.basicOpen (U := ⊤) f
  let A := AffineCoordinateRing k X
  let B := AffineCoordinateRing k (openOver k X U)
  choose n a ha using fun i => IsLocalization.Away.surj f (C.numerator i)
  choose m b hb using fun i => IsLocalization.Away.surj f (C.denominator i)
  have heval (q : RingPoint k (openOver k X U) k) (s : B) (t : A) (l : ℕ)
      (h : s * algebraMap A B f ^ l = algebraMap A B t) :
      regularEvaluation q s * regularEvaluation (openPointMap k X k U q) f ^ l =
        regularEvaluation (openPointMap k X k U q) t := by
    simpa only [map_mul, map_pow, regularEvaluation_openPointMap_algebraMap] using
      congrArg (regularEvaluation q) h
  refine {
    homeomorph := C.homeomorph.lift_openEmbedding
      (isOpenEmbedding_basicOpenPointMap k X k f)
    numerator := fun i => a i * f ^ m i
    denominator := fun i => b i * f ^ n i
    denominator_ne_zero := ?_
    apply_eq := ?_
    contDiffOn_inverse_evaluation := ?_ }
  · rintro p ⟨q, hq, rfl⟩ i
    have hf := regularEvaluation_basicOpen_ne_zero k X f q
    have hb' := heval q (C.denominator i) (b i) (m i) (hb i)
    rw [map_mul, map_pow, ← hb']
    exact mul_ne_zero (mul_ne_zero (C.denominator_ne_zero q hq i)
      (pow_ne_zero _ hf)) (pow_ne_zero _ hf)
  · rintro p ⟨q, hq, rfl⟩ i
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, C.apply_eq q hq,
      map_mul, map_pow, map_mul, map_pow,
      ← heval q (C.numerator i) (a i) (n i) (ha i),
      ← heval q (C.denominator i) (b i) (m i) (hb i)]
    have hf := regularEvaluation_basicOpen_ne_zero k X f q
    dsimp only [U] at *
    field_simp [hf, C.denominator_ne_zero q hq i]
  · intro a
    simpa only [OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_target, Function.comp_apply,
      openPointMap, regularEvaluation_postcomp] using
      C.contDiffOn_inverse_evaluation (affineCoordinatePullback k (openOverι k X U) a)

@[simp] theorem ofBasicOpen_source (f : AffineCoordinateRing k X)
    (C : RegularChart k (openOver k X (X.left.basicOpen (U := ⊤) f)) d) :
    (C.ofBasicOpen f).homeomorph.source =
      openPointMap k X k (X.left.basicOpen (U := ⊤) f) '' C.homeomorph.source := rfl

end RegularChart

end Langlands.AlgebraicGeometry.PointManifold
