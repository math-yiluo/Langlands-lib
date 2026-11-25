import Langlands.GroupScheme.RelativeLevi.FaceHeightCocharacter
import Langlands.GroupScheme.RelativeLevi.SplitParabolicFaceChart
import Langlands.GroupScheme.RelativeLevi.SplitParabolicComparison
import Langlands.GroupScheme.RelativeUnipotent.RootWeightScaling

/-! # Actual contracting and parabolic groups of a face-height realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {wt : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)

/-- A chosen positive-multiple realization of the original unscaled face height. -/
def faceRealization : RootSpanCocharacterRealization P
    (faceHeight C.base C.faceCoweight) :=
  faceHeightCocharacterRealization P C.base C.faceCoweight

/-- The positive natural multiplier used only to realize the face height. -/
def faceMultiplier : ℕ := C.faceRealization.multiplier.toNat

/-- A coordinate cocharacter realizing a positive multiple of the face height. -/
def faceCocharacter : I → ℤ := C.faceRealization.cocharacter

theorem faceMultiplier_pos : 0 < C.faceMultiplier := by
  have h := C.faceRealization.multiplier_pos
  change 0 < C.faceRealization.multiplier.toNat
  omega

theorem facePairing (a : J) :
    coPairing (P.root a) C.faceCocharacter =
      (C.faceMultiplier : ℤ) * faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) := by
  rw [faceMultiplier, Int.toNat_of_nonneg (le_of_lt C.faceRealization.multiplier_pos)]
  exact C.faceRealization.pairing_eq (P.rootSpanMem ℤ a)

theorem facePairing_nonneg {a : J} (ha : C.base.IsPos a) :
    0 ≤ coPairing (P.root a) C.faceCocharacter := by
  rw [C.facePairing]
  exact mul_nonneg (Int.natCast_nonneg _) (faceHeight_nonneg_of_isPos _ _ ha)

theorem facePairing_nonpos {a : J} (ha : ¬ C.base.IsPos a) :
    coPairing (P.root a) C.faceCocharacter ≤ 0 := by
  let := P.indexNeg
  have hp := C.facePairing_nonneg ((RootPairing.Base.IsPos.neg_iff_not C.base a).mpr ha)
  have he : P.root (-a) = -P.root a := by
    change P.root (P.reflectionPerm a a) = _
    simp
  change 0 ≤ coPairingLinear C.faceCocharacter (P.root (-a)) at hp
  rw [he, map_neg] at hp
  change 0 ≤ - coPairing (P.root a) C.faceCocharacter at hp
  omega

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))

include hG hmax hP hfam in
/-- The realized face cocharacter has exactly the original actual contracting
subgroup functor, on all scheme tests over the arbitrary base ring. -/
theorem unipotent_faceCocharacter :
    Dynamic.unipotent (AffineRegularBorel.cocharacter i C.faceCocharacter) =
      Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) := by
  classical
  let neg := (Finite.equivFin {a // ¬ C.base.IsPos a}).symm
  let pos := C.index
  let : IsOpenImmersion
      (cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP C.base fam hfam neg pos
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let : Mono j.hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).1
  let W := C.weights.scale C.faceMultiplier C.faceMultiplier_pos
  have hw (k : Fin C.chart.dimension) : (W.weight k : ℤ) =
      coPairing (P.root (pos k)) C.faceCocharacter := by
    rw [C.facePairing]
    change ((C.faceMultiplier * C.weights.weight k : ℕ) : ℤ) = _
    rw [Nat.cast_mul, C.weight_eq]
  have hn (k : Fin (Nat.card {a // ¬ C.base.IsPos a})) :
      coPairing (P.root (neg k)) C.faceCocharacter ≤ 0 :=
    C.facePairing_nonpos (neg k).property
  let : IsAffineHom (AffineRegularBorel.contractingGroup i C.faceCocharacter).X.hom :=
    AffineRegularBorel.isAffineHom_contractingGroup i C.faceCocharacter
  let : IsAffine (AffineRegularBorel.contractingGroup i C.faceCocharacter).X.left :=
    isAffine_of_isAffineHom (AffineRegularBorel.contractingGroup i C.faceCocharacter).X.hom
  have hnew := isRepresentedBy_positiveWeightInclusion
    (neg := fun k => (neg k : J)) (pos := fun k => (pos k : J))
    C.chart W j C.root_comp (fun a T t c => (hfam a).equivariant T t c)
    C.faceCocharacter hw hn
    (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.faceCocharacter))
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C.faceCocharacter))
  have hz (k : Fin C.chart.dimension) : W.weight k = 0 ↔ C.weights.weight k = 0 := by
    change C.faceMultiplier * C.weights.weight k = 0 ↔ _
    simp only [Nat.mul_eq_zero, C.faceMultiplier_pos.ne', false_or]
  have hold := W.isRepresentedBy_zeroInclusion_of_sameZero C.weights hz j _ C.represented
  exact hnew.2.symm.trans hold.2

include hG hmax hP hfam in
/-- The actual positive face term represents the realized cocharacter's
contracting group with the same original unscaled inclusion. -/
theorem isRepresentedBy_faceCocharacter :
    (Dynamic.unipotent (AffineRegularBorel.cocharacter i C.faceCocharacter)).IsRepresentedBy
      (C.weights.inclusion 0 ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) := by
  rw [C.unipotent_faceCocharacter hG hmax hP hfam]
  exact C.represented

variable [Nontrivial R] [DecidableEq I]

include hG hmax hP hfam in
/-- The realized face cocharacter also defines exactly the original actual
parabolic; no regularity assumption on the original cocharacter is used. -/
theorem parabolic_faceCocharacter :
    Dynamic.parabolic (AffineRegularBorel.cocharacter i C.faceCocharacter) =
      Dynamic.parabolic (AffineRegularBorel.cocharacter i wt) :=
  AffineRegularBorel.parabolic_eq_of_unipotent_eq i P hG hmax hP fam hfam
    C.faceCocharacter wt (C.unipotent_faceCocharacter hG hmax hP hfam)

end Langlands.GroupScheme.SplitParabolicFaceChart
