import Langlands.Global.AdelicBlockEisensteinRoots
import Langlands.Global.AdelicEisensteinSmoothHeight
import Langlands.Global.ArchimedeanIwasawaChart
import Langlands.Global.ArchimedeanSmoothDifferential
import Langlands.Global.GeneralLinearInfiniteAdelicManifold

/-! # Smooth Iwasawa height for actual block parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter IsDedekindDomain
open scoped CategoryTheory.MonObj Classical Manifold ContDiff Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Langlands.Global.AdelicBlockEisensteinGeometry

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints InfiniteAdelicGroupPoints GeneralLinearGroupPoints

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}
  (B : Langlands.GeneralLinear.BlockShape n)

local notation "GL[F," n "]" => groupScheme (Fin n) (CommRingCat.of F)
local notation "P[F," B "]" =>
  blockParabolicScheme (Fin n) (CommRingCat.of F) (blockShapeWeight B)
local notation "p[F," B "]" =>
  blockParabolicHom (Fin n) (CommRingCat.of F) (blockShapeWeight B)
local notation "Ar" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "G∞" => InfiniteAdelicGroupPoints F GL[F, n]
local notation "M∞" => ArchimedeanMatrix F n

local instance blockSmoothGLAffine : IsAffine (GL[F, n]).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance blockSmoothParabolicAffine : IsAffine (P[F, B]).X.left :=
  blockParabolic_isAffine F B

local instance blockSmoothParabolicClosed : IsClosedImmersion (p[F, B]).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin n) (CommRingCat.of F) (blockShapeWeight B)

omit [NumberField F] in
private theorem archimedeanGLCoordinates_symm_upper
    (g : ArchimedeanGL F n) (hg : g.val.IsUpperTriangular) :
    ((archimedeanGLCoordinates F n).symm g).val.IsUpperTriangular := by
  intro i j hij
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [map_zero, ← archimedeanGLCoordinates_apply, ContinuousMulEquiv.apply_symm_apply]
  exact hg hij

omit [NumberField F] in
/-- Lift a triangular archimedean matrix unit to the actual block parabolic. -/
def parabolicOfUpper (g : ArchimedeanGL F n) (hg : g.val.IsUpperTriangular) :
    InfiniteAdelicGroupPoints F P[F, B] :=
  (blockParabolicPointsEquiv F B Ar).symm
    ⟨_, B.mem_parabolic_of_isUpperTriangular _ (archimedeanGLCoordinates_symm_upper F g hg)⟩

omit [NumberField F] in
private theorem parabolicOfUpper_image (g : ArchimedeanGL F n) (hg : g.val.IsUpperTriangular) :
    affinePointsEquiv (Fin n) (CommRingCat.of F) Ar
      ((P[F, B]).affinePointsTarget (p[F, B]) Ar (parabolicOfUpper F B g hg)) =
        (archimedeanGLCoordinates F n).symm g := by
  let y := (archimedeanGLCoordinates F n).symm g
  have h := congrArg Subtype.val
    ((blockParabolicPointsEquiv F B Ar).apply_symm_apply
      ⟨y, B.mem_parabolic_of_isUpperTriangular y (archimedeanGLCoordinates_symm_upper F g hg)⟩)
  rw [blockParabolicPointsEquiv_val] at h
  exact h

private theorem map_ofInfinite_blockParabolic (q : InfiniteAdelicGroupPoints F P[F, B]) :
    map F P[F, B] GL[F, n] (p[F, B]) (ofInfinite F P[F, B] q) =
      ofInfinite F GL[F, n] ((P[F, B]).affinePointsTarget (p[F, B]) Ar q) := by
  apply (split F GL[F, n]).injective
  have hi (g : AdelicGroupPoints F P[F, B]) :
      infinite F GL[F, n] (map F P[F, B] GL[F, n] (p[F, B]) g) =
        (P[F, B]).affinePointsTarget (p[F, B]) Ar (infinite F P[F, B] g) :=
    DFunLike.congr_fun ((P[F, B]).affinePointsTarget_naturality (p[F, B])
      (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) g
  have hf (g : AdelicGroupPoints F P[F, B]) :
      finite F GL[F, n] (map F P[F, B] GL[F, n] (p[F, B]) g) =
        (P[F, B]).affinePointsTarget (p[F, B]) (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
          (finite F P[F, B] g) :=
    DFunLike.congr_fun ((P[F, B]).affinePointsTarget_naturality (p[F, B])
      (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) g
  change (infinite F GL[F, n] _, finite F GL[F, n] _) =
    (infinite F GL[F, n] _, finite F GL[F, n] _)
  rw [hi, hf, infinite_ofInfinite, finite_ofInfinite, infinite_ofInfinite,
    finite_ofInfinite, map_one]

variable {d : ℕ}

/-- The archimedean triangular Iwasawa charts give local smooth factors for the
actual block-parabolic scheme. -/
theorem hasSmoothLocalIwasawaFactors_blockParabolic
    (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom) :
    IsIwasawaCompact.HasSmoothLocalIwasawaFactors (p[F, B]) (standardCompactPoints F n) hsmooth := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GL[F, n] hsmooth
  let e := infiniteDiffeomorph F n hsmooth
  let eG := (infiniteHomeomorph F n).trans (archimedeanGLCoordinates F n)
  intro a
  obtain ⟨b, k, hb, _, hNear⟩ := ArchimedeanGL.exists_smoothLocalIwasawa F n (e a)
  let x (y : G∞) : M∞ := (e y).val
  have hgood : ∀ᶠ y in 𝓝 a, (b (x y)).IsUpperTriangular ∧ IsUnit (b (x y)) ∧
      k (x y) ∈ unitary M∞ ∧ b (x y) * k (x y) = x y := by
    exact (Units.continuous_val.comp e.continuous).continuousAt hNear
  let bUnit (y : G∞) : ArchimedeanGL F n :=
    if h : IsUnit (b (x y)) then h.unit else 1
  let q (y : G∞) : InfiniteAdelicGroupPoints F P[F, B] :=
    if h : (bUnit y).val.IsUpperTriangular then parabolicOfUpper F B (bUnit y) h else 1
  let kUnit (y : G∞) : ArchimedeanGL F n :=
    if h : k (x y) ∈ unitary M∞ then Unitary.toUnits ⟨k (x y), h⟩ else 1
  have hpar (y : G∞) (hy : (b (x y)).IsUpperTriangular ∧ IsUnit (b (x y))) :
      eG ((P[F, B]).affinePointsTarget (p[F, B]) Ar (q y)) = bUnit y := by
    have hu : (bUnit y).val = b (x y) := by
      simp only [bUnit, dite_eq_left hy.2, IsUnit.unit_spec]
    have ht : (bUnit y).val.IsUpperTriangular := hu ▸ hy.1
    simp only [q, dite_eq_left ht]
    change archimedeanGLCoordinates F n (affinePointsEquiv (Fin n) (CommRingCat.of F) Ar
      ((P[F, B]).affinePointsTarget (p[F, B]) Ar (parabolicOfUpper F B (bUnit y) ht))) = _
    rw [parabolicOfUpper_image, ContinuousMulEquiv.apply_symm_apply]
  refine ⟨q, fun y => eG.symm (kUnit y), ?_, ?_⟩
  · let I := 𝓘(ℝ, smoothModel F d)
    let J := 𝓘(ℝ, M∞)
    let c := ArchimedeanGL.unitsChart F n
    have hbu : ContMDiffAt J J ∞ c.symm (b (x a)) := by
      have hc : ContMDiffOn J J ∞ c.symm (Set.range (Units.val : ArchimedeanGL F n → M∞)) :=
        contMDiffOn_isOpenEmbedding_symm (I := J) Units.isOpenEmbedding_val
      have ha := hgood.self_of_nhds
      exact hc.contMDiffAt
        (Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨ha.2.1.unit, ha.2.1.unit_spec⟩)
    have hx : ContMDiffAt I J ∞ x a :=
      (Units.contMDiff_val (𝕜 := ℝ) (n := ∞)).contMDiffAt.comp a e.contMDiff.contMDiffAt
    have hb' : ContMDiffAt J J ∞ b (x a) := hb.contMDiffAt
    have hbx : ContMDiffAt I J ∞ (fun y => b (x y)) a := hb'.comp a hx
    have hF : ContMDiffAt I I ∞ (fun y => e.symm (c.symm (b (x y)))) a :=
      e.symm.contMDiff.contMDiffAt.comp a (hbu.comp a hbx)
    apply hF.congr_of_eventuallyEq
    filter_upwards [hgood] with y hy
    apply eG.injective
    rw [hpar y ⟨hy.1, hy.2.1⟩]
    change bUnit y = eG (eG.symm (c.symm (b (x y))))
    rw [ContinuousMulEquiv.apply_symm_apply]
    change (if h : IsUnit (b (x y)) then h.unit else 1) = c.symm (b (x y))
    rw [dite_eq_left hy.2.1]
    calc
      hy.2.1.unit = c.symm hy.2.1.unit.val :=
        (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
          Units.val Units.isOpenEmbedding_val (x := hy.2.1.unit)).symm
      _ = c.symm (b (x y)) := congrArg (fun z : M∞ => c.symm z) hy.2.1.unit_spec
  · filter_upwards [hgood] with y hy
    have hku : (kUnit y).val = k (x y) := by
      simp only [kUnit, dite_eq_left hy.2.2.1, Unitary.val_toUnits_apply]
    constructor
    · change eG.symm (kUnit y) ∈ (standardCompactPoints F n).comap (ofInfinite F GL[F, n]).toMonoidHom
      rw [standardCompactPoints_comap_ofInfinite]
      change infiniteHomeomorph F n (eG.symm (kUnit y)) ∈
        standardInfiniteCompact F n
      rw [ArchimedeanGL.mem_standardInfiniteCompact_iff_mem_unitary]
      change (eG (eG.symm (kUnit y))).val ∈ unitary M∞
      rw [ContinuousMulEquiv.apply_symm_apply, hku]
      exact hy.2.2.1
    · rw [map_ofInfinite_blockParabolic F B, ← map_mul]
      congr 1
      apply eG.injective
      rw [map_mul, hpar y ⟨hy.1, hy.2.1⟩, ContinuousMulEquiv.apply_symm_apply]
      apply Units.ext
      change (bUnit y).val * (kUnit y).val = x y
      rw [hku, show (bUnit y).val = b (x y) by
        simp only [bUnit, dite_eq_left hy.2.1, IsUnit.unit_spec]]
      exact hy.2.2.2

/-- The usual block Iwasawa height has smooth complex pairings on every
archimedean slice for the standard compact. -/
theorem hasSmoothHeightPairings_blockParabolic
    (hsmooth : SmoothOfRelativeDimension d (GL[F, n]).X.hom) :
    (isIwasawaCompact_blockParabolic F B).HasSmoothHeightPairings hsmooth :=
  (isIwasawaCompact_blockParabolic F B).hasSmoothHeightPairings_of_localIwasawa hsmooth
    (hasSmoothLocalIwasawaFactors_blockParabolic F B hsmooth)

end Langlands.Global.AdelicBlockEisensteinGeometry
