import Langlands.GroupScheme.RelativeLevi.SplitFaceSameBaseComparison
import Langlands.GroupScheme.RelativeLevi.SplitDominantFace
import Langlands.GroupScheme.Reductive.RootDatumWeylFiniteness

/-! # Canonical face-filtration terms with a fixed torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent Langlands.GroupTheory
open Langlands.LinearAlgebra.RootDatumFaceHeight
open Langlands.LinearAlgebra.RootDatumFaceBaseComparison

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam fam' : J → (Ga R ⟶ G)} {wt : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (C' : SplitParabolicFaceChart i P fam' wt)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- A root with strictly positive original pairing belongs to every
compatible dominant positive system. -/
theorem isPos_of_coPairing_pos [P.IsReduced] (a : J)
    (ha : 0 < coPairing (P.root a) wt) : C.base.IsPos a := by
  by_contra hn
  let := P.indexNeg
  have hneg := root'_nonneg_of_isPos P C.base C.faceCoweight C.dominant
    ((RootPairing.Base.IsPos.neg_iff_not C.base a).mpr hn)
  have he : P.root (-a) = - P.root a := by
    change P.root (P.reflectionPerm a a) = _
    simp
  change 0 ≤ P.toLinearMap (P.root (-a)) C.faceCoweight at hneg
  rw [he, map_neg, LinearMap.neg_apply] at hneg
  change 0 ≤ - P.root' a C.faceCoweight at hneg
  rw [C.coweight_eq] at hneg
  omega

/-- The positive natural face weights are exactly the original strictly
positive root pairings among the chart's chosen positive roots. -/
theorem weight_pos_iff_coPairing_pos [P.IsReduced] (k : Fin C.chart.dimension) :
    0 < C.weights.weight k ↔ 0 < coPairing (P.root (C.index k)) wt := by
  have hnonneg := root'_nonneg_of_isPos P C.base C.faceCoweight C.dominant
    (C.index k).property
  have h := faceHeight_pos_iff_of_nonneg C.base C.faceCoweight C.dominant
    (C.index k) hnonneg
  rw [← C.weight_eq, C.coweight_eq] at h
  exact_mod_cast h

variable (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)

include hG hmax hP in
/-- Over a nontrivial ring, actual fibrewise root data make the exact
face-height form independent of the chart's compatible positive base. -/
theorem faceHeight_eq_of_sameCocharacter [Nontrivial R] :
    faceHeight C.base C.faceCoweight = faceHeight C'.base C'.faceCoweight := by
  let : P.IsReduced := hP.isReduced
  let := hP.finite_zeroReflectionSubgroup hG hmax C.faceCoweight
  have hdom' : ∀ a ∈ C'.base.support, 0 ≤ P.root' a C.faceCoweight := by
    intro a ha
    rw [C.coweight_eq, ← C'.coweight_eq]
    exact C'.dominant a ha
  calc
    faceHeight C.base C.faceCoweight = faceHeight C'.base C.faceCoweight :=
      faceHeight_eq_of_dominant_bases P C.base C'.base C.faceCoweight C.dominant hdom'
    _ = faceHeight C'.base C'.faceCoweight := by
      apply faceHeight_eq_of_simple_zero_iff
      intro a _
      rw [C.coweight_eq, C'.coweight_eq]

variable (hheight : faceHeight C.base C.faceCoweight = faceHeight C'.base C'.faceCoweight)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization i (P.root a) (fam' a))

include hheight hfam hfam' in
/-- Match only the active roots at a positive cutoff; zero-root lists may
be different for the two bases. -/
theorem range_inclusion_comp_le_of_height_eq [P.IsReduced] (d : ℕ) :
    SubgroupFunctor.range (C.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) ≤
    SubgroupFunctor.range (C'.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)) := by
  rw [range_weightInclusion_comp, range_weightInclusion_comp]
  intro T
  change HeightFiltration.level _ C.weights.weight (d + 1) ≤
    HeightFiltration.level _ C'.weights.weight (d + 1)
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  have hpair : 0 < coPairing (P.root (C.index k)) wt :=
    (C.weight_pos_iff_coPairing_pos k).mp (by omega)
  have hpos' : C'.base.IsPos (C.index k) := C'.isPos_of_coPairing_pos _ hpair
  let l := C'.index.symm ⟨(C.index k : J), hpos'⟩
  have hl : (C'.index l : J) = (C.index k : J) := by simp [l]
  have hw : C.weights.weight k = C'.weights.weight l := by
    have hcast : (C.weights.weight k : ℤ) = (C'.weights.weight l : ℤ) := by
      rw [C.weight_eq, C'.weight_eq, hl, ← hheight]
    exact_mod_cast hcast
  have hr : SubgroupFunctor.range (C.chart.roots (ULift.up k) ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) =
      SubgroupFunctor.range (C'.chart.roots (ULift.up l) ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)) := by
    rw [C.root_comp, C'.root_comp, hl]
    exact (hfam (C.index k)).represents.2.trans (hfam' (C.index k)).represents.2.symm
  have hfactor :
      rootFactor (fun a => C.chart.roots a ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter))
        ULift.up T k =
      rootFactor (fun a => C'.chart.roots a ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter))
        ULift.up T l := by
    rw [rootFactor_eq_range, rootFactor_eq_range]
    exact congrArg (fun F => F.carrier T) hr
  rw [hfactor]
  exact HeightFiltration.le_level _ _ (by rw [← hw]; exact hk)

include hG hmax hP hfam hfam' in
/-- For actual root data over a nontrivial ring, every ambient face-filtration
term is independent of the compatible positive base and all chart choices
except the common torus, root datum and original cocharacter. -/
theorem range_inclusion_comp_sameTorus [Nontrivial R] (d : ℕ) :
    SubgroupFunctor.range (C.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) =
    SubgroupFunctor.range (C'.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)) := by
  let : P.IsReduced := hP.isReduced
  have hh := C.faceHeight_eq_of_sameCocharacter C' hG hmax hP
  exact le_antisymm
    (C.range_inclusion_comp_le_of_height_eq C' hh hfam hfam' d)
    (C'.range_inclusion_comp_le_of_height_eq C hh.symm hfam' hfam d)

/-- The actual terms of any two compatible face charts for the same torus
and original cocharacter are ambient-compatibly isomorphic. -/
def sameTorusTermIso [Nontrivial R] (d : ℕ) :
    C.weights.groupScheme d ≅ C'.weights.groupScheme d := by
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let j' := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)
  let : Mono j.hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).1
  let : Mono j'.hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C'.cocharacter)).1
  let : Mono (C.weights.inclusion d).hom.hom := (C.weights.isRepresentedBy_inclusion d).1
  let : Mono (C'.weights.inclusion d).hom.hom := (C'.weights.isRepresentedBy_inclusion d).1
  have hmono : Mono (C.weights.inclusion d ≫ j).hom.hom := by
    change Mono ((C.weights.inclusion d).hom.hom ≫ j.hom.hom)
    exact mono_comp' (C.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter)).1
  have hmono' : Mono (C'.weights.inclusion d ≫ j').hom.hom := by
    change Mono ((C'.weights.inclusion d).hom.hom ≫ j'.hom.hom)
    exact mono_comp' (C'.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C'.cocharacter)).1
  exact (show (SubgroupFunctor.range (C.weights.inclusion d ≫ j)).IsRepresentedBy
      (C.weights.inclusion d ≫ j) from ⟨hmono, rfl⟩).isoOfIsRepresentedBy
    ⟨hmono', (C.range_inclusion_comp_sameTorus C' hG hmax hP hfam hfam' d).symm⟩

/-- The cross-base, fixed-torus term comparison preserves the exact ambient inclusions. -/
theorem sameTorusTermIso_hom_comp [Nontrivial R] (d : ℕ) :
    (C.sameTorusTermIso C' hG hmax hP hfam hfam' d).hom ≫
      (C'.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)) =
      C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter) := by
  unfold sameTorusTermIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.SplitParabolicFaceChart
