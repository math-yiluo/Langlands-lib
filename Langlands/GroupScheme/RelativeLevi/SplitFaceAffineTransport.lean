import Langlands.GroupScheme.RelativeLevi.RootWeightBaseChange
import Langlands.GroupScheme.RelativeLevi.SplitFaceRootRangeTransport

/-! # Original face terms under coefficient and ambient transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell LocalSplitRootBaseChange
open Langlands.GroupTheory Langlands.LinearAlgebra.RootDatumFaceHeight
open Langlands.LinearAlgebra.RootDatumFaceBaseComparison

variable {R A : Type u} [CommRing R] [CommRing A]
  {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of A))} [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of A)) I ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {fam' : J → (Ga A ⟶ H)} {wt : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (D : SplitParabolicFaceChart j P fam' wt)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)

local instance splitFaceAffineTransport_sourceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance splitFaceAffineTransport_targetAffine : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom

include hG hmax hP in
/-- The canonical face functional depends only on the full datum and the
fixed presenting weight, even across different coefficient rings. -/
theorem faceHeight_eq_of_sameCoordinateData [Nontrivial R] :
    faceHeight C.base C.faceCoweight = faceHeight D.base D.faceCoweight := by
  let : P.IsReduced := hP.isReduced
  let := hP.finite_zeroReflectionSubgroup hG hmax C.faceCoweight
  have hdom : ∀ a ∈ D.base.support, 0 ≤ P.root' a C.faceCoweight := by
    intro a ha
    rw [C.coweight_eq, ← D.coweight_eq]
    exact D.dominant a ha
  calc
    faceHeight C.base C.faceCoweight = faceHeight D.base C.faceCoweight :=
      faceHeight_eq_of_dominant_bases P C.base D.base C.faceCoweight C.dominant hdom
    _ = faceHeight D.base D.faceCoweight := by
      apply faceHeight_eq_of_simple_zero_iff
      intro a _
      rw [C.coweight_eq, D.coweight_eq]

section Coefficients

variable [Algebra R A]

local instance splitFaceAffineTransport_pullbackAffine :
    IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom (algebraBaseMap R A) inferInstance

variable (f : (baseChange (algebraBaseMap R A)).obj G ≅ H)
  (D' : SplitParabolicFaceChart
    (splitTorus.baseChangeHom (K := A) G I i ≫ f.hom) P
    (fun a => baseChangeRoot A (fam a) ≫ f.hom) wt)

include hG hmax hP in
/-- The original term pulled to a coefficient algebra and then to an
isomorphic actual ambient group is the independently constructed face term
on the transported roots. The target algebra may be the zero ring. -/
theorem range_baseChange_comp_ambientIso [Nontrivial R] (d : ℕ) :
    SubgroupFunctor.range
      ((baseChange (algebraBaseMap R A)).map
        (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
          (AffineRegularBorel.cocharacter i C.cocharacter)) ≫ f.hom) =
    SubgroupFunctor.range (D'.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter
        (splitTorus.baseChangeHom (K := A) G I i ≫ f.hom) D'.cocharacter)) := by
  have hheight := C.faceHeight_eq_of_sameCoordinateData D' hG hmax hP
  apply SubgroupFunctor.ext
  intro T
  rw [SubgroupFunctor.range_comp_carrier, C.range_affineBaseChange_inclusion,
    D'.range_inclusion_comp_eq_allRootSubgroup]
  change (HeightFiltration.level
    (rootFactor (fun a => baseChangeRoot A (fam a)) (allRootIndex J) T)
    (fun k => C.allRootWeight ((allRootIndex J) k)) (d + 1)).map
      ((yonedaGrp.map f.hom).app (Opposite.op T)).hom =
    HeightFiltration.level
      (rootFactor (fun a => baseChangeRoot A (fam a) ≫ f.hom) (allRootIndex J) T)
      (fun k => D'.allRootWeight ((allRootIndex J) k)) (d + 1)
  rw [HeightFiltration.map_level]
  congr 1
  · funext k
    exact map_rootFactor (fun a => baseChangeRoot A (fam a)) (allRootIndex J) f.hom T k
  · funext k
    exact congrArg Int.toNat
      (LinearMap.congr_fun hheight (P.rootSpanMem ℤ ((allRootIndex J) k)))

end Coefficients
end Langlands.GroupScheme.SplitParabolicFaceChart
