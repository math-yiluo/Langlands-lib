import Langlands.GroupScheme.RelativeLevi.PicardSplitTorusConjugacy
import Langlands.GroupScheme.Torus.EtaleCoordinateConjugacy
import Langlands.GroupScheme.Reductive.RelativeCentralizerReductive
import Langlands.GroupScheme.Reductive.AffineRegularBorel
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Actual coordinate-torus conjugacy inside the original parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

namespace splitTorus

variable {R : CommRingCat.{u}} {I J : Type u}
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (G : GroupScheme (Spec R)) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec R) I ⟶ G) (j : splitTorus (Spec R) J ⟶ G)
  (wt : I → ℤ) (wt' : J → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Actual etale coordinate-conjugacy data whose conjugator belongs to the
base change of the original dynamic parabolic, on the original affine base. -/
structure EtaleParabolicCoordinateConjugacyData (s : Spec R)
    extends EtaleCoordinateConjugacyData G i j s where
  mem_parabolic : conjugator ∈
    ((Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).baseChange projection).carrier
      (Over.mk (𝟙 (Spec ring)))

/-- Two fibrewise maximal split tori presenting the same actual parabolic are
etale locally conjugate inside that parabolic, retaining one fixed integral
coordinate matrix and the exact ambient inclusion square. -/
def etaleParabolicCoordinateConjugacyAt
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
    (hj : IsFibrewiseMaximalTorus (T := commGroupScheme _ J) j)
    (hPar : Dynamic.parabolic (AffineRegularBorel.cocharacter i wt) =
      Dynamic.parabolic (AffineRegularBorel.cocharacter j wt')) (s : Spec R) :
    EtaleParabolicCoordinateConjugacyData G i j wt s := by
  let χ := AffineRegularBorel.cocharacter i wt
  let H := Dynamic.Affine.parabolicScheme χ
  let p : H ⟶ G := Dynamic.Affine.parabolicHom χ
  have hp : (Dynamic.parabolic χ).IsRepresentedBy p :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hpc : IsClosedSubgroup p := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  let : IsAffineHom H.X.hom := hpc.isAffineHom
  let : Smooth H.X.hom := (dynamicBaseSmoothConnected _ G χ H p).2.1 hp |>.1
  have hle : SubgroupFunctor.range i ≤ Dynamic.parabolic χ := by
    rw [← hp.2]
    exact AffineRegularBorel.torus_range_le i wt
  have hle' : SubgroupFunctor.range j ≤ Dynamic.parabolic χ := by
    change SubgroupFunctor.range j ≤ Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)
    rw [hPar, ← (Dynamic.Affine.isRepresentedBy_parabolicHom
      (AffineRegularBorel.cocharacter j wt')).2]
    exact AffineRegularBorel.torus_range_le j wt'
  let t : splitTorus (Spec R) I ⟶ H := hp.factorHom i hle
  let t' : splitTorus (Spec R) J ⟶ H := hp.factorHom j hle'
  have ht : t ≫ p = i := hp.factorHom_comp i hle
  have ht' : t' ≫ p = j := hp.factorHom_comp j hle'
  have hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) t :=
    IsFibrewiseMaximalTorus.of_comp hpc (ht.symm ▸ hi)
  have hmax' : IsFibrewiseMaximalTorus (T := commGroupScheme _ J) t' :=
    IsFibrewiseMaximalTorus.of_comp hpc (ht'.symm ▸ hj)
  let D := etaleCoordinateConjugacyAt H t t' hmax hmax' s
  let pA := (GroupScheme.baseChange D.projection).map p
  let g := D.conjugator ≫ pA.hom.hom
  refine {
    ring := D.ring
    projection := D.projection
    etale := D.etale
    mem_range := D.mem_range
    coordinateMap := D.coordinateMap
    conjugator := g
    square := ?_
    mem_parabolic := ?_ }
  · have he := congrArg (fun f => f ≫ pA) D.square
    rw [Category.assoc, innerIso_hom_comp] at he
    simpa only [pA, Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
      ht, ht', g] using he
  · have hpa := hp.baseChange D.projection
    rw [← hpa.2]
    exact SubgroupFunctor.mem_range.mpr ⟨D.conjugator, rfl⟩

end splitTorus
end Langlands.GroupScheme
