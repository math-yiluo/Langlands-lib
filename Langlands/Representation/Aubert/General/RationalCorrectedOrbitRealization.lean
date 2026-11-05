import Langlands.Representation.Aubert.General.RationalCorrectedOrbitCentralizers
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitModulusTarget

/-! # Actual cocharacters for a corrected orbit with a common Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Two actual cocharacters of the original split torus realizing the
standard source and the forward conjugate of the second standard subgroup,
with equality of their entire centralizer functors. -/
structure CorrectedOrbitCocharacterRealization
    (I K : Finset (SimpleRoot i ν)) (m : rationalPoints G) where
  zeta : cocharacterLattice T
  eta : cocharacterLattice T
  parabolic_left : standardParabolic i ν (rootSet i ν I) =
    Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)
  levi_left : standardLevi i ν (rootSet i ν I) =
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)
  unipotent_left : standardUnipotent i ν (rootSet i ν I) =
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)
  parabolic_right :
    (standardParabolic i ν (rootSet i ν K)).comap (G.innerIso m).inv =
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)
  levi_right : (standardLevi i ν (rootSet i ν K)).comap (G.innerIso m).inv =
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)
  unipotent_right :
    (standardUnipotent i ν (rootSet i ν K)).comap (G.innerIso m).inv =
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)
  centralizer_eq : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)

/-- The exact whole-Levi comparison of a corrected orbit supplies such a
realization, using the actual scheme normalizer point above the given lift. -/
def correctedOrbitCocharacterRealization
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (I K : Finset (SimpleRoot i ν))
    (m : Group.RelativeWeyl.normalizer (torusPoints i))
    (hK : ∀ x : rationalPoints G, x ∈ levi i ν I ↔
      (m : rationalPoints G)⁻¹ * x * m ∈ levi i ν K) :
    CorrectedOrbitCocharacterRealization i ν I K m := by
  have := hG.smooth
  have := hG.connectedSpace
  have hI := hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  let zeta := Classical.choose hI.1
  obtain ⟨hPI, hMI, hUI⟩ := hI.2 zeta (Classical.choose_spec hI.1)
  have hKK := hStandard k G hG T i hi ν hν (rootSet i ν K) (rootSet_subset i ν K)
  let xi := Classical.choose hKK.1
  obtain ⟨hPK, hMK, hUK⟩ := hKK.2 xi (Classical.choose_spec hKK.1)
  let n : normalizerPoints i := (normalizerEquiv i hN).symm m
  have hm : (n : rationalPoints G) = m :=
    congrArg (fun q : Group.RelativeWeyl.normalizer (torusPoints i) =>
      (q : rationalPoints G)) ((normalizerEquiv i hN).apply_symm_apply m)
  let eta := cocharacterAut (normalizingAut i n) xi
  have he : CommGroupScheme.groupHom eta ≫ i =
      (CommGroupScheme.groupHom xi ≫ i) ≫
        (G.innerIso (m : rationalPoints G)).hom := by
    rw [groupHom_cocharacterAut_comp, hm]
  have hP :
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
        (Dynamic.parabolic (CommGroupScheme.groupHom xi ≫ i)).comap
          (G.innerIso (m : rationalPoints G)).inv := by
    rw [he]
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using Dynamic.parabolic_eq_comap_of_iso
        ((CommGroupScheme.groupHom xi ≫ i) ≫
          (G.innerIso (m : rationalPoints G)).hom)
        (G.innerIso (m : rationalPoints G)).symm
  have hM :
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) =
        (Dynamic.centralizer (CommGroupScheme.groupHom xi ≫ i)).comap
          (G.innerIso (m : rationalPoints G)).inv := by
    rw [he]
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using Dynamic.centralizer_eq_comap_of_iso
        ((CommGroupScheme.groupHom xi ≫ i) ≫
          (G.innerIso (m : rationalPoints G)).hom)
        (G.innerIso (m : rationalPoints G)).symm
  have hU :
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) =
        (Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).comap
          (G.innerIso (m : rationalPoints G)).inv := by
    rw [he]
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using Dynamic.unipotent_eq_comap_of_iso
        ((CommGroupScheme.groupHom xi ≫ i) ≫
          (G.innerIso (m : rationalPoints G)).hom)
        (G.innerIso (m : rationalPoints G)).symm
  refine ⟨zeta, eta, hPI, hMI, hUI, ?_, ?_, ?_, ?_⟩
  · rw [hPK]
    exact hP.symm
  · rw [hMK]
    exact hM.symm
  · rw [hUK]
    exact hU.symm
  · rw [← hMI, hM, ← hMK]
    exact standardLevi_eq_comap_innerIso_inv_of_point_comparison
      i ν hStandard hG hi hν hN I K m hK

namespace CorrectedOrbitCocharacterRealization

variable {i ν} {I K : Finset (SimpleRoot i ν)} {m : rationalPoints G}
    (r : CorrectedOrbitCocharacterRealization i ν I K m)

/-- The first dynamic radical is literally the original standard subgroup
of rational points. -/
theorem unipotent_left_points :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints =
      unipotent i ν I := by
  rw [← r.unipotent_left]

/-- The second dynamic radical consists exactly of the points whose inverse
conjugates belong to the original second standard radical. -/
theorem unipotent_right_points :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints =
      (unipotent i ν K).comap (MulAut.conj m⁻¹).toMonoidHom := by
  rw [← r.unipotent_right, SubgroupFunctor.rationalPoints_comap,
    rationalPoints_map_innerIso_inv]

/-- The dynamic positive intersection is exactly the orbit intersection
appearing in the squared-modulus target. -/
theorem intersection_points :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints =
      CorrectedFiltration.orbitUnipotentIntersection
        (unipotent i ν I) (unipotent i ν K) m := by
  change (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints ⊓
      (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints = _
  rw [r.unipotent_left_points, r.unipotent_right_points]
  rfl

end CorrectedOrbitCocharacterRealization

end Langlands.Aubert.General.RationalPointFamily
