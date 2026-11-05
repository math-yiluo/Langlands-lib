import Langlands.Representation.Aubert.General.RationalCorrectedOrbitRadicalTarget
import Langlands.Representation.Aubert.General.RationalPointSourceGeometry
import Langlands.Representation.Aubert.General.RankOneLongestLiftNormalization
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections
import Langlands.Representation.Aubert.General.GeometricIntersectionTransport

/-! # Actual radical intersections on surviving corrected Aubert orbits -/

noncomputable section

open Classical

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

section Algebraic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hN hStandard hG hi hν in
/-- The mixed intersection of a normalizer-conjugated standard radical with
another standard parabolic has both factors over the original field. -/
theorem conjugateUnipotent_inf_parabolic_eq_mul
    (I J : Finset (SimpleRoot i ν))
    (m : Group.RelativeWeyl.normalizer (torusPoints i)) :
    let V := (unipotent i ν I).map (MulAut.conj (m : rationalPoints G)⁻¹).toMonoidHom
    (↑(V ⊓ parabolic i ν J) : Set (rationalPoints G)) =
      (↑(V ⊓ levi i ν J) : Set (rationalPoints G)) *
        (↑(V ⊓ unipotent i ν J) : Set (rationalPoints G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.isSeparated
  obtain ⟨⟨zeta, hzeta⟩, hcompareI⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨⟨mu, hmu⟩, hcompareJ⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)
  obtain ⟨_, _, hUI⟩ := hcompareI zeta hzeta
  obtain ⟨hPJ, hMJ, hUJ⟩ := hcompareJ mu hmu
  let n := (normalizerEquiv i hN).symm m
  let xi := (cocharacterAut (normalizingAut i n)).symm zeta
  have htransport :
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comap
          (G.innerIso (m : rationalPoints G)).hom =
        Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i) := by
    change (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comap
      (G.innerIso (n : rationalPoints G)).hom = _
    rw [Dynamic.unipotent_eq_comap_of_iso
      (CommGroupScheme.groupHom xi ≫ i) (G.innerIso (n : rationalPoints G)),
      ← groupHom_cocharacterAut_comp, LinearEquiv.apply_symm_apply]
  have hV : (unipotent i ν I).map (MulAut.conj (m : rationalPoints G)⁻¹).toMonoidHom =
      (Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).rationalPoints := by
    have hp := congrArg SubgroupFunctor.rationalPoints htransport
    rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map, ← hUI] at hp
    exact hp
  dsimp only
  rw [hV]
  change (↑((Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).carrier
        (Over.mk (𝟙 _)) ⊓ (standardParabolic i ν (rootSet i ν J)).carrier
          (Over.mk (𝟙 _))) : Set (rationalPoints G)) =
    (↑((Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).carrier
        (Over.mk (𝟙 _)) ⊓ (standardLevi i ν (rootSet i ν J)).carrier
          (Over.mk (𝟙 _))) : Set (rationalPoints G)) *
      (↑((Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).carrier
        (Over.mk (𝟙 _)) ⊓ (standardUnipotent i ν (rootSet i ν J)).carrier
          (Over.mk (𝟙 _))) : Set (rationalPoints G))
  rw [hPJ, hMJ, hUJ]
  exact Dynamic.unipotent_inf_parabolic_eq_mul i (CommGroupScheme.groupHom xi)
    (CommGroupScheme.groupHom mu) (Over.mk (𝟙 _))

end Algebraic

/-- The whole published rational radical-intersection proposition, with the
supplied whole-Levi index retained in both containments. -/
theorem rationalCorrectedOrbitRadicalIntersectionStatement :
    RationalCorrectedOrbitRadicalIntersectionStatement.{u} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X) :=
    pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ _ CM cs hLength hSimple hW
  let : DecidableEq (SimpleRoot i ν) := LinearOrder.toDecidableEq
  intro I j hj m hm K hK
  let w := Support.rankOrderedElement cs.length j hj
  have hRad : ∀ (J : Finset (SimpleRoot i ν)), K ⊆ J → IsMinimal cs J I w →
      ∀ x : rationalPoints G, x ∈ levi i ν J →
        ((m : rationalPoints G) * x * (m : rationalPoints G)⁻¹ ∈ unipotent i ν I ↔
          x ∈ unipotent i ν K) := by
    intro J hKJ hw
    obtain ⟨hL, _, hR⟩ := pointSourceIntersectionIdentities i ν hN hZ cs
      hStandard hG hi hν hInter hLength hSimple I J w⁻¹ (isMinimal_inv cs hw) m hm
    simp only [inv_inv] at hL hR
    have hLeq : geometricSourceIntersection (levi i ν I) (levi i ν J)
        (m : rationalPoints G) = levi i ν K := by
      ext x
      rw [mem_geometricSourceIntersection]
      constructor
      · rintro ⟨_, hx⟩
        simpa [mul_assoc] using (hK ((m : rationalPoints G) * x *
          (m : rationalPoints G)⁻¹)).mp hx
      · intro hx
        refine ⟨levi_le_of_subset i ν hInter hG hi hν K J hKJ hx, (hK _).mpr ?_⟩
        simpa [mul_assoc] using hx
    have hIndex := leviFamily_injective_of_actualLeviWeylIdentification
        (levi i ν) (torusPoints i) cs hW (hL.symm.trans hLeq)
    rw [hIndex] at hR
    intro x hxJ
    constructor
    · intro hx
      have hx' : (⟨x, hxJ⟩ : levi i ν J) ∈
          (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
            (m : rationalPoints G)).subgroupOf (levi i ν J) :=
        (mem_geometricSourceIntersection _ _ _ _).mpr ⟨hxJ, hx⟩
      rw [hR] at hx'
      exact hx'
    · intro hx
      have hx' : (⟨x, hxJ⟩ : levi i ν J) ∈
          (unipotent i ν K).subgroupOf (levi i ν J) := hx
      rw [← hR] at hx'
      exact ((mem_geometricSourceIntersection _ _ _ _).mp hx').2
  constructor
  · intro s hKs hw x hx hxP
    let y : rationalPoints G := (m : rationalPoints G)⁻¹ * x * m
    let V := (unipotent i ν I).map (MulAut.conj (m : rationalPoints G)⁻¹).toMonoidHom
    have hyV : y ∈ V := by
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp [y]⟩
    have hprod := conjugateUnipotent_inf_parabolic_eq_mul i ν hN hStandard hG hi hν
      I (Finset.univ \ s) m
    have hy : y ∈ (↑(V ⊓ parabolic i ν (Finset.univ \ s)) : Set (rationalPoints G)) :=
      ⟨hyV, hxP⟩
    rw [hprod] at hy
    obtain ⟨a, ⟨haV, haJ⟩, b, ⟨_, hbU⟩, hab⟩ := Set.mem_mul.mp hy
    have haI : (m : rationalPoints G) * a * (m : rationalPoints G)⁻¹ ∈
        unipotent i ν I := by
      rcases Subgroup.mem_map.mp haV with ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
    have haK := (hRad (Finset.univ \ s) hKs hw a haJ).mp haI
    have hbK := standardUnipotent_antitone i ν hOrder hG hi hν hKs hbU
    have hyK : y ∈ unipotent i ν K := hab ▸ mul_mem haK hbK
    exact hyK
  · intro s hKs hw x hxJ hxK
    exact (hRad (Finset.univ \ s) hKs hw x hxJ).mpr hxK

end Langlands.Aubert.General.RationalPointFamily
