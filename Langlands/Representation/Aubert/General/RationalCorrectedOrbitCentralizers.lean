import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.Representation.Aubert.General.RationalWeylComparisonTarget

/-! # From the rational corrected-orbit Levi comparison to actual centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T) (n : normalizerPoints i)

include hT

/-- A whole rational-point comparison under a normalizing point gives equality
of the actual centralizers, after forward conjugation of the second cocharacter. -/
theorem dynamicCentralizer_eq_conjugate_of_rationalPoints
    (hpoints : ∀ x : rationalPoints G,
      x ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints ↔
        (n : rationalPoints G)⁻¹ * x * n ∈
          (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).rationalPoints) :
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
      Dynamic.centralizer
        ((CommGroupScheme.groupHom eta ≫ i) ≫ (G.innerIso (n : rationalPoints G)).hom) := by
  have hc := congrArg
    (fun F : SubgroupFunctor G => F.comap (G.innerIso (n : rationalPoints G)).inv)
    (Dynamic.centralizer_eq_comap_of_iso
      (CommGroupScheme.groupHom eta ≫ i) (G.innerIso (n : rationalPoints G)))
  rw [← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id] at hc
  rw [← groupHom_cocharacterAut_comp i n eta]
  apply dynamicCentralizer_eq_of_rationalPoints_eq hT i zeta
    (cocharacterAut (normalizingAut i n) eta)
  rw [groupHom_cocharacterAut_comp, ← hc, SubgroupFunctor.rationalPoints_comap,
    rationalPoints_map_innerIso_inv]
  ext x
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    using hpoints x

/-- The same comparison, expressed as inverse-image equality of subgroup
functors under the inverse inner automorphism. -/
theorem dynamicCentralizer_eq_comap_innerIso_inv_of_rationalPoints
    (hpoints : ∀ x : rationalPoints G,
      x ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints ↔
        (n : rationalPoints G)⁻¹ * x * n ∈
          (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).rationalPoints) :
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
      (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).comap
        (G.innerIso (n : rationalPoints G)).inv := by
  have h := dynamicCentralizer_eq_conjugate_of_rationalPoints hT i zeta eta n hpoints
  have hc := congrArg
    (fun F : SubgroupFunctor G => F.comap (G.innerIso (n : rationalPoints G)).inv)
    (Dynamic.centralizer_eq_comap_of_iso
      (CommGroupScheme.groupHom eta ≫ i) (G.innerIso (n : rationalPoints G)))
  rw [← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id] at hc
  exact h.trans hc.symm

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- For every actual normalizer lift, the corrected-orbit whole-Levi
comparison determines equality of the full standard Levi subgroup functors. -/
theorem standardLevi_eq_comap_innerIso_inv_of_point_comparison
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (I K : Finset (SimpleRoot i ν))
    (m : Group.RelativeWeyl.normalizer (torusPoints i))
    (hK : ∀ x : rationalPoints G, x ∈ levi i ν I ↔
      (m : rationalPoints G)⁻¹ * x * m ∈ levi i ν K) :
    standardLevi i ν (rootSet i ν I) =
      (standardLevi i ν (rootSet i ν K)).comap
        (G.innerIso (m : rationalPoints G)).inv := by
  have := hG.smooth
  have := hG.connectedSpace
  obtain ⟨⟨zeta, hzeta⟩, hcmpI⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨_, hMI, _⟩ := hcmpI zeta hzeta
  obtain ⟨⟨eta, heta⟩, hcmpK⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν K) (rootSet_subset i ν K)
  obtain ⟨_, hMK, _⟩ := hcmpK eta heta
  have hm : (((normalizerEquiv i hN).symm m) : rationalPoints G) = m :=
    congrArg (fun n : Group.RelativeWeyl.normalizer (torusPoints i) =>
      (n : rationalPoints G)) ((normalizerEquiv i hN).apply_symm_apply m)
  rw [hMI, hMK]
  apply dynamicCentralizer_eq_comap_innerIso_inv_of_rationalPoints
    hi.isSplitSubtorus.1 i zeta eta ((normalizerEquiv i hN).symm m)
  intro x
  rw [← hMI, ← hMK, hm]
  exact hK x

end Langlands.Aubert.General.RationalPointFamily
