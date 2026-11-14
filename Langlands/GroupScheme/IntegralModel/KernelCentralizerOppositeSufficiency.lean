import Langlands.GroupScheme.IntegralModel.KernelCentralizerOppositeFactors
import Langlands.GroupScheme.IntegralModel.KernelCentralizerResidueQuotient
import Langlands.GroupScheme.Rational.RootKernelIdentityAction
import Langlands.GroupScheme.Rational.CrossTorusRootTransport

/-! # Opposite-factor sufficiency from the ambient residue quotient -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [PerfectField (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    (i : T.toGrp ⟶ M.group) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν)
    [Mono (M.genericHom i).hom.hom.left]

local notation "b" => (Spec.algebraMap R K)
local notation "b₀" => (residueBaseMap R)
set_option quotPrecheck false in
local notation "iK" => (M.genericHom i :
  ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T).toGrp ⟶ G)
local notation "aK" => (characterLattice.baseChange b T a)

variable {H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (q : M.specialFibre ⟶ H) (hH : IsConnectedReductive H)
    (hqs : Smooth q.hom.hom.left) (hq : HasSmoothConnectedUnipotentKernel q)
    (hi : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj T)
      ((baseChange (residueBaseMap R)).map i ≫ q))

include hT hpos hH hqs hq hi in
/-- Nonidentity in the original residue quotient makes both prescribed
opposite factors of an integral generic root point integral. -/
theorem KernelCentralizerData.integral_oppositeFactors_of_residueQuotient
    (D : KernelCentralizerData M i a)
    (hroot : HasRelativeRootSystem (T := (CommGroupScheme.baseChange b).obj T) iK)
    (ha : aK ∈ relativeRoots (T := (CommGroupScheme.baseChange b).obj T) iK)
    (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange b).obj T) iK aK).carrier
        (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (hqx : rationalPoints.map q (M.reduction x) ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair (T := (CommGroupScheme.baseChange b).obj T)
      iK aK (M.integralPointMap x) p) :
    p.1 ∈ M.integralPoints ∧ p.2 ∈ M.integralPoints := by
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  let : IsAffineHom D.componentGroup.X.hom := D.model.affine
  let : IsAffine D.componentGroup.X.left :=
    isAffine_of_isAffineHom D.componentGroup.X.hom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : Smooth H.X.hom := hH.smooth
  obtain ⟨E, jE, hjE, hEs, hE⟩ :=
    RelativeRoot.kernelCentralizer_hasSmoothClosedRepresentative_overRing
      ((baseChange b₀).map i ≫ q) (hT.baseChange b₀)
      (characterLattice.baseChange b₀ T a) hH.smooth
  let : Smooth E.X.hom := hEs
  let : IsClosedImmersion jE.hom.hom.left := hjE
  let : IsAffineHom E.X.hom := by
    rw [← jE.hom.hom.w]
    infer_instance
  have ha₀ : characterLattice.baseChange b₀ T a ≠ 0 :=
    KernelCentralizerData.character_fibre_ne_zero b₀ ν hpos
  have hQ : IsConnectedReductive (identityComponent E) :=
    RelativeRoot.kernelCentralizerComponentReductive
      (IsLocalRing.ResidueField R) H hH
      ((CommGroupScheme.baseChange b₀).obj T) (hT.baseChange b₀)
      ((baseChange b₀).map i ≫ q) (characterLattice.baseChange b₀ T a) ha₀
      E jE hE hjE hEs
  let : IsAffineHom (identityComponent E).X.hom := hQ.isAffineHom
  let qC := D.fibreQuotientMap b₀ q hE
  have hqCs : Smooth qC.hom.hom.left ∧ Surjective qC.hom.hom.left :=
    D.fibreQuotientMap_smooth_surjective b₀ q hE hT hqs
  have hqCK : HasSmoothConnectedUnipotentKernel qC :=
    D.fibreQuotientMap_kernel_geometry b₀ q hE hT hq
  let : ConnectedSpace (kernel qC).X.left := hqCK.2.1
  have hiC : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange b₀).obj T)
      ((baseChange b₀).map (D.torus hT) ≫ qC) := by
    rw [show qC = D.fibreQuotientMap b₀ q hE from rfl,
      D.fibreQuotientMap_torus b₀ q hE hT]
    exact hi.kernelCentralizerIdentityTorus
      (characterLattice.baseChange b₀ T a) jE hE hjE
  let : IsClosedImmersion
      ((baseChange b₀).map (D.torus hT) ≫ qC).hom.hom.left := hiC.1.2
  let : SurjectiveOnStalks
      ((baseChange b₀).map (D.torus hT) ≫ qC).hom.hom.left := hiC.1.2.toSurjectiveOnStalks
  let : Mono ((baseChange b₀).map (D.torus hT) ≫ qC).hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective hiC.1.2.isClosedEmbedding.injective
  obtain ⟨e, he, -⟩ :=
    RelativeRoot.existsUnique_kernelCentralizerIdentityQuotientAction
      (T := (CommGroupScheme.baseChange b₀).obj T) (G := H) (C := E)
      ((baseChange b₀).map i ≫ q) (hT.baseChange b₀)
      (characterLattice.baseChange b₀ T a) jE hE ha₀
  have heC : e.restrict
      (CommGroupScheme.groupHom (characterLattice.baseChange b₀ T a)) =
      AutomorphicAction.conjugation ((baseChange b₀).map (D.torus hT) ≫ qC) := by
    rw [show qC = D.fibreQuotientMap b₀ q hE from rfl,
      D.fibreQuotientMap_torus b₀ q hE hT]
    exact he
  have ht :
      (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange b).obj T) iK aK).comap
          M.genericIso.hom =
        RelativeRoot.subgroup ((baseChange b).map i) aK := by
    simpa only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp] using
      RelativeRoot.subgroup_comap_of_transport
        (Iso.refl ((CommGroupScheme.baseChange b).obj T)) M.genericIso
        (i := (baseChange b).map i) (j := iK)
        (by
          change _ = 𝟙 _ ≫ _
          rw [Category.id_comp]
          rfl)
        aK
  have hxraw : baseChangeSectionHom b M.group x ∈
      (RelativeRoot.subgroup ((baseChange b).map i) aK).carrier
        (Over.mk (𝟙 _)) := by
    rw [← ht]
    exact hx
  let y := D.integralRootUnipotentLift hT ν hpos x hxraw
  let xC : D.model.integralSections := rationalPoints.map
    (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ D.torus hT)) y.val
  have hxC : rationalPoints.map (D.componentHom ≫ D.fullHom) xC = x := y.property
  have hnon : D.model.reduction xC ≫
      ((baseChange b₀).map (D.componentHom ≫ D.fullHom) ≫ q).hom.hom ≠ 1 := by
    have hs : D.model.reduction xC ≫
        ((baseChange b₀).map (D.componentHom ≫ D.fullHom) ≫ q).hom.hom =
        rationalPoints.map q (M.reduction x) := by
      change (baseChangeSectionHom b₀ D.componentGroup xC) ≫
        ((baseChange b₀).map (D.componentHom ≫ D.fullHom) ≫ q).hom.hom = _
      rw [Grp.comp_hom_hom, ← Category.assoc,
        ← baseChangeSectionHom_naturality b₀ (D.componentHom ≫ D.fullHom) xC]
      change rationalPoints.map q
        (M.reduction (rationalPoints.map (D.componentHom ≫ D.fullHom) xC)) = _
      rw [hxC]
    rwa [hs]
  have hy1 : rationalPoints.map qC (D.model.reduction xC) ≠ 1 :=
    D.fibreQuotientMap_ne_one_of_ambient b₀ q hE (D.model.reduction xC) hnon
  exact D.integral_oppositeFactors_of_componentQuotient
    (Q := identityComponent E) (T := T) hT ν hpos
    qC hQ hqCs.1 hqCs.2 hqCK.2.2 hiC e heC
    hroot ha y.val x y.property hy1 hx hx1 p hp

include hT hpos hH hqs hq hi in
/-- The ambient quotient criterion, with the centralizer data constructed
from the split torus in the given smooth integral model. -/
theorem integral_oppositeFactors_of_residueQuotient
    (hroot : HasRelativeRootSystem (T := (CommGroupScheme.baseChange b).obj T) iK)
    (ha : aK ∈ relativeRoots (T := (CommGroupScheme.baseChange b).obj T) iK)
    (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange b).obj T) iK aK).carrier
        (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (hqx : rationalPoints.map q (M.reduction x) ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair (T := (CommGroupScheme.baseChange b).obj T)
      iK aK (M.integralPointMap x) p) :
    p.1 ∈ M.integralPoints ∧ p.2 ∈ M.integralPoints :=
  KernelCentralizerData.integral_oppositeFactors_of_residueQuotient
    M i hT a ν hpos q hH hqs hq hi (KernelCentralizerData.ofSplit M i a hT)
    hroot ha x hx hx1 hqx p hp

/-- Choose integral lifts with the exact generic images of the prescribed
ambient opposite-factor pair. -/
def residueQuotientOppositeFactorLift
    (hroot : HasRelativeRootSystem (T := (CommGroupScheme.baseChange b).obj T) iK)
    (ha : aK ∈ relativeRoots (T := (CommGroupScheme.baseChange b).obj T) iK)
    (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange b).obj T) iK aK).carrier
        (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (hqx : rationalPoints.map q (M.reduction x) ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair (T := (CommGroupScheme.baseChange b).obj T)
      iK aK (M.integralPointMap x) p) :
    {z : M.integralSections × M.integralSections //
      M.integralPointMap z.1 = p.1 ∧ M.integralPointMap z.2 = p.2} := by
  have h := M.integral_oppositeFactors_of_residueQuotient
    i hT a ν hpos q hH hqs hq hi hroot ha x hx hx1 hqx p hp
  exact ⟨(Classical.choose h.1, Classical.choose h.2),
    Classical.choose_spec h.1, Classical.choose_spec h.2⟩

end Langlands.GroupScheme.IntegralModel
