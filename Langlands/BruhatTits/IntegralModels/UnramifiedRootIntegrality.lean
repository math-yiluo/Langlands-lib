import Langlands.BruhatTits.IntegralModels.UnramifiedNonnegativeIntegrality
import Langlands.Geometry.Building.TorusRestrictedRootFixer

/-! # Recovered integral root points and nonnegative restricted depth -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [Smooth G.X.hom]

private instance rootIntegralityExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable
  (L : RelativeComponentModelData ↥𝒪[F] F G)
  (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : UnramifiedComponentModelRecovery L E)
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} [Mono iS.hom.hom.left] {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (f : S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = iS)
  (hS : IsSplitTorus S.toGrp)
  (hopp : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (x : D.Apartment)
  (hfull : E.full.integralPoints =
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      D.pointwiseFixer (D.apartmentMap '' ({x} : Set D.Apartment)))

include e hGK hiT hf hfull

omit [Mono iS.hom.hom.left] in
/-- A root point integral in the recovered full model has nonnegative
torus-then-field restricted depth. This direction uses no centralizer datum. -/
theorem nonnegative_restrictedDepth_of_mem_full_integralPoints
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hgi : g ∈ L.full.integralPoints) :
    0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g := by
  have hfK :
      CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  have haK :
      characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S a ∈
        relativeRoots (CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
          (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) := by
    rw [hfK]
    exact (mem_roots_baseChange_iff (K := inertiaFixedField F) G S hS iS a).mpr ha
  have hgiK : rationalExtend F (inertiaFixedField F) G g ∈
      E.full.integralPoints := by
    rwa [e.full_integralPoints_eq_comap] at hgi
  rw [hfull] at hgiK
  have hgfix : rationalExtend F (inertiaFixedField F) G g ∈
      D.reducedFixer (D.apartmentMap x) :=
    D.mem_reducedFixer.mpr
      (D.mem_pointwiseFixer.mp hgiK.2 _ ⟨x, Set.mem_singleton x, rfl⟩)
  have hgrootK := rationalExtend_mem_rootGroupPoints
    (K := inertiaFixedField F) iS a hg
  rw [← hfK] at hgrootK
  have hdepth : rationalExtend F (inertiaFixedField F) G g ∈
      torusRestrictedRootDepthSubgroup x.isValuation
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S a) 0 := by
    rw [← D.restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero hGK hiT
      (hS.baseChange (algebraBaseMap F (inertiaFixedField F))) hopp _ _ haK.1 x]
    exact ⟨hgrootK, hgfix⟩
  have hfil : g ∈ rootFiltration iS
      (torusFieldRestrictedRootFunctionFamily
        (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
        (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)) a 0 := by
    rw [rootFiltration_torusFieldRestrictedRootFunctionFamily iS hS
      hiT.isSplitSubtorus.1 hopp _ _ hfK a ha 0]
    exact hdepth
  simpa using hfil.2

omit [Mono iS.hom.hom.left] in
/-- Neutral root integrality has the same nonnegative-depth consequence. -/
theorem nonnegative_restrictedDepth_of_mem_neutral_integralPoints
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hgi : g ∈ L.neutral.integralPoints) :
    0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g := by
  apply nonnegative_restrictedDepth_of_mem_full_integralPoints
    L E e hGK hiT D f hf hS hopp x hfull ha hg
  exact L.neutralPoints_le_full (L.neutralPoints_eq.symm ▸ hgi)

variable
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

include C hDC

/-- For actual lower root points, recovered neutral integrality is equivalent
to nonnegative restricted depth. -/
theorem mem_neutral_integralPoints_iff_nonnegative_restrictedDepth
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a) :
    g ∈ L.neutral.integralPoints ↔
      0 ≤ torusFieldRestrictedRootFunctionFamily
        (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
        (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g :=
  ⟨nonnegative_restrictedDepth_of_mem_neutral_integralPoints
      L E e hGK hiT D f hf hS hopp x hfull ha hg,
    mem_neutral_integralPoints_of_nonnegative_restrictedDepth
      L E e hGK hiT D C hDC f hf hS hopp x hfull ha hg⟩

include hS hopp in
/-- The root intersection of the recovered neutral image is the exact
preimage of the canonical upper restricted depth-zero subgroup. -/
theorem rootGroupPoints_inf_neutral_integralPoints_eq_restrictedDepthZero
    {a : characterLattice S} (ha : a ∈ relativeRoots iS) :
    rootGroupPoints iS a ⊓ L.neutral.integralPoints =
      torusFieldRestrictedRootDepthSubgroup
        (G := G)
        (j := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
        x.isValuation
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a 0 := by
  have hfK :
      CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  apply SetLike.coe_injective
  rw [← rootFiltration_torusFieldRestrictedRootFunctionFamily
    iS hS hiT.isSplitSubtorus.1 hopp x.isValuation _ hfK a ha 0]
  ext g
  change (g ∈ rootGroupPoints iS a ∧ g ∈ L.neutral.integralPoints) ↔
    g ∈ rootGroupPoints iS a ∧ _
  exact and_congr_right fun hg => by
    simpa using mem_neutral_integralPoints_iff_nonnegative_restrictedDepth
      L E e hGK hiT D f hf hS hopp x hfull C hDC ha hg

/-- The depth-zero comparison as an equivalence preserving the original
generic root point. -/
def neutralRootIntegralEquivRestrictedDepthZero
    {a : characterLattice S} (ha : a ∈ relativeRoots iS) :
    (rootGroupPoints iS a ⊓ L.neutral.integralPoints :
      Subgroup (rationalPoints G)) ≃*
      torusFieldRestrictedRootDepthSubgroup
        (G := G)
        (j := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
        x.isValuation
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a 0 :=
  MulEquiv.subgroupCongr
    (rootGroupPoints_inf_neutral_integralPoints_eq_restrictedDepthZero
      L E e hGK hiT D f hf hS hopp x hfull C hDC ha)

@[simp] theorem neutralRootIntegralEquivRestrictedDepthZero_coe
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    (g : (rootGroupPoints iS a ⊓ L.neutral.integralPoints :
      Subgroup (rationalPoints G))) :
    (neutralRootIntegralEquivRestrictedDepthZero
      L E e hGK hiT D f hf hS hopp x hfull C hDC ha g : rationalPoints G) = g :=
  rfl

end Langlands.BruhatTits.IntegralModels
