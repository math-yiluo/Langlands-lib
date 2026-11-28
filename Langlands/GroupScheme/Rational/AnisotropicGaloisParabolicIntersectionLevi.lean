import Langlands.GroupScheme.Dynamic.AffineDecomposition
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceReduction
import Langlands.GroupScheme.FactoredKernel
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Rational.AnisotropicConnectedSubgroupReductivity
import Langlands.GroupScheme.Rational.GaloisParabolicOrbitIntersectionDimension
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Levi embeddings for descended parabolic intersections in anisotropic groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

section LeviProjection

variable {k : Type u} [Field k] [CharZero k]
  {H P Z : GroupScheme (Spec (CommRingCat.of k))}

/-- In characteristic zero the restriction of a homomorphism with unipotent
kernel to a closed reductive subgroup of its source is a closed embedding. -/
theorem IsConnectedReductive.isClosedSubgroup_comp_of_unipotent_kernel
    (hH : IsConnectedReductive H) [IsAffineHom Z.X.hom] [LocallyOfFiniteType Z.X.hom]
    (f : H ⟶ P) (hf : IsClosedSubgroup f) (q : P ⟶ Z)
    (hU : IsUnipotent (kernel q)) [IsAffineHom (kernel q).X.hom]
    [LocallyOfFiniteType (kernel q).X.hom] :
    IsClosedSubgroup (f ≫ q) := by
  let W := kernel (f ≫ q)
  let w := kernelι (f ≫ q)
  have hw : IsClosedSubgroup w := kernelι_isClosedImmersion _
  let g : W ⟶ kernel q := FactoredKernel.map (f ≫ q) f q rfl
  have hg : IsClosedSubgroup g := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (FactoredKernel.isPullback_scheme (f ≫ q) f q rfl) hf
  have hW : IsUnipotent W := unipotentClosedSubgroup k (kernel q) W g hg hU
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth H.X.hom := hH.smooth
  let : ConnectedSpace H.X.left := hH.connectedSpace
  have hs : Smooth W.X.hom := affineCartierSmooth k W hw.isAffineHom hw.locallyOfFiniteType
  have hc : ConnectedSpace W.X.left :=
    charZeroUnipotentConnected k W hw.isAffineHom hw.locallyOfFiniteType hW
  have htriv := hH.hasTrivialUnipotentRadical W w hw hs hc hW
    (HopfPrimitive.isNormal_range_kernelι (f ≫ q))
  let : Mono (f ≫ q).hom.hom := SubgroupFunctor.mono_of_range_kernel_eq_bot _ htriv
  exact HomImage.isClosedSubgroup_of_mono _

omit [CharZero k] in
private theorem lieDimension_eq_of_smooth_closed
    [IsAffineHom H.X.hom] [IsAffineHom P.X.hom]
    (f : H ⟶ P) (hf : IsClosedSubgroup f) (hs : Smooth f.hom.hom.left) :
    Lie.dimension H = Lie.dimension P := by
  let : Mono f.hom.hom := hf.mono_overHom
  let e := LinearEquiv.ofBijective (Lie.targetMapLinear f k)
    ⟨Lie.targetMapLinear_injective f k, Lie.targetMapLinear_surjective_of_smooth f k hs⟩
  exact e.finrank_eq

end LeviProjection

section Orbit

variable (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local notation "B" => GroupScheme.baseChange (algebraBaseMap k K)
local notation "GK" => (Functor.obj B G)

private local instance affineGK : IsAffine (GK).X.left := isAffine_of_isAffineHom (GK).X.hom

/-- For an anisotropic semisimple group in characteristic zero, the identity
component of the descended parabolic orbit intersection is reductive. Its base
change embeds in the given parabolic's Levi by the actual limit homomorphism. -/
theorem IsAnisotropic.exists_reductive_subgroup_of_parabolic_orbit
    (hG : IsAnisotropic G) (hss : IsSemisimple G)
    (χ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ GK)
    (hP : IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ)) (c : ℕ)
    (hc : haveI := hP.isClosedSubgroup.isAffineHom
      Lie.dimension GK ≤ Lie.dimension (Dynamic.Affine.parabolicScheme χ) + c) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G) (hj : IsClosedSubgroup j),
      haveI := hj.isAffineHom
      IsConnectedReductive H ∧
      Lie.dimension GK ≤ Lie.dimension H + finrank k K * c ∧
      ∃ (f : (B).obj H ⟶ Dynamic.Affine.parabolicScheme χ),
        f ≫ Dynamic.Affine.parabolicHom χ = (B).map j ∧
        IsClosedSubgroup (f ≫ Corepresented.limitGroupHom (Dynamic.Affine.cocharacter χ)) := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨C, i, hi, horbit, hdim⟩ :=
    galoisParabolicOrbitIntersectionDimension k K G hss.isConnectedReductive _ _ hP c hc
  let : IsAffineHom C.X.hom := hi.isAffineHom
  let : Smooth C.X.hom := affineCartierSmooth k C hi.isAffineHom hi.locallyOfFiniteType
  let H := identityComponent C
  let a : H ⟶ C := identityComponentι C
  let ha := IdentityComponent.isClosedSubgroup_identityComponentι C
  let j : H ⟶ G := a ≫ i
  have hj : IsClosedSubgroup j := ha.comp hi
  let : IsAffineHom H.X.hom := hj.isAffineHom
  have hH := hG.isConnectedReductive_of_closed_of_isSemisimple hss hj inferInstance
  have hdimH : Lie.dimension H = Lie.dimension C :=
    lieDimension_eq_of_smooth_closed a ha inferInstance
  refine ⟨H, j, hj, hH, hdimH.symm ▸ hdim, ?_⟩
  let P := Dynamic.Affine.parabolicScheme χ
  let p : P ⟶ GK := Dynamic.Affine.parabolicHom χ
  let hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hleC : SubgroupFunctor.range ((B).map i) ≤ SubgroupFunctor.range p := by
    rw [horbit]
    intro T x hx
    have hv := (SubgroupFunctor.mem_intersection.mp hx) (1 : K ≃ₐ[k] K)
    rw [map_one] at hv
    exact hv
  have hle : SubgroupFunctor.range ((B).map j) ≤ Dynamic.parabolic χ := by
    rw [← hp.2]
    intro T x hx
    apply hleC T
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ ((B).map a).hom.hom, by
      rw [show j = a ≫ i from rfl, Functor.map_comp, Grp.comp_hom_hom, Category.assoc]⟩
  let f := hp.liftOfLE ((B).map j) hle
  have hf : f ≫ p = (B).map j := hp.liftOfLE_comp _ _
  have hfclosed : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hP.isClosedSubgroup (hf ▸ hj.baseChange (algebraBaseMap k K))
  let Z := Dynamic.Affine.centralizerScheme χ
  let U := Dynamic.Affine.unipotentScheme χ
  let q : P ⟶ Z := Corepresented.limitGroupHom (Dynamic.Affine.cocharacter χ)
  let z := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  let : IsAffineHom Z.X.hom := z.isAffineHom
  let : LocallyOfFiniteType (GK).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K)))
  let : LocallyOfFiniteType Z.X.hom := z.locallyOfFiniteType
  let : IsAffineHom P.X.hom := hP.isClosedSubgroup.isAffineHom
  let : LocallyOfFiniteType P.X.hom := hP.isClosedSubgroup.locallyOfFiniteType
  let hq := (show IsClosedSubgroup (kernelι q) from kernelι_isClosedImmersion _)
  let : IsAffineHom (kernel q).X.hom := hq.isAffineHom
  let : LocallyOfFiniteType (kernel q).X.hom := hq.locallyOfFiniteType
  have hU : IsUnipotent U := dynamicUnipotentUnipotenceReduction unitriangularUnipotent
    unipotentClosedSubgroup K GK χ U _ (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
  have hUq : IsUnipotent (kernel q) :=
    IsUnipotent.of_iso (Corepresented.unipotentIsoKernel (Dynamic.Affine.cocharacter χ)).symm hU
  have hHK := connectedReductiveFieldExtensionStatement k K H hH
  exact ⟨f, hf, hHK.isClosedSubgroup_comp_of_unipotent_kernel f hfclosed q hUq⟩

end Orbit

/-- A reductive subgroup with the parabolic orbit dimension bound whose
base change embeds in the Levi. -/
def AnisotropicGaloisParabolicIntersectionLeviStatement : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsGalois k K]
      (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G → IsSemisimple G →
    let B := GroupScheme.baseChange (algebraBaseMap k K)
    let GK := B.obj G
    haveI : IsAffine GK.X.left := isAffine_of_isAffineHom GK.X.hom
    ∀ (χ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ GK)
      (hP : IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ)) (c : ℕ)
      (_hc : haveI := hP.isClosedSubgroup.isAffineHom
        Lie.dimension GK ≤ Lie.dimension (Dynamic.Affine.parabolicScheme χ) + c),
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G) (hj : IsClosedSubgroup j),
        haveI := hj.isAffineHom
        IsConnectedReductive H ∧
        Lie.dimension GK ≤ Lie.dimension H + finrank k K * c ∧
        ∃ (f : B.obj H ⟶ Dynamic.Affine.parabolicScheme χ),
          f ≫ Dynamic.Affine.parabolicHom χ = B.map j ∧
          IsClosedSubgroup (f ≫ Corepresented.limitGroupHom (Dynamic.Affine.cocharacter χ))

theorem anisotropicGaloisParabolicIntersectionLevi :
    AnisotropicGaloisParabolicIntersectionLeviStatement.{u} := by
  intro k K _ _ _ _ _ _ G _ _ hG hss
  dsimp only
  exact hG.exists_reductive_subgroup_of_parabolic_orbit k K G hss

end Langlands.GroupScheme
