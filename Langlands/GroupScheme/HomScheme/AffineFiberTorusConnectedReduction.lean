import Langlands.GroupScheme.HomScheme.AffineFiberTorusSubgroupReduction
import Langlands.GroupScheme.HomScheme.AffineFiberValuation
import Langlands.GroupScheme.Rational.LeviCentralizerExtension
import Langlands.GroupScheme.Reductive.MonomorphismValuativeReductionProof
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothProof
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonoClosedImmersionProof
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType

/-! # Reduction of affine-fibre torus moduli to geometrically connected fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G H K : GroupScheme S}

/-- Over a locally noetherian base, every monomorphic relative torus map into
a smooth separated quasi-compact group with affine residue fibres is closed. -/
theorem isClosedSubgroup_of_mono_of_affineResidueFibers [IsLocallyNoetherian S]
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasAffineResidueFibers G) (hK : RelativeTorus.IsTorus K) (j : K ⟶ G)
    [Mono j.hom.hom.left] : IsClosedSubgroup j := by
  have : Smooth K.X.hom := hK.smooth
  have : IsAffineHom K.X.hom := hK.isAffineHom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : LocallyOfFiniteType j.hom.hom.left := by
    have : LocallyOfFiniteType (j.hom.hom.left ≫ G.X.hom) := by rw [j.hom.hom.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ G.X.hom
  have : QuasiCompact j.hom.hom.left := by
    have : QuasiCompact (j.hom.hom.left ≫ G.X.hom) := by rw [j.hom.hom.w]; infer_instance
    exact QuasiCompact.of_comp _ G.X.hom
  apply ReductiveMonomorphismValuativeReduction.isClosedImmersion_of_dvr_lifts j.hom.hom.left
  intro sq hsq
  let : IsDiscreteValuationRing sq.R := hsq
  let b := sq.i₂ ≫ G.X.hom
  let G' := (baseChange b).obj G
  let j' := (baseChange b).map j
  have : IsAffineHom G'.X.hom := G.isAffineHom_dvrPullback_of_residueFibers hG b
  have : LocallyOfFinitePresentation G'.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  have : Mono j'.hom.hom.left := (baseChange_map_isPullback b j).flip.mono_snd_of_mono
  have : Mono j'.hom.hom := Over.mono_of_mono_left _
  apply ReductiveMonomorphismValuativeReduction.hasLift_of_baseChange_isClosedImmersion j sq
  exact multiplicativeTypeMonoClosedImmersion _ G' _ j' (hK.baseChange b).isMultiplicativeType inferInstance

/-- Relative torus maps factor through the relative identity component, with
the factorization tested on the literal all-test subgroup ranges. -/
theorem range_le_of_isRelativeIdentityComponent (i : H ⟶ G) (hi : IsRelativeIdentityComponent G i)
    (j : K ⟶ G) (hK : RelativeTorus.IsTorus K) : range j ≤ range i := by
  have hj : InRelativeIdentityComponent G j.hom.hom := by
    intro s
    let b := S.fromSpecResidueField s
    let K' := (baseChange b).obj K
    let G' := (baseChange b).obj G
    let j' := (baseChange b).map j
    have : GeometricallyConnected K.X.hom := hK.geometricallyConnected
    have : ConnectedSpace K'.X.left :=
      (geometrically_iff_of_isClosedUnderIsomorphisms.mp
        (GeometricallyConnected.geometrically_connectedSpace (f := K.X.hom)))
        (S.residueField s) b
    exact IdentityComponent.range_subset_identitySet G' j'.hom.hom η[K'.X]
      (IsMonHom.one_hom j'.hom.hom)
  have hmem : j.hom.hom ∈ (range i).carrier K.X := mem_range.mpr ((hi.factors_iff K.X _).mpr hj)
  intro T z hz
  obtain ⟨a, rfl⟩ := mem_range.mp hz
  exact (range i).comp_mem a hmem

private theorem isUniversal_comp_identityComponent [Smooth G.X.hom]
    (i : H ⟶ G) (hi : IsRelativeIdentityComponent G i) {M : Over S} {T : GroupScheme M.left}
    (j : T ⟶ (baseChange M.hom).obj H) (hu : IsUniversal j) :
    IsUniversal (j ≫ (baseChange M.hom).map i) := by
  intro U F hF
  let r := admissibleRepresentative ⟨F, hF⟩
  let b := (baseChange U.hom).map i
  have hI : IsRelativeIdentityComponent _ b :=
    RelativeIdentityComponent.smoothStructure.2.2 S G inferInstance H i hi U.left U.hom
  have : IsOpenImmersion b.hom.hom.left := hI.isOpenImmersion
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have hle : range r.hom ≤ range b := range_le_of_isRelativeIdentityComponent b hI r.hom r.torus
  let f := rangeFactor r.hom b hle
  have hf := rangeFactor_comp r.hom b hle
  have hfc : IsClosedSubgroup f := by
    have he := congrArg (fun a => a.hom.hom.left) hf
    simp only [Grp.comp_hom_hom, Over.comp_left] at he
    have : IsClosedImmersion (f.hom.hom.left ≫ b.hom.hom.left) := he.symm ▸ r.closed
    exact IsClosedImmersion.of_comp f.hom.hom.left b.hom.hom.left
  have hEval (a : U ⟶ M) : evaluate (j ≫ (baseChange M.hom).map i) a =
      range (familyHom j a ≫ b) := by
    simp only [evaluate, familyHom, Functor.map_comp, Category.assoc]
    rw [Descent.pullbackComparison_naturality M.hom a.left U.hom a.w i]
  have hFb : range (f ≫ b) = F := (congrArg range hf).trans r.represents.2
  obtain ⟨a, ha, huniq⟩ := hu U (range f) (isAdmissible_range f hfc r.torus)
  refine ⟨a, ?_, fun a' ha' => huniq a' ?_⟩
  · change evaluate (j ≫ (baseChange M.hom).map i) a = F
    rw [hEval a, ← hFb]
    exact le_antisymm (range_comp_mono ha.le b) (range_comp_mono ha.ge b)
  · change evaluate (j ≫ (baseChange M.hom).map i) a' = F at ha'
    rw [hEval a', ← hFb] at ha'
    let he := range_comp_le_iff_of_mono (familyHom j a') f b (inferInstance : Mono b.hom.hom)
    let he' := range_comp_le_iff_of_mono f (familyHom j a') b (inferInstance : Mono b.hom.hom)
    exact le_antisymm (he.mp ha'.le) (he'.mp ha'.ge)

/-- Smooth representability over noetherian affine bases restricted to
ambient groups with geometrically connected fibres. -/
def NoetherianAffineConnectedTorusSubgroupRepresentabilityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom], HasAffineResidueFibers G →
    ∃ (M : Over (Spec (CommRingCat.of A))) (T : GroupScheme M.left)
      (j : T ⟶ (baseChange M.hom).obj G),
      IsClosedSubgroup j ∧ RelativeTorus.IsTorus T ∧ IsUniversal j ∧ Smooth M.hom

/-- The identity-component family solves the noetherian affine problem for
all smooth separated quasi-compact groups with affine residue fibres. -/
theorem noetherianAffineTorusSubgroupRepresentability_of_connected
    (h : NoetherianAffineConnectedTorusSubgroupRepresentabilityStatement.{u}) :
    NoetherianAffineTorusSubgroupRepresentabilityStatement.{u} := by
  intro A _ _ G _ _ _ hG
  let B := Spec (CommRingCat.of A)
  obtain ⟨H, i, hi, hH, hconn⟩ := RelativeIdentityComponent.smoothStructure.1 B G inferInstance
  have : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  have : IsSeparated H.X.hom := by rw [← i.hom.hom.w]; infer_instance
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : IsNoetherian G.X.left := {}
  have : NoetherianSpace H.X.left := i.hom.hom.left.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact H.X.hom := inferInstance
  have hAh : HasAffineResidueFibers H := by
    intro s
    have : IsClosedImmersion (((baseChange (B.fromSpecResidueField s)).map i).hom.hom.left) :=
      hi.isClosedImmersion_residueFiber s
    have : IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom := hG s
    rw [← Over.w (((baseChange (B.fromSpecResidueField s)).map i).hom.hom)]
    infer_instance
  obtain ⟨M, T, j, hj, hT, hu, hM⟩ := h A H hAh
  let G' := (baseChange M.hom).obj G
  let i' := (baseChange M.hom).map i
  have : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  have : Smooth G'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsSeparated G'.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : QuasiCompact G'.X.hom := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  have : IsOpenImmersion i'.hom.hom.left := MorphismProperty.of_isPullback
    (RelativeIdentityComponent.overPullback_isPullback M.hom i.hom.hom).flip hi.isOpenImmersion
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono (j ≫ i').hom.hom.left := inferInstanceAs (Mono (j.hom.hom.left ≫ i'.hom.hom.left))
  have hi' := isClosedSubgroup_of_mono_of_affineResidueFibers
    (HasAffineResidueFibers.baseChange hG M.hom) hT (j ≫ i')
  exact ⟨M, T, j ≫ i', hi', hT, isUniversal_comp_identityComponent i hi j hu, hM⟩

end Langlands.GroupScheme.TorusSubgroupModuli
