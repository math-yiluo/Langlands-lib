import Langlands.Geometry.Building.ValuationBuildingDerivedComparison
import Langlands.GroupScheme.Rational.TorusCoverNormalizer
import Langlands.GroupScheme.Rational.CentralQuotientCenter
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.CentralSurjection.TorusImage
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.Geometry.Building.FullValidity.DatumTransport.Building

/-!
# Reduced buildings along a central surjection, through the derived subgroups

Let `f : G → G'` be a flat surjective homomorphism of connected reductive groups over a
nonarchimedean local field, `B` and `B'` valuation-building data of `G` and `G'` whose
maximal split tori correspond, `B.i ≫ f = fS ≫ B'.i` with `fS` flat, surjective and of
finite presentation, and let `fD : D → D'` be a central isogeny of derived subgroups
over `f`, with maximal split tori `T ⊆ D` and `T' ⊆ D'` inside `S` and `S'` corresponding
under an isogeny `t : T → T'`. Then the reduced buildings of `B` and `B'` are identified by
an equivariant building isomorphism along `f`
(`exists_isEquivariantBuildingIso_of_derivedIsogeny`).

The apartment comparison passes through the derived apartment class of `D`: the derived
pullback of the apartment class of `B` and the central-isogeny pullback of the derived
pullback of the apartment class of `B'` agree by KP Proposition 6.2.6. The derived part
`d(N_D(F))` of `N(F)` is handled by the two pullback comparisons. For the centralizer
`Z(F)` of `S`, both actions are translations by `ν` (axiom V 6), and the linear part of the
comparison is the cocharacter map of `fS`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

section CentralizerMap

variable {G G' : GroupScheme (Spec (CommRingCat.of F))}
  {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G'} (f : G ⟶ G') (fS : S ⟶ S')
  [Flat (CommGroupScheme.groupHom fS).hom.hom.left]
  [Surjective (CommGroupScheme.groupHom fS).hom.hom.left]
  (hS : i ≫ f = CommGroupScheme.groupHom fS ≫ i')
  (CS : CentralizerDatum i) (CT : CentralizerDatum i')

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hS in
/-- `f` maps the centralizer of `S` into the centralizer of `S'`. -/
theorem range_centralizer_comp_le_of_flat :
    SubgroupFunctor.range (CS.j ≫ f) ≤ torusCentralizer i' := by
  rintro U _ ⟨z, rfl⟩
  change (z ≫ CS.j.hom.hom) ≫ f.hom.hom ∈ (torusCentralizer i').carrier U
  exact TorusCoverTransport.map_mem_torusCentralizer f fS hS (by
    rw [← CS.isRepresentedBy.2]
    exact ⟨z, rfl⟩)

/-- The centralizer map `Z → Z'` induced by `f`. -/
def centralizerMapOfFlat : CS.Z ⟶ CT.Z :=
  CT.isRepresentedBy.factorHom (CS.j ≫ f) (range_centralizer_comp_le_of_flat f fS hS CS)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem centralizerMapOfFlat_comp :
    centralizerMapOfFlat f fS hS CS CT ≫ CT.j = CS.j ≫ f :=
  CT.isRepresentedBy.factorHom_comp _ _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem centralizerMapOfFlat_torus :
    CS.s ≫ centralizerMapOfFlat f fS hS CS CT = CommGroupScheme.groupHom fS ≫ CT.s := by
  apply CT.isRepresentedBy.hom_ext
  rw [Category.assoc, centralizerMapOfFlat_comp, ← Category.assoc,
    CS.comp_eq, Category.assoc, CT.comp_eq, hS]

/-- The translation vectors `ν` correspond under the cocharacter map of `fS`. -/
theorem centralizerMapOfFlat_translation (z : rationalPoints CS.Z) :
    cocharacterMapReal fS (CS.translation z).toAdd =
      (CT.translation (rationalPoints.map (centralizerMapOfFlat f fS hS CS CT) z)).toAdd :=
  cocharacterMapReal_centralizerTranslation fS CS.s _ CT.s
    (centralizerMapOfFlat_torus f fS hS CS CT) CS.bijective CT.bijective z

end CentralizerMap

/-- **Reduction of the central-surjection comparison to derived data.** Let `f : G → G'` be
flat and surjective, let `B`, `B'` be valuation-building data whose maximal split tori
correspond under `f` through a flat surjection `fS`, and let `fD : D → D'` be a central
isogeny of derived subgroups over `f`, with maximal split tori `j : T → D`, `j' : T' → D'`
inside `S` and `S'` related by an isogeny `t`. Then the reduced buildings of `B` and `B'` are
identified by an equivariant building isomorphism along `f`. -/
theorem exists_isEquivariantBuildingIso_of_derivedIsogeny
    {G G' : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [IsAffineHom G'.X.hom] (f : G ⟶ G') [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    (B : ValuationBuildingData G) (B' : ValuationBuildingData G')
    (fS : B.S ⟶ B'.S) [Flat (CommGroupScheme.groupHom fS).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom fS).hom.hom.left]
    [LocallyOfFinitePresentation (CommGroupScheme.groupHom fS).hom.hom.left]
    (hS : B.i ≫ f = CommGroupScheme.groupHom fS ≫ B'.i)
    {D D' : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom D.X.hom]
    [IsAffineHom D'.X.hom] (d : D ⟶ G) (d' : D' ⟶ G') (hd : IsDerivedSubgroup d)
    (hd' : IsDerivedSubgroup d') (fD : D ⟶ D') (hfD : IsCentralIsogeny fD)
    (hfDd : fD ≫ d' = d ≫ f)
    {T T' : CommGroupScheme (Spec (CommRingCat.of F))}
    (j : T.toGrp ⟶ D) (j' : T'.toGrp ⟶ D') (e : T ⟶ B.S) (e' : T' ⟶ B'.S)
    (hj : IsMaximalSplitTorus j) (hj' : IsMaximalSplitTorus j')
    (he : IsClosedSubgroup (CommGroupScheme.groupHom e))
    (he' : IsClosedSubgroup (CommGroupScheme.groupHom e'))
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ B.i)
    (h' : j' ≫ d' = CommGroupScheme.groupHom e' ≫ B'.i)
    (t : T ⟶ T') (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hjt : j ≫ fD = CommGroupScheme.groupHom t ≫ j') (hte : t ≫ e' = e ≫ fS) :
    ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
      IsEquivariantBuildingIso B B' (rationalPoints.map f) Φ := by
  have hG := B.isConnectedReductive
  have hG' := B'.isConnectedReductive
  have : Smooth G.X.hom := hG.smooth
  have : Smooth G'.X.hom := hG'.smooth
  have hDred : IsConnectedReductive D := hd.isConnectedReductive hG
  have hDred' : IsConnectedReductive D' := hd'.isConnectedReductive hG'
  have : Smooth D.X.hom := hDred.smooth
  have : Smooth D'.X.hom := hDred'.smooth
  have : Mono d.hom.hom.left := by
    have : IsClosedImmersion d.hom.hom.left := hd.1
    infer_instance
  have : Mono d'.hom.hom.left := by
    have : IsClosedImmersion d'.hom.hom.left := hd'.1
    infer_instance
  have : Mono j.hom.hom.left := mono_of_isMaximalSplitTorus hj
  have : Mono j'.hom.hom.left := mono_of_isMaximalSplitTorus hj'
  have hT : IsSplitTorus T.toGrp := hj.1.1
  have hT' : IsSplitTorus T'.toGrp := hj'.1.1
  have hSs : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.1.1
  have hSs' : IsSplitTorus B'.S.toGrp := B'.isMaximalSplitTorus.1.1
  -- Central split components.
  obtain ⟨A, a, ha⟩ := (splitComponentStatement F G hG).1
  obtain ⟨cc, hca, -, -⟩ := ha.exists_commFactor_of_isMaximalSplitTorus B.isMaximalSplitTorus
  have hp : IsCentralIsogeny (RelativeRoot.centralComplementProduct e cc) :=
    derivedCentralSplitTorusProduct F G D d hG hd B.S T A B.i j e a cc
      B.isMaximalSplitTorus hj he h ha hca
  have : Flat (RelativeRoot.centralComplementProduct e cc).hom.hom.left := hp.flat
  have : Surjective (RelativeRoot.centralComplementProduct e cc).hom.hom.left := hp.surjective
  have hA : IsSplitTorus A.toGrp := ha.isCentralSplitTorus.1.1
  have hc : IsCentral (CommGroupScheme.groupHom cc ≫ B.i) := by
    rw [hca]
    exact ha.isCentralSplitTorus.2
  obtain ⟨A', a', ha'⟩ := (splitComponentStatement F G' hG').1
  obtain ⟨cc', hca', -, -⟩ :=
    ha'.exists_commFactor_of_isMaximalSplitTorus B'.isMaximalSplitTorus
  have hp' : IsCentralIsogeny (RelativeRoot.centralComplementProduct e' cc') :=
    derivedCentralSplitTorusProduct F G' D' d' hG' hd' B'.S T' A' B'.i j' e' a' cc'
      B'.isMaximalSplitTorus hj' he' h' ha' hca'
  have : Flat (RelativeRoot.centralComplementProduct e' cc').hom.hom.left := hp'.flat
  have : Surjective (RelativeRoot.centralComplementProduct e' cc').hom.hom.left :=
    hp'.surjective
  have hA' : IsSplitTorus A'.toGrp := ha'.isCentralSplitTorus.1.1
  have hc' : IsCentral (CommGroupScheme.groupHom cc' ≫ B'.i) := by
    rw [hca']
    exact ha'.isCentralSplitTorus.2
  -- The derived apartment classes, identified by KP Proposition 6.2.6.
  let CD := CentralizerDatum.ofValuationComparison Cartan.centralizerValuationComparison
    hDred j hj
  let CD' := CentralizerDatum.ofValuationComparison Cartan.centralizerValuationComparison
    hDred' j' hj'
  let X := B.apartment.derivedPullback e cc j B.i d hd h hT hSs hA hc B.isMaximalSplitTorus
  have hX : X.IsOmegaCompatible CD :=
    B.isOmegaCompatible.derivedPullback e cc j B.i d h hT hA hc CD B.centralizer hd hSs
      B.isMaximalSplitTorus
  let X' := B'.apartment.derivedPullback e' cc' j' B'.i d' hd' h' hT' hSs' hA' hc'
    B'.isMaximalSplitTorus
  have hX' : X'.IsOmegaCompatible CD' :=
    B'.isOmegaCompatible.derivedPullback e' cc' j' B'.i d' h' hT' hA' hc' CD' B'.centralizer
      hd' hSs' B'.isMaximalSplitTorus
  let Y := X'.centralIsogenyPullback fD hfD hT hT' t hjt ht
  have hY : Y.IsOmegaCompatible CD :=
    hX'.centralIsogenyPullback fD t hjt ht CD CD' hfD hT hT'
  have hXY : X = Y := omegaCompatibleApartmentUniqueness F D hDred T j hj CD X Y hX hY
  -- The two comparisons out of the derived class.
  let cd := B.apartment.derivedComparison e cc j B.i d hd h hT hSs hA hc B.isMaximalSplitTorus
  let cY := (X'.centralIsogenyComparison fD hfD hT hT' t hjt ht).trans
    (B'.apartment.derivedComparison e' cc' j' B'.i d' hd' h' hT' hSs' hA' hc'
      B'.isMaximalSplitTorus)
  let cX := cY.congrLeft hXY
  have hcXlin : cX.e.linear = cY.e.linear := cY.congrLeft_linear hXY
  let E : B.Apartment ≃ᵃ[ℝ] B'.Apartment := cd.e.symm.trans cX.e
  have hθ : (rationalPoints.map d').comp (rationalPoints.map fD) =
      (rationalPoints.map f).comp (rationalPoints.map d) := by
    rw [map_comp_rationalPoints, hfDd, map_comp_rationalPoints]
  -- The linear part of `E` is the cocharacter map of `fS`.
  have hlin : ∀ w : V B.S, E.linear (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (cocharacterMapReal fS w) := by
    intro w
    obtain ⟨v, z0, rfl⟩ :=
      exists_eq_cocharacterMapReal_add_of_centralComplement e cc hT hA hSs w
    have hz1 : cocharacterMapReal cc z0 ∈ rootAnnihilator B.i := by
      rw [mem_rootAnnihilator]
      intro b hb
      rw [eval_cocharacterMapReal, root_restrict_eq_zero_of_isCentral B.i cc hA hc hb,
        eval_zero_char]
    have hcc : IsCentral (CommGroupScheme.groupHom (cc ≫ fS) ≫ B'.i) := by
      have hcf := hc.comp_flat_surjective f
      rw [Category.assoc, hS, ← Category.assoc] at hcf
      exact hcf
    have hz2 : cocharacterMapReal fS (cocharacterMapReal cc z0) ∈ rootAnnihilator B'.i := by
      rw [← LinearMap.comp_apply, ← cocharacterMapReal_comp, mem_rootAnnihilator]
      intro b hb
      rw [eval_cocharacterMapReal,
        root_restrict_eq_zero_of_isCentral B'.i (cc ≫ fS) hA hcc hb, eval_zero_char]
    rw [map_add, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero _).mpr hz1, (Submodule.Quotient.mk_eq_zero _).mpr hz2,
      add_zero, add_zero]
    have h1 : cd.e.linear (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (cocharacterMapReal e v) := rfl
    have h2 : cY.e.linear (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (cocharacterMapReal e' (cocharacterMapReal t v)) := rfl
    change cX.e.linear (cd.e.symm.linear (Submodule.Quotient.mk (cocharacterMapReal e v))) = _
    rw [AffineEquiv.linear_symm, ← h1, LinearEquiv.symm_apply_apply, hcXlin, h2,
      ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← cocharacterMapReal_comp,
      ← cocharacterMapReal_comp, hte]
  let tr : B.apartment.Transfer B'.apartment (rationalPoints.map f) :=
    { e := E
      map_mem_normalizerPoints := fun n =>
        (TorusCoverTransport.normalizerPointsMap f fS hS n).2
      e_smul := fun n x => by
        obtain ⟨C, π, hπ⟩ :=
          simplyConnectedCoverExistence F D (derivedSubgroupSemisimple F G D d hG hd)
        obtain ⟨cpt, z, hz⟩ := simplyConnectedCentralizerProduct F B.S G B.centralizer.Z C D
          B.i B.centralizer.j d π ⟨hG, hd, hπ⟩ B.isMaximalSplitTorus
          B.centralizer.isRepresentedBy n.val
        have hzN : (B.centralizer.toNormalizer z : rationalPoints G) =
            rationalPoints.map B.centralizer.j z := rfl
        have hmd : rationalPoints.map d (rationalPoints.map π cpt) =
            (n : rationalPoints G) * (B.centralizer.toNormalizer z : rationalPoints G)⁻¹ := by
          rw [hzN, hz, mul_inv_cancel_right, ← map_comp_rationalPoints]
          rfl
        have hmN : rationalPoints.map π cpt ∈ normalizerPoints j :=
          DerivedCoverNormalizerLift.mem_normalizerPoints (𝟙 D) d
            (isCentralIsogeny_of_isIso _) j hj B.i e (by rw [Category.id_comp]; exact h) _
            (by
              rw [Category.id_comp, hmd]
              exact mul_mem n.2 (inv_mem (B.centralizer.toNormalizer z).2))
        let mN : normalizerPoints j := ⟨_, hmN⟩
        have hn : n = ⟨rationalPoints.map d (mN : rationalPoints D),
            cd.map_mem_normalizerPoints mN⟩ * B.centralizer.toNormalizer z := by
          apply Subtype.ext
          change (n : rationalPoints G) = rationalPoints.map d (rationalPoints.map π cpt) *
            (B.centralizer.toNormalizer z : rationalPoints G)
          rw [hmd, inv_mul_cancel_right]
        have e1 : ((rationalPoints.map d').comp (rationalPoints.map fD))
            (mN : rationalPoints D) =
            rationalPoints.map f (rationalPoints.map d (mN : rationalPoints D)) := by
          rw [hθ]
          rfl
        have e2 : rationalPoints.map B'.centralizer.j (rationalPoints.map
            (centralizerMapOfFlat f fS hS B.centralizer B'.centralizer) z) =
            rationalPoints.map f (rationalPoints.map B.centralizer.j z) := by
          rw [← MonoidHom.comp_apply, map_comp_rationalPoints, centralizerMapOfFlat_comp,
            ← map_comp_rationalPoints]
          rfl
        have hfn : (⟨rationalPoints.map f n, (TorusCoverTransport.normalizerPointsMap f fS hS
            n).2⟩ : normalizerPoints B'.i) =
            ⟨((rationalPoints.map d').comp (rationalPoints.map fD)) (mN : rationalPoints D),
              cX.map_mem_normalizerPoints mN⟩ *
              B'.centralizer.toNormalizer (rationalPoints.map
                (centralizerMapOfFlat f fS hS B.centralizer B'.centralizer) z) := by
          apply Subtype.ext
          change rationalPoints.map f n =
            ((rationalPoints.map d').comp (rationalPoints.map fD)) (mN : rationalPoints D) *
              rationalPoints.map B'.centralizer.j (rationalPoints.map
                (centralizerMapOfFlat f fS hS B.centralizer B'.centralizer) z)
          rw [e1, e2, ← map_mul]
          congr 1
        rw [hfn]
        conv_lhs => rw [hn]
        rw [mul_smul, mul_smul]
        have hstep : ∀ w : B.Apartment,
            E ((⟨rationalPoints.map d (mN : rationalPoints D),
              cd.map_mem_normalizerPoints mN⟩ : normalizerPoints B.i) • w) =
            (⟨((rationalPoints.map d').comp (rationalPoints.map fD)) (mN : rationalPoints D),
              cX.map_mem_normalizerPoints mN⟩ : normalizerPoints B'.i) • E w := by
          intro w
          change cX.e (cd.e.symm (_ • w)) = _ • cX.e (cd.e.symm w)
          rw [cd.e_symm_smul mN w, cX.e_smul]
        rw [hstep]
        congr 1
        rw [B.isOmegaCompatible.smul_eq_vadd, B'.isOmegaCompatible.smul_eq_vadd,
          AffineEquiv.map_vadd, hlin, centralizerMapOfFlat_translation]
      map_sharpFixer := fun x => by
        obtain ⟨y, rfl⟩ := cd.e.surjective x
        have hE : E (cd.e y) = cX.e y := by
          change cX.e (cd.e.symm (cd.e y)) = _
          rw [AffineEquiv.symm_apply_apply]
        rw [hE, ← cd.map_sharpFixer y, Subgroup.map_map, ← cX.map_sharpFixer y, hθ]
      mem_normalizerPoints_of_map := fun g hg => by
        obtain ⟨C, π, hπ⟩ :=
          simplyConnectedCoverExistence F D (derivedSubgroupSemisimple F G D d hG hd)
        obtain ⟨cpt, n0, hn0⟩ := exists_eq_map_mul_normalizer B d π ⟨hG, hd, hπ⟩ g
        have hgm : g = rationalPoints.map d (rationalPoints.map π cpt) * n0 := by
          rw [hn0, ← map_comp_rationalPoints]
          rfl
        have hn0' : rationalPoints.map f (n0 : rationalPoints G) ∈ normalizerPoints B'.i :=
          (TorusCoverTransport.normalizerPointsMap f fS hS n0).2
        have hfm : rationalPoints.map (fD ≫ d') (rationalPoints.map π cpt) ∈
            normalizerPoints B'.i := by
          have hmem := mul_mem hg (inv_mem hn0')
          rw [hgm, map_mul, mul_inv_cancel_right] at hmem
          rw [hfDd, ← map_comp_rationalPoints]
          exact hmem
        have hjtS : j ≫ fD ≫ d' = CommGroupScheme.groupHom (t ≫ e') ≫ B'.i := by
          rw [← Category.assoc, hjt, Category.assoc, h']
          rfl
        have hm := DerivedCoverNormalizerLift.mem_normalizerPoints fD d' hfD j hj B'.i
          (t ≫ e') hjtS _ hfm
        rw [hgm]
        exact mul_mem (cd.map_mem_normalizerPoints ⟨_, hm⟩) n0.2
      exists_mul := fun g' => by
        have hDss' := derivedSubgroupSemisimple F G' D' d' hG' hd'
        obtain ⟨C', π', hπ'⟩ := simplyConnectedCoverExistence F D' hDss'
        obtain ⟨cpt, n', hn'⟩ := exists_eq_map_mul_normalizer B' d' π' ⟨hG', hd', hπ'⟩ g'
        obtain ⟨lift, hlift, -⟩ :=
          hπ'.universal D fD (derivedSubgroupSemisimple F G D d hG hd) hfD
        refine ⟨rationalPoints.map d (rationalPoints.map lift cpt), n', ?_⟩
        rw [hn', ← hlift, Category.assoc, hfDd, ← map_comp_rationalPoints,
          ← map_comp_rationalPoints]
        rfl
      transportedRoots_eq := by
        change AffineRootSystem.transportedRoots (cd.e.symm.trans cX.e) B.apartment.affineRoots =
          B'.apartment.affineRoots
        rw [AffineRootSystem.transportedRoots_trans, ← cd.transportedRoots_eq,
          AffineRootSystem.transportedRoots_symm, cX.transportedRoots_eq] }
  exact ⟨tr.reducedBuildingEquiv, Transfer.isEquivariantBuildingIso tr⟩

/-- **The central-surjection comparison.** For a surjective homomorphism `f : G → G'` with
central kernel, any valuation-building data `B` of `G` and `B'` of `G'` have reduced buildings
identified by an equivariant building isomorphism along `f`. -/
theorem exists_isEquivariantBuildingIso_centralSurjection
    {G G' : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [IsAffineHom G'.X.hom] (f : G ⟶ G') (hf : IsCentralSurjection f)
    (B : ValuationBuildingData G) (B' : ValuationBuildingData G') :
    ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
      IsEquivariantBuildingIso B B' (rationalPoints.map f) Φ := by
  have hG := B.isConnectedReductive
  have hG' := B'.isConnectedReductive
  have : Smooth G.X.hom := hG.smooth
  have : Smooth G'.X.hom := hG'.smooth
  have : Surjective f.hom.hom.left := hf.surjective
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ G'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left G'.X.hom
  have : Flat f.hom.hom.left := flat_of_surjective f
  obtain ⟨S', i', fS, hi', hfS, hflat, hsurj, hlfp⟩ :=
    exists_maximalSplitTorus_image hG hG' f hf.isCentral_kernelι B.isMaximalSplitTorus
  -- Move `B'` to the image torus `i'` by an inner automorphism.
  obtain ⟨g, σ₀, hσ₀⟩ := (maximalSplitTorusConjugacy F G' hG').1
    B'.S S' B'.i i' B'.isMaximalSplitTorus hi'
  let σ : B'.S ≅ S' :=
    { hom := Additive.ofMul σ₀.hom
      inv := Additive.ofMul σ₀.inv
      hom_inv_id := congrArg Additive.ofMul σ₀.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul σ₀.inv_hom_id }
  have hσ : B'.i ≫ (G'.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i' := hσ₀
  let B'' := B'.basedTransport σ (G'.innerIso g) hσ
  suffices hB'' : ∃ Φ : B.ReducedBuilding ≃ B''.ReducedBuilding,
      IsEquivariantBuildingIso B B'' (rationalPoints.map f) Φ by
    obtain ⟨Φ, hΦ⟩ := hB''
    exact hΦ.exists_retarget
  -- Derived subgroups, their maximal split tori, and the isogeny between them.
  obtain ⟨D, d, _, _, hd⟩ := derivedSubgroupRepresentability F G
  obtain ⟨D', d', _, _, hd'⟩ := derivedSubgroupRepresentability F G'
  obtain ⟨T, j, e, hj, he, h⟩ :=
    derivedMaximalSplitTorus F G D d hG hd B.S B.i B.isMaximalSplitTorus
  obtain ⟨T', j', e', hj', he', h'⟩ := derivedMaximalSplitTorus F G' D' d' hG' hd' S' i' hi'
  obtain ⟨t, hjt, hte, ht⟩ := exists_derivedTorus_isogeny hG hG' hd hd' f
    hf.isCentral_kernelι hi'.1 hfS hj hj' h h'
  exact exists_isEquivariantBuildingIso_of_derivedIsogeny f B B'' fS hfS d d' hd hd'
    (hd.map hd' f) (hd.isCentralIsogeny_map hd' f hG hG' hf.isCentral_kernelι)
    (IsDerivedSubgroup.map_comp hd hd' f) j j' e e' hj hj' he he' h h' t ht hjt hte

end Langlands.Geometry.Building.ValuationBuildingData
