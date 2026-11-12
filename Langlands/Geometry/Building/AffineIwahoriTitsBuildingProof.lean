import Langlands.Geometry.Building.AffineIwahoriTitsBuildingStatement
import Langlands.Geometry.Building.TitsNormalizerApartmentStabilizer
import Langlands.Geometry.Building.BuildingFacetIncidence
import Langlands.Geometry.Building.AffineChamberFaceExistence
import Langlands.Geometry.Building.AffineWeylFacetFixing
import Langlands.Geometry.Building.AffineFacetParabolic
import Langlands.Geometry.Building.AffineSimpleFixedAdmissible
import Langlands.Geometry.Building.AffineChamberSimpleCone
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.Geometry.Building.ChamberIwahoriCompactOpenProof
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Group.TitsApartmentComparison
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof

/-! # The actual affine Iwahori–Tits system is the building Tits system -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.Group.RelativeWeyl Langlands.BruhatTits.IntegralModels

namespace Langlands.Group.TitsSystem

variable {W W' : Type*} [Group W] [Group W']

/-- A multiplicative equivalence carries irreducible components of `S` back to irreducible
components of its preimage. -/
theorem sameComponent_preimage (e : W ≃* W') {S : Set W'} {s t : W'}
    (h : SameComponent S s t) : SameComponent (e ⁻¹' S) (e.symm s) (e.symm t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨by simpa using hbc.1, by simpa using hbc.2.1, fun h => hbc.2.2 ?_⟩
    simpa using congrArg e h

/-- Admissible types are carried back along a multiplicative equivalence. -/
theorem isAdmissibleType_preimage (e : W ≃* W') {S X : Set W'}
    (h : IsAdmissibleType S X) : IsAdmissibleType (e ⁻¹' S) (e ⁻¹' X) := by
  refine ⟨Set.preimage_mono h.1, fun s hs => ?_⟩
  obtain ⟨t, ht, hst, htX⟩ := h.2 (e s) hs
  refine ⟨e.symm t, by simpa using ht, ?_, by simpa using htX⟩
  simpa using sameComponent_preimage e hst

end Langlands.Group.TitsSystem

namespace Langlands.Geometry.Building.ParahoricBuildingData

open AffineRootSystem AffineRootSystem.GalleryGeometry

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G}

/-! ### Points of the closed chamber and the generated full parahoric -/

/-- The generated full parahoric of the chamber of `c` fixes the image of every point of the
closure of that chamber. -/
theorem parahoric_le_fixer_of_mem_facetClosure
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c y : P.Apartment} (hy : y ∈ facetClosure P.affineRoots c) :
    P.parahoric (facet P.affineRoots c) ≤ P.fixer (P.apartmentMap y) := by
  refine sup_le ((P.map_centralizerZero_le_compactStabilizer y).trans
    (P.compactStabilizer_le_fixer _)) ?_
  exact ((P.apartment.sharpFixer_anti
    (Set.singleton_subset_iff.2 (mem_facet_self P.affineRoots c))).trans
    (P.apartment.sharpFixer_singleton_le_of_mem_facetClosure hD.mem_or_two_smul_mem hy)).trans
    (P.sharpFixer_le_fixer y)

/-- An element fixing every image point of `Fa` stabilizes the image of `Fa`. -/
theorem smul_image_apartmentMap_eq {g : rationalPoints G} {Fa : Set P.Apartment}
    (hg : ∀ y ∈ Fa, g • P.apartmentMap y = P.apartmentMap y) :
    g • (P.apartmentMap '' Fa) = P.apartmentMap '' Fa := by
  rw [← Set.image_smul, Set.image_image]
  exact Set.image_congr hg

/-- `N(F)` acts on images of apartment subsets through its action on the apartment. -/
theorem normalizer_smul_image_apartmentMap (m : normalizerPoints P.i) (Fa : Set P.Apartment) :
    (m : rationalPoints G) • (P.apartmentMap '' Fa) = P.apartmentMap '' (m • Fa) := by
  rw [← Set.image_smul, Set.image_image, ← Set.image_smul, Set.image_image]
  exact Set.image_congr fun y _ => P.normalizer_smul_apartmentMap m y

/-- Stabilizers in `G(F)^0` are conjugated by translation. -/
theorem zeroStabilizerIn_smul (k : P.zeroSubgroup) (Y : Set P.ReducedBuilding) :
    P.zeroStabilizerIn ((k : rationalPoints G) • Y) =
      conjugateSubgroup k (P.zeroStabilizerIn Y) := by
  change MulAction.stabilizer P.zeroSubgroup (k • Y) =
    (MulAction.stabilizer P.zeroSubgroup Y).map (MulAut.conj k).toMonoidHom
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj k Y

/-! ### The normalizer representatives of the affine part -/

/-- The point of `N(F)` underlying an element of `N(F) ∩ G(F)^0`. -/
def normalizerInZeroPoint (n : P.normalizerInZero) : normalizerPoints P.i :=
  (P.normalizerInZeroEquiv n : normalizerPoints P.i)

@[simp] theorem coe_normalizerInZeroPoint (n : P.normalizerInZero) :
    ((normalizerInZeroPoint n : normalizerPoints P.i) : rationalPoints G) =
      ((n : P.zeroSubgroup) : rationalPoints G) :=
  rfl

variable [P.normalizerZero.Normal]

/-- Under the affine Weyl comparison of `AffineIwahoriTitsWith`, the transported image of a
representative acts on the apartment as the representative itself. -/
theorem affineTitsProjection_apply {C : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith C e) (n : P.normalizerInZero) (x : P.Apartment) :
    (e (P.affineTitsProjection n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) x =
      normalizerInZeroPoint n • x := by
  rw [← P.apartment.normalizerAffineEquiv_apply]
  exact congrArg (fun f : P.Apartment ≃ᵃ[ℝ] P.Apartment => f x)
    (hW.action_compatible (P.normalizerInZeroEquiv n))

theorem image_affineTitsProjection {C : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith C e) (n : P.normalizerInZero) (Fa : Set P.Apartment) :
    (e (P.affineTitsProjection n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' Fa =
      normalizerInZeroPoint n • Fa := by
  rw [← Set.image_smul]
  exact Set.image_congr fun x _ => affineTitsProjection_apply hW n x


/-! ### Stabilizers of the faces of the chamber -/

/-- A representative of `N(F) ∩ G(F)^0` stabilizes the image in `B(G)` of a facet of the
apartment exactly when its affine Weyl image fixes that facet pointwise. -/
theorem smul_image_facet_eq_iff
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith C e) (n : P.normalizerInZero) (x : P.Apartment) :
    ((n : P.zeroSubgroup) : rationalPoints G) • (P.apartmentMap '' facet P.affineRoots x) =
        P.apartmentMap '' facet P.affineRoots x ↔
      ∀ y ∈ facet P.affineRoots x,
        (e (P.affineTitsProjection n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) y = y := by
  rw [← coe_normalizerInZeroPoint, normalizer_smul_image_apartmentMap,
    (P.apartmentMap_injective_of_rankOne hD
      P.hasRankOneFactorization_actual).image_injective.eq_iff,
    ← image_affineTitsProjection hW]
  constructor
  · exact affineWeyl_facet_fixing
      hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
      (isFacet_facet _ x) _
  · intro h
    rw [Set.image_congr h, Set.image_id']

omit [P.normalizerZero.Normal] in
/-- The generated full parahoric of the chamber of `c` stabilizes the image of the facet of
every point of the closed chamber. -/
theorem parahoricInZero_le_zeroStabilizerIn
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c x : P.Apartment} (hx : x ∈ facetClosure P.affineRoots c) :
    P.parahoricInZero (facet P.affineRoots c) ≤
      P.zeroStabilizerIn (P.apartmentMap '' facet P.affineRoots x) := by
  intro b hb
  refine P.mem_zeroStabilizerIn.2 (smul_image_apartmentMap_eq fun y hy => ?_)
  exact P.mem_fixer.1 (parahoric_le_fixer_of_mem_facetClosure hD
    (mem_facetClosure_trans hx (facet_subset_facetClosure _ x hy)) (Subgroup.mem_subgroupOf.1 hb))

/-- KP Proposition 7.6.3 for the faces of the chamber: the stabilizer in `G(F)^0` of the image
of the facet of a point `x` of the closed chamber of `c` is the standard parabolic subset
`B ⟨X⟩ B` of the Iwahori–Tits system, for `X` the simple reflections fixing that facet. -/
theorem coe_zeroStabilizerIn_facet
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e)
    {x : P.Apartment} (hx : x ∈ facetClosure P.affineRoots c) :
    (P.zeroStabilizerIn (P.apartmentMap '' facet P.affineRoots x) : Set P.zeroSubgroup) =
      standardParabolic (P.parahoricInZero (facet P.affineRoots c)) P.affineTitsProjection
        (P.facetSimpleInAffinePart e (facet P.affineRoots c) (facet P.affineRoots x)) := by
  have hB := parahoricInZero_le_zeroStabilizerIn hD hx
  refine hW.tits.coe_eq_standardParabolic hB (fun n hn => ?_) (fun v hv => ?_)
  · refine Subgroup.closure_mono ?_
      (hW.tits.mem_closure_of_mem _ hB (P.affineTitsProjection n) n rfl hn)
    rintro s ⟨hs, m, rfl, hm⟩
    have hfix := (smul_image_facet_eq_iff hD hW m x).1 (P.mem_zeroStabilizerIn.1 hm)
    change e (P.affineTitsProjection m) ∈ facetSimpleReflections _ _ _
    rw [facetSimpleReflections_facet_eq]
    exact ⟨hs, hfix x (mem_facet_self _ x)⟩
  · refine exists_rep_mem_of_mem_closure (fun s hs => ?_) hv
    obtain ⟨n, rfl⟩ := hW.tits.surjective s
    refine ⟨n, rfl, P.mem_zeroStabilizerIn.2
      ((smul_image_facet_eq_iff hD hW n x).2 fun y hy => ?_)⟩
    have hs' : e (P.affineTitsProjection n) ∈
        facetSimpleReflections P.affineRoots (facet P.affineRoots c) (facet P.affineRoots y) := by
      rw [facet_eq_of_mem hy]
      exact hs
    rw [facetSimpleReflections_facet_eq] at hs'
    exact hs'.2

/-- No simple reflection of a chamber fixes its regular point. -/
theorem facetSimpleInAffinePart_self_eq_empty {c : P.Apartment}
    (hc : IsRegular P.affineRoots c) (e : P.affinePart ≃* affineWeylGroup P.affineRoots) :
    P.facetSimpleInAffinePart e (facet P.affineRoots c) (facet P.affineRoots c) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun s hs => ?_
  change e s ∈ facetSimpleReflections _ _ _ at hs
  rw [facetSimpleReflections_facet_eq] at hs
  obtain ⟨⟨ψ, hψ, v, hv, hs'⟩, hfix⟩ := hs
  rw [hs', affineReflection_apply_eq_self_iff] at hfix
  exact hc ψ (simpleAffineRoots_subset _ _ hψ) hfix

/-- The Iwahori subgroup of KP Axiom 4.1.9 is the Borel subgroup of the actual affine
Iwahori–Tits system: `G(F)^0_C = P_C ∩ G(F)^0`. -/
theorem chamberZeroStabilizerIn_eq_parahoricInZero
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e) :
    P.chamberZeroStabilizerIn (facet P.affineRoots c) =
      P.parahoricInZero (facet P.affineRoots c) := by
  apply SetLike.coe_injective
  rw [chamberZeroStabilizerIn, coe_zeroStabilizerIn_facet hD hW (mem_facetClosure_self _ c),
    facetSimpleInAffinePart_self_eq_empty hc, hW.tits.standardParabolic_empty]

/-- The stabilizer in `G(F)^0` of the image of the facet of a point of the closed chamber is
the standard parabolic subgroup `B ⟨X⟩ B` of its facet-simple reflections. -/
theorem zeroStabilizerIn_facet_eq
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e)
    {x : P.Apartment} (hx : x ∈ facetClosure P.affineRoots c) :
    P.zeroStabilizerIn (P.apartmentMap '' facet P.affineRoots x) =
      hW.tits.standardParabolicSubgroup
        (P.facetSimpleInAffinePart_subset e (facet P.affineRoots c) (facet P.affineRoots x)) :=
  SetLike.coe_injective (coe_zeroStabilizerIn_facet hD hW hx)

/-- The facet-simple reflections of every facet form an admissible type. -/
theorem isAdmissibleType_facetSimpleInAffinePart
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    (e : P.affinePart ≃* affineWeylGroup P.affineRoots) (x : P.Apartment) :
    IsAdmissibleType (P.chamberSimpleInAffinePart e (facet P.affineRoots c))
      (P.facetSimpleInAffinePart e (facet P.affineRoots c) (facet P.affineRoots x)) :=
  isAdmissibleType_preimage e
    (hD.isAffineRootSystem_affineRoots.isAdmissibleType_facetSimpleReflections ⟨c, hc, rfl⟩
      (isFacet_facet _ x))

/-- Every admissible type is the type of a face of the chamber of `c`. -/
theorem exists_facetSimpleInAffinePart_eq
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    (e : P.affinePart ≃* affineWeylGroup P.affineRoots) {X : Set P.affinePart}
    (hX : IsAdmissibleType (P.chamberSimpleInAffinePart e (facet P.affineRoots c)) X) :
    ∃ x ∈ facetClosure P.affineRoots c,
      P.facetSimpleInAffinePart e (facet P.affineRoots c) (facet P.affineRoots x) = X := by
  have hS : e.symm ⁻¹' P.chamberSimpleInAffinePart e (facet P.affineRoots c) =
      chamberSimpleReflections P.affineRoots (facet P.affineRoots c) := by
    ext s
    simp [chamberSimpleInAffinePart]
  have hX' := isAdmissibleType_preimage e.symm hX
  rw [hS] at hX'
  obtain ⟨Fa, hFa, hFaX⟩ :=
    hD.isAffineRootSystem_affineRoots.exists_isFaceOf_facetSimpleReflections_eq hc hX'
  obtain ⟨x, hx, rfl⟩ := IsAffineRootSystemWithRankZero.exists_eq_facet_of_isFaceOf hFa
  refine ⟨x, hx, ?_⟩
  rw [facetSimpleInAffinePart, hFaX]
  ext s
  simp

/-! ### Every facet of `B(G)` is a `G(F)^0`-translate of a face of the chamber -/

/-- Every facet of the apartment is the translate, by a representative in `N(F) ∩ G(F)^0`, of
a face of the chamber of `c`. -/
theorem exists_normalizerInZero_smul_facet
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e) (y : P.Apartment) :
    ∃ (n : P.normalizerInZero) (x : P.Apartment), x ∈ facetClosure P.affineRoots c ∧
      facet P.affineRoots y = normalizerInZeroPoint n • facet P.affineRoots x := by
  have hΨ := hD.isAffineRootSystem_affineRoots
  obtain ⟨d, hd, hyd⟩ := hΨ.isLocallyFiniteReflectionArrangement.exists_regularPoint_closure y
  obtain ⟨w, hw, -⟩ := affineChamberSimpleTransitivity _ _ _ hΨ _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  obtain ⟨n, hn⟩ := hW.tits.surjective (e.symm w)
  have hnC : normalizerInZeroPoint n • facet P.affineRoots c = facet P.affineRoots d := by
    rw [← image_affineTitsProjection hW, hn, MulEquiv.apply_symm_apply, hw]
  have hface : IsFaceOf P.affineRoots (facet P.affineRoots y)
      (normalizerInZeroPoint n • facet P.affineRoots c) := by
    rw [hnC]
    exact IsAffineRootSystemWithRankZero.isFaceOf_facet_of_mem_facetClosure hyd
  have hface' := P.normalizer_smul_isFaceOf hD hface (normalizerInZeroPoint n)⁻¹
  rw [inv_smul_smul] at hface'
  obtain ⟨x, hx, hxeq⟩ := IsAffineRootSystemWithRankZero.exists_eq_facet_of_isFaceOf hface'
  refine ⟨n, x, hx, ?_⟩
  rw [← hxeq, smul_inv_smul]

/-- Every facet of `B(G)` is the `G(F)^0`-translate of the image of a face of the chamber of
`c`, using `G(F) = G(F)^0 N(F)` (KP Fact 2.6.22). -/
theorem exists_eq_zero_smul_facet
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e)
    (Fc : BuildingFacet P.toValuationBuildingData) :
    ∃ (k : P.zeroSubgroup) (x : P.Apartment), x ∈ facetClosure P.affineRoots c ∧
      Fc.val = (k : rationalPoints G) • (P.apartmentMap '' facet P.affineRoots x) := by
  obtain ⟨g, Fa, hFa, hFc⟩ := Fc.property
  obtain ⟨k, hk, m, hm, rfl⟩ :=
    exists_zero_mul_normalizer (P := P) simplyConnectedCentralizerProduct g
  obtain ⟨y, hy⟩ := P.normalizer_smul_isFacet hD hFa ⟨m, hm⟩
  obtain ⟨n, x, hx, hyx⟩ := exists_normalizerInZero_smul_facet hD hc hW y
  have h1 : ((n : P.zeroSubgroup) : rationalPoints G) •
      (P.apartmentMap '' facet P.affineRoots x) = m • (P.apartmentMap '' Fa) := by
    rw [← coe_normalizerInZeroPoint, normalizer_smul_image_apartmentMap, ← hyx, hy]
    exact (normalizer_smul_image_apartmentMap ⟨m, hm⟩ Fa).symm
  refine ⟨⟨k, hk⟩ * (n : P.zeroSubgroup), x, hx, ?_⟩
  rw [hFc, Subgroup.coe_mul, mul_smul, h1, ← mul_smul, ← Set.image_smul, Set.image_image]

/-- The stabilizer of a translate of the image of a face of the chamber is the corresponding
conjugate of a standard parabolic subgroup. -/
theorem facetZeroStabilizer_eq_conjugate
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e)
    {Fc : BuildingFacet P.toValuationBuildingData} {k : P.zeroSubgroup} {x : P.Apartment}
    (hFc : Fc.val = (k : rationalPoints G) • (P.apartmentMap '' facet P.affineRoots x))
    (hx : x ∈ facetClosure P.affineRoots c) :
    P.facetZeroStabilizer Fc = conjugateSubgroup k (hW.tits.standardParabolicSubgroup
      (P.facetSimpleInAffinePart_subset e (facet P.affineRoots c) (facet P.affineRoots x))) := by
  change P.zeroStabilizerIn Fc.val = _
  rw [hFc, zeroStabilizerIn_smul, zeroStabilizerIn_facet_eq hD hW hx]

omit [P.normalizerZero.Normal] in
/-- A translate of the image of a subset of the apartment is its image in the translated
chart. -/
theorem smul_image_apartmentMap (g : rationalPoints G) (Y : Set P.Apartment) :
    g • (P.apartmentMap '' Y) = P.translatedApartmentMap g '' Y := by
  rw [← Set.image_smul, Set.image_image]
  rfl

/-! ### The three comparisons of KP Axiom 4.1.9 -/

/-- KP Proposition 7.6.3 and Remark 7.6.5: `F ↦ G(F)^0_F` is a bijection from the facets of
`B(G)` onto the admissible parabolic subgroups of the actual affine Iwahori–Tits system. -/
theorem bijOn_facetZeroStabilizer_of_affineIwahoriTitsWith
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e) :
    Set.BijOn P.facetZeroStabilizer Set.univ
      {Q | IsAdmissibleParabolic (P.parahoricInZero (facet P.affineRoots c))
        P.affineTitsProjection (P.chamberSimpleInAffinePart e (facet P.affineRoots c)) Q} := by
  have hΨ := hD.isAffineRootSystem_affineRoots
  refine ⟨fun Fc _ => ?_, fun Fc₁ _ Fc₂ _ heq => ?_, fun Q hQ => ?_⟩
  · obtain ⟨k, x, hx, hFc⟩ := exists_eq_zero_smul_facet hD hc hW Fc
    exact ⟨k, _, isAdmissibleType_facetSimpleInAffinePart hD hc e x, by
      rw [facetZeroStabilizer_eq_conjugate hD hW hFc hx]; rfl⟩
  · obtain ⟨k₁, x₁, hx₁, h₁⟩ := exists_eq_zero_smul_facet hD hc hW Fc₁
    obtain ⟨k₂, x₂, hx₂, h₂⟩ := exists_eq_zero_smul_facet hD hc hW Fc₂
    rw [facetZeroStabilizer_eq_conjugate hD hW h₁ hx₁,
      facetZeroStabilizer_eq_conjugate hD hW h₂ hx₂] at heq
    have hfacet : facet P.affineRoots x₁ = facet P.affineRoots x₂ :=
      (hΨ.bijOn_facetSimpleReflections hc).injOn
        (IsAffineRootSystemWithRankZero.isFaceOf_facet_of_mem_facetClosure hx₁)
        (IsAffineRootSystemWithRankZero.isFaceOf_facet_of_mem_facetClosure hx₂)
        (Set.preimage_injective.mpr e.surjective
          (hW.tits.eq_of_conjugateSubgroup_eq _ _ _ _ heq))
    rw [← hfacet] at h₂ heq
    have hmem := hW.tits.mem_of_eq_conjugate (hW.tits.le_of_coe_eq rfl)
      (hW.tits.le_of_coe_eq rfl) (g := k₂⁻¹ * k₁) (by
        rw [conjugateSubgroup_mul, heq, ← conjugateSubgroup_mul, inv_mul_cancel,
          conjugateSubgroup_one])
    rw [← zeroStabilizerIn_facet_eq hD hW hx₁, mem_zeroStabilizerIn] at hmem
    have h := congrArg ((k₂ : rationalPoints G) • ·) hmem
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_smul, smul_inv_smul] at h
    exact Subtype.ext (h₁.trans (h.trans h₂.symm))
  · obtain ⟨g, X, hX, hQ⟩ := hQ
    obtain ⟨x, hx, rfl⟩ := exists_facetSimpleInAffinePart_eq hD hc e hX
    refine ⟨P.zeroFacetTranslate g (chamberFacet (isFacet_facet _ x)), Set.mem_univ _, ?_⟩
    apply SetLike.coe_injective
    rw [facetZeroStabilizer_eq_conjugate hD hW
      (Fc := P.zeroFacetTranslate g (chamberFacet (isFacet_facet _ x))) rfl hx, hQ]
    rfl

/-- KP Proposition 7.6.4(1): the face relation of `B(G)` is reverse inclusion of the stabilizers
in `G(F)^0`. -/
theorem facetPrecedes_iff_of_affineIwahoriTitsWith
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e)
    (Fc Fc' : BuildingFacet P.toValuationBuildingData) :
    FacetPrecedes P.toValuationBuildingData Fc Fc' ↔
      P.facetZeroStabilizer Fc' ≤ P.facetZeroStabilizer Fc := by
  have hΨ := hD.isAffineRootSystem_affineRoots
  have hinj := P.apartmentMap_injective_of_rankOne hD P.hasRankOneFactorization_actual
  obtain ⟨k', x', hx', h'⟩ := exists_eq_zero_smul_facet hD hc hW Fc'
  rw [facetZeroStabilizer_eq_conjugate hD hW h' hx']
  constructor
  · intro hprec
    have hsub : Fc'.val ⊆ (k' : rationalPoints G) • P.apartmentImage := by
      rw [h']
      exact Set.smul_set_mono (Set.image_subset_range _ _)
    obtain ⟨Fa, Ca, hFaCa, hFa, hCa⟩ :=
      P.exists_apartment_faces_of_facetPrecedes hD hprec (k' : rationalPoints G) hsub
    have hCa' : Ca = facet P.affineRoots x' := by
      apply (P.translatedApartmentMap_injective hinj (k' : rationalPoints G)).image_injective
      rw [← hCa, h', smul_image_apartmentMap]
    subst hCa'
    obtain ⟨y, hy, rfl⟩ := IsAffineRootSystemWithRankZero.exists_eq_facet_of_isFaceOf
      (hFaCa.trans (IsAffineRootSystemWithRankZero.isFaceOf_facet_of_mem_facetClosure hx'))
    rw [facetZeroStabilizer_eq_conjugate hD hW (hFa.trans (smul_image_apartmentMap _ _).symm) hy]
    refine Subgroup.map_mono ((hW.tits.standardParabolicSubgroup_le_iff _ _).2
      (Set.preimage_mono
        ((hΨ.subset_facetClosure_iff_facetSimpleReflections_subset hc hy hx').1 ?_)))
    obtain ⟨-, z, hz, hsub⟩ := hFaCa
    rwa [facetClosure_eq_of_facetRel (facet_eq_facet_iff.1 hz)] at hsub
  · intro hle
    obtain ⟨k, x, hx, hFc⟩ := exists_eq_zero_smul_facet hD hc hW Fc
    rw [facetZeroStabilizer_eq_conjugate hD hW hFc hx] at hle
    set L := hW.tits.standardParabolicSubgroup
      (P.facetSimpleInAffinePart_subset e (facet P.affineRoots c) (facet P.affineRoots x))
      with hL
    set L' := hW.tits.standardParabolicSubgroup
      (P.facetSimpleInAffinePart_subset e (facet P.affineRoots c) (facet P.affineRoots x'))
      with hL'
    have hBL : P.parahoricInZero (facet P.affineRoots c) ≤ L := hW.tits.le_of_coe_eq rfl
    have hBL' : P.parahoricInZero (facet P.affineRoots c) ≤ L' := hW.tits.le_of_coe_eq rfl
    have hconj : conjugateSubgroup (k⁻¹ * k') L' ≤ L := by
      have h := Subgroup.map_mono
        (f := (MulAut.conj k⁻¹ : P.zeroSubgroup →* P.zeroSubgroup)) hle
      change conjugateSubgroup k⁻¹ (conjugateSubgroup k' L') ≤
        conjugateSubgroup k⁻¹ (conjugateSubgroup k L) at h
      rwa [← conjugateSubgroup_mul, ← conjugateSubgroup_mul, inv_mul_cancel,
        conjugateSubgroup_one] at h
    have hg : k⁻¹ * k' ∈ L := L.inv_mem_iff.mp
      (hW.tits.mem_of_conjugate_le hBL _ fun b hb => by
        simpa [mul_assoc] using hconj ⟨b, hBL' hb, rfl⟩)
    have hL'L : L' ≤ L :=
      calc L' = conjugateSubgroup (k⁻¹ * k')⁻¹ (conjugateSubgroup (k⁻¹ * k') L') := by
            rw [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one]
        _ ≤ conjugateSubgroup (k⁻¹ * k')⁻¹ L := Subgroup.map_mono hconj
        _ = L := conjugateSubgroup_eq_self (L.inv_mem hg)
    have htype := (hW.tits.standardParabolicSubgroup_le_iff _ _).1 hL'L
    simp only [facetSimpleInAffinePart, e.surjective.preimage_subset_preimage_iff] at htype
    have hface : facet P.affineRoots x ⊆ facetClosure P.affineRoots x' :=
      (hΨ.subset_facetClosure_iff_facetSimpleReflections_subset hc hx hx').2 htype
    have hgY : ((k⁻¹ * k' : P.zeroSubgroup) : rationalPoints G) •
        (P.apartmentMap '' facet P.affineRoots x) = P.apartmentMap '' facet P.affineRoots x := by
      rw [← mem_zeroStabilizerIn, zeroStabilizerIn_facet_eq hD hW hx]
      exact hg
    refine ⟨(k' : rationalPoints G), facet P.affineRoots x, facet P.affineRoots x',
      ⟨isFacet_facet _ x, x', rfl, hface⟩, ?_, h'.trans (smul_image_apartmentMap _ _)⟩
    calc Fc.val = (k : rationalPoints G) • (P.apartmentMap '' facet P.affineRoots x) := hFc
      _ = (k : rationalPoints G) • (((k⁻¹ * k' : P.zeroSubgroup) : rationalPoints G) •
            (P.apartmentMap '' facet P.affineRoots x)) := by rw [hgY]
      _ = (k' : rationalPoints G) • (P.apartmentMap '' facet P.affineRoots x) := by
            rw [← mul_smul, ← Subgroup.coe_mul, mul_inv_cancel_left]
      _ = _ := smul_image_apartmentMap _ _

/-- The facet stabilizers of the facets contained in `A(S)` form the standard apartment of the
restricted building. -/
theorem facetStabilizersIn_apartmentImage_of_affineIwahoriTitsWith
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e) :
    P.facetStabilizersIn P.apartmentImage =
      restrictedApartment (P.parahoricInZero (facet P.affineRoots c)) P.affineTitsProjection
        (P.chamberSimpleInAffinePart e (facet P.affineRoots c)) 1 := by
  ext Q
  rw [hW.tits.mem_restrictedApartment_iff_conjugate]
  constructor
  · rintro ⟨Fc, hFcA, rfl⟩
    obtain ⟨k₀, x₀, -, hFc₀⟩ := exists_eq_zero_smul_facet hD hc hW Fc
    have hne : (Fc.val ∩ P.apartmentImage).Nonempty := by
      refine Set.Nonempty.mono (Set.subset_inter subset_rfl hFcA) ?_
      rw [hFc₀]
      exact ⟨_, Set.smul_mem_smul_set ⟨x₀, mem_facet_self _ x₀, rfl⟩⟩
    obtain ⟨Fa, ⟨y, rfl⟩, hFa⟩ := P.exists_isFacet_image_of_isFacet hD Fc.val Fc.property hne
    obtain ⟨n, x, hx, hyx⟩ := exists_normalizerInZero_smul_facet hD hc hW y
    have hFc : Fc.val = ((n : P.zeroSubgroup) : rationalPoints G) •
        (P.apartmentMap '' facet P.affineRoots x) := by
      rw [hFa, hyx, ← coe_normalizerInZeroPoint, normalizer_smul_image_apartmentMap]
    exact ⟨n, _, isAdmissibleType_facetSimpleInAffinePart hD hc e x, by
      rw [facetZeroStabilizer_eq_conjugate hD hW hFc hx, one_mul]⟩
  · rintro ⟨n, X, hX, rfl⟩
    obtain ⟨x, hx, rfl⟩ := exists_facetSimpleInAffinePart_eq hD hc e hX
    refine ⟨P.zeroFacetTranslate n (chamberFacet (isFacet_facet _ x)), ?_, ?_⟩
    · change ((n : P.zeroSubgroup) : rationalPoints G) •
        (P.apartmentMap '' facet P.affineRoots x) ⊆ P.apartmentImage
      rw [← coe_normalizerInZeroPoint, normalizer_smul_image_apartmentMap]
      exact Set.image_subset_range _ _
    · rw [facetZeroStabilizer_eq_conjugate hD hW
        (Fc := P.zeroFacetTranslate n (chamberFacet (isFacet_facet _ x))) rfl hx, one_mul]

/-- KP Proposition 7.6.3(1) and Remark 7.6.5: the apartments `h · A(S)` of `B(G)` are the
apartments of the restricted building, using `G(F) = G(F)^0 N(F)` (KP Fact 2.6.22). -/
theorem apartmentFacetStabilizers_eq_of_affineIwahoriTitsWith
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e) :
    P.apartmentFacetStabilizers =
      restrictedApartments (P.parahoricInZero (facet P.affineRoots c)) P.affineTitsProjection
        (P.chamberSimpleInAffinePart e (facet P.affineRoots c)) := by
  have hA := facetStabilizersIn_apartmentImage_of_affineIwahoriTitsWith hD hc hW
  ext Q
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨k, hk, m, hm, rfl⟩ :=
      exists_zero_mul_normalizer (P := P) simplyConnectedCentralizerProduct h
    have hk' := P.facetStabilizersIn_smul ⟨k, hk⟩ P.apartmentImage
    refine ⟨⟨k, hk⟩, ?_⟩
    change _ = P.facetStabilizersIn ((k * m) • P.apartmentImage)
    rw [mul_smul,
      MulAction.mem_stabilizer_iff.1 (P.normalizerPoints_le_stabilizer_apartmentImage hm)]
    refine Eq.trans ?_ hk'.symm
    rw [hA, hW.tits.image_conjugateSubgroup_restrictedApartment, mul_one]
  · rintro ⟨g, rfl⟩
    refine ⟨(g : rationalPoints G), ?_⟩
    change _ = P.facetStabilizersIn ((g : rationalPoints G) • P.apartmentImage)
    rw [P.facetStabilizersIn_smul, hA, hW.tits.image_conjugateSubgroup_restrictedApartment,
      mul_one]

/-- KP Axiom 4.1.9 at the chamber of `c`, for the actual affine Iwahori–Tits system. -/
theorem isBuildingTitsSystem_of_affineIwahoriTitsWith
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {c : P.Apartment} (hc : IsRegular P.affineRoots c)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith (facet P.affineRoots c) e) :
    P.IsBuildingTitsSystem (facet P.affineRoots c) P.affineTitsProjection
      (P.chamberSimpleInAffinePart e (facet P.affineRoots c)) := by
  have hB := chamberZeroStabilizerIn_eq_parahoricInZero hD hc hW
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]
    exact hW.tits
  · exact Set.Finite.preimage e.injective.injOn
      (finite_chamberSimpleReflections hD.isAffineRootSystem_affineRoots hc)
  · rw [hB]
    exact hW.saturated
  · rw [hB]
    exact bijOn_facetZeroStabilizer_of_affineIwahoriTitsWith hD hc hW
  · exact facetPrecedes_iff_of_affineIwahoriTitsWith hD hc hW
  · rw [hB]
    exact apartmentFacetStabilizers_eq_of_affineIwahoriTitsWith hD hc hW

end Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.Geometry.Building

/-- KP Propositions 7.6.3 and 7.6.4(1) and Remark 7.6.5: under the apartment axioms, an actual
affine Iwahori–Tits system for a chamber of `A(S)` is the Tits system of KP Axiom 4.1.9 on the
reduced building `B(G)`. -/
theorem affineIwahoriTitsBuilding : AffineIwahoriTitsBuildingStatement.{u} := by
  intro F _ _ _ _ G _ P hD _ _ C e hC hW
  obtain ⟨c, hc, rfl⟩ := hC
  exact ParahoricBuildingData.isBuildingTitsSystem_of_affineIwahoriTitsWith hD hc hW

end Langlands.Geometry.Building
