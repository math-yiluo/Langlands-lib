import Langlands.BruhatTits.SpecialCompact.WeylRepresentatives
import Langlands.BruhatTits.Iwasawa.AvailableStatement
import Langlands.Geometry.Building.IwasawaDecompositionProof
import Langlands.Geometry.Building.SpecialPointGlobalFixedLocus
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Geometry.Building.NormalizerApartmentActionKernel
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.Geometry.Building.BuildingFacetIncidence
import Langlands.Geometry.Building.AffineWeylFacetFixing
import Langlands.Geometry.Building.MetricRealizationProof
import Langlands.Geometry.Metric.KPBoundedSetStabilizerProof
import Langlands.Geometry.Metric.KPCompleteNPCGeodesicProof
import Langlands.BruhatTits.RationalPoints.BoundedSubgroupNormKernel
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicContainsMinimalProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-!
# KP Theorem 5.3.4 on available corrected Bruhat–Tits data

The exact published available Iwasawa statement, including all six parabolic
families, both product orders, parahoric inclusion and compact-open maximality.
Specialness supplies the finite Weyl representatives inside the actual parahoric;
chamber Iwasawa then gives the minimal product. Compact-orbit fixed points and the
unique fixed locus of a special norm-one stabilizer give maximality.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.Iwasawa

section Products
variable {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))}

private theorem products_of_factorization (H K : Subgroup (rationalPoints G))
    (h : ∀ g : rationalPoints G, ∃ p ∈ H, ∃ k ∈ K, g = p * k) :
    PointProductEqualities H K := by
  constructor
  · apply Set.Subset.antisymm (fun g _ => ?_) (Set.subset_univ _)
    obtain ⟨p, hp, k, hk, rfl⟩ := h g
    exact Set.mul_mem_mul hp hk
  · apply Set.Subset.antisymm (fun g _ => ?_) (Set.subset_univ _)
    obtain ⟨p, hp, k, hk, heq⟩ := h g⁻¹
    have hg : g = k⁻¹ * p⁻¹ := by rw [← mul_inv_rev, ← heq, inv_inv]
    rw [hg]
    exact Set.mul_mem_mul (K.inv_mem hk) (H.inv_mem hp)

private theorem factorization_of_products {H K : Subgroup (rationalPoints G)}
    (h : PointProductEqualities H K) (g : rationalPoints G) :
    ∃ p ∈ H, ∃ k ∈ K, g = p * k := by
  obtain ⟨p, hp, k, hk, heq⟩ := Set.mem_mul.mp (h.1 ▸ Set.mem_univ g)
  exact ⟨p, hp, k, hk, heq.symm⟩

private theorem products_mono {H K H' K' : Subgroup (rationalPoints G)}
    (h : PointProductEqualities H K) (hH : H ≤ H') (hK : K ≤ K') :
    PointProductEqualities H' K' := by
  apply products_of_factorization
  intro g
  obtain ⟨p, hp, k, hk, heq⟩ := factorization_of_products h g
  exact ⟨p, hH hp, k, hK hk, heq⟩

private theorem products_conjugate_left {H K : Subgroup (rationalPoints G)}
    (h : PointProductEqualities H K) (a : rationalPoints G) :
    PointProductEqualities (H.map (MulAut.conj a).toMonoidHom) K := by
  obtain ⟨k, hk, b, hb, hkb⟩ := Set.mem_mul.mp (h.2 ▸ Set.mem_univ a)
  apply products_of_factorization
  intro g
  obtain ⟨p, hp, q, hq, heq⟩ := factorization_of_products h (k⁻¹ * g)
  refine ⟨k * p * k⁻¹, ?_, k * q, K.mul_mem hk hq, ?_⟩
  · refine ⟨b⁻¹ * p * b, H.mul_mem (H.mul_mem (H.inv_mem hb) hp) hb, ?_⟩
    change a * (b⁻¹ * p * b) * a⁻¹ = k * p * k⁻¹
    rw [← hkb]
    group
  · calc
      g = k * (k⁻¹ * g) := by group
      _ = k * (p * q) := by rw [heq]
      _ = (k * p * k⁻¹) * (k * q) := by group

private theorem products_map_conj {H K : Subgroup (rationalPoints G)}
    (h : PointProductEqualities H K) (a : rationalPoints G) :
    PointProductEqualities (H.map (MulAut.conj a).toMonoidHom)
      (K.map (MulAut.conj a).toMonoidHom) := by
  apply products_of_factorization
  intro g
  obtain ⟨p, hp, k, hk, heq⟩ := factorization_of_products h (a⁻¹ * g * a)
  refine ⟨a * p * a⁻¹, ⟨p, hp, rfl⟩, a * k * a⁻¹, ⟨k, hk, rfl⟩, ?_⟩
  calc
    g = a * (a⁻¹ * g * a) * a⁻¹ := by group
    _ = a * (p * k) * a⁻¹ := by rw [heq]
    _ = (a * p * a⁻¹) * (a * k * a⁻¹) := by group

private theorem products_conjugate_right {H K : Subgroup (rationalPoints G)}
    (h : PointProductEqualities H K) (a : rationalPoints G) :
    PointProductEqualities H (K.map (MulAut.conj a).toMonoidHom) := by
  have h' := products_map_conj (products_conjugate_left h a⁻¹) a
  simpa only [ParahoricBuildingData.map_conj_map_conj, mul_inv_cancel,
    ParahoricBuildingData.map_conj_one] using h'

private theorem family_mono [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {K K' : Subgroup (rationalPoints G)}
    (h : ParabolicPointProductFamily i ν K) (hK : K ≤ K') :
    ParabolicPointProductFamily i ν K' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨fun P j hj => products_mono (h1 P j hj) le_rfl hK,
    fun χ => products_mono (h2 χ) le_rfl hK,
    fun J hJ => products_mono (h3 J hJ) le_rfl hK,
    fun P j hj g => products_mono (h4 P j hj g) le_rfl hK,
    fun χ g => products_mono (h5 χ g) le_rfl hK,
    fun J hJ g => products_mono (h6 J hJ g) le_rfl hK⟩

private theorem family_conjugate [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {K : Subgroup (rationalPoints G)}
    (h : ParabolicPointProductFamily i ν K) (a : rationalPoints G) :
    ParabolicPointProductFamily i ν (K.map (MulAut.conj a).toMonoidHom) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨fun P j hj => products_conjugate_right (h1 P j hj) a,
    fun χ => products_conjugate_right (h2 χ) a,
    fun J hJ => products_conjugate_right (h3 J hJ) a,
    fun P j hj g => products_conjugate_right (h4 P j hj g) a,
    fun χ g => products_conjugate_right (h5 χ g) a,
    fun J hJ g => products_conjugate_right (h6 J hJ g) a⟩

set_option maxHeartbeats 1000000 in
private theorem family_of_minimal [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {K : Subgroup (rationalPoints G)}
    (h : PointProductEqualities (standardParabolicPoints i ν ∅) K) :
    ParabolicPointProductFamily i ν K := by
  have hB : (standardParabolic i ν ∅) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν
  obtain ⟨P₀, j₀, hj₀, heq₀⟩ := isMinimalParabolicFunctor_iff_exists.mp
    (genericMinimalParabolic F G hG T i hi ν hν)
  have hpoints₀ : (rationalPoints.map j₀).range = standardParabolicPoints i ν ∅ := by
    change (SubgroupFunctor.range j₀).rationalPoints = _
    rw [heq₀, ← hB]
  have halg : AlgebraicParabolicProducts K := by
    intro P j hj
    obtain ⟨Q, j', hj', hle⟩ := parabolicContainsMinimalStatement F G hG P j hj
    obtain ⟨g, e, hcomp⟩ := minimalParabolicConjugacy F G hG P₀ Q j₀ j' hj₀ hj'
    have hrange : ((rationalPoints.map j₀).range.map (MulAut.conj g).toMonoidHom) ≤
        (rationalPoints.map j).range := by
      rw [← rationalPoints_range_comp_innerIso, hcomp]
      change (SubgroupFunctor.range (e.hom ≫ j')).rationalPoints ≤ _
      rw [SubgroupFunctor.range_iso_comp]
      exact hle _
    exact products_mono (products_conjugate_left (hpoints₀ ▸ h) g) hrange le_rfl
  have hdyn : DynamicParabolicProducts K := by
    intro χ
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have hp := Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic
      parabolicDynamic hG χ
    have hre := SubgroupFunctor.rationalPoints_eq_range
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
    change PointProductEqualities (Dynamic.parabolic χ).rationalPoints K
    rw [hre]
    exact halg _ _ hp
  have hstd : StandardParabolicProducts i ν K := by
    intro J hJ
    have hle := ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J
      (Set.empty_subset _) hJ).1.mp (Set.empty_subset J)
    exact products_mono h (hle _) le_rfl
  refine ⟨halg, hdyn, hstd, ?_, fun χ g => hdyn _, ?_⟩
  · intro P j hj g
    rw [rationalPoints_range_comp_innerIso]
    exact products_conjugate_left (halg P j hj) g
  · intro J hJ g
    change PointProductEqualities ((standardParabolic i ν J).comap
      (G.innerIso g).inv).rationalPoints K
    rw [standardParabolicPoints_comap_innerIso_inv]
    exact products_conjugate_left (hstd J hJ) g

end Products

section Datum
variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G)

set_option maxHeartbeats 1000000 in
private theorem minimal_parahoric_products
    (hA : B.SatisfiesApartmentAxioms) (hgen : B.HasZeroFixerGenerators)
    (ν : cocharacterLattice B.S) (hν : IsGenericCocharacter B.i ν)
    {x : B.Apartment} (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x) :
    PointProductEqualities (standardParabolicPoints B.i ν ∅) (B.parahoricAt x) := by
  have hF := rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hTits := relativeTitsSystem F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus ν hν
  obtain ⟨c, hc, hxc⟩ := hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
    |>.exists_regularPoint_closure x
  let C := AffineRootSystem.facet B.affineRoots c
  have hC : AffineRootSystem.IsChamber B.affineRoots C := ⟨c, hc, rfl⟩
  have hCx : B.parahoric C ≤ B.parahoricAt x := by
    apply (B.parahoric_anti (Set.singleton_subset_iff.mpr
      (AffineRootSystem.mem_facet_self B.affineRoots c))).trans
    exact sup_le_sup_left (B.apartment.sharpFixer_singleton_le_of_mem_facetClosure
      hA.mem_or_two_smul_mem hxc) _
  have hI := B.iwasawaDecomposition_of_relativeTitsSystem hA hC hν hF
    (hasSimpleRootParabolicFactorization_of_statements relativeRootSystem standardParabolicEndpoints
      genericCentralizer RelativeRoot.dynamicRootOrderedProduct F G B.isConnectedReductive
      B.S B.i B.isMaximalSplitTorus ν hν) hTits
  apply products_of_factorization
  intro g
  obtain ⟨u, hu, n, p, hp, rfl⟩ := hI g
  obtain ⟨m, hm, hmn⟩ := SpecialCompact.WeylRepresentatives.special_parahoric_normalizer_surjective B hA hgen hF ν hν hx
    (QuotientGroup.mk n)
  have hcentral : (n * m⁻¹ : normalizerPoints B.i).val ∈ centralizerPoints B.i := by
    change n * m⁻¹ ∈ (centralizerPoints B.i).subgroupOf (normalizerPoints B.i)
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' ((centralizerPoints B.i).subgroupOf (normalizerPoints B.i)))
      (n * m⁻¹) = 1
    rw [map_mul, map_inv]
    change (QuotientGroup.mk n : relativeWeylGroup B.i) * (QuotientGroup.mk m)⁻¹ = 1
    rw [hmn, mul_inv_cancel]
  refine ⟨u * (n * m⁻¹ : normalizerPoints B.i).val, ?_, m.val * p,
    (B.parahoricAt x).mul_mem hm (hCx hp), ?_⟩
  · exact (standardParabolicPoints B.i ν ∅).mul_mem
      (standardUnipotent_le_standardParabolic B.i ν ∅ _ hu)
      ((torusCentralizer_le_standardLevi B.i ν ∅).trans
        (standardLevi_le_standardParabolic B.i ν ∅) _
          (by
            exact (congrArg
              (fun H : Subgroup (rationalPoints G) => (n * m⁻¹ : normalizerPoints B.i).val ∈ H)
              (torusCentralizer_carrier_base B.i)).mpr hcentral))
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

section Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- The compact-orbit part of the public fixed-point draft by Worker 3557. -/
private theorem compact_subgroup_fixes
    (M : B.toValuationBuildingData.MetricRealization)
    (H : Subgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    ∃ y : B.ReducedBuilding, ∀ h ∈ H, h • y = y := by
  let : MetricSpace B.ReducedBuilding := M.metric
  let : CompleteSpace B.ReducedBuilding := M.complete
  let : IsIsometricSMul (rationalPoints G) B.ReducedBuilding := M.isometric
  have hNPC := M.nonpositivelyCurved
  have hgeo := Langlands.Geometry.Metric.KP.completeNPCGeodesic B.ReducedBuilding hNPC
  let x := B.apartmentMap (Classical.arbitrary B.Apartment)
  let O := (fun g : rationalPoints G => g • x) '' (H : Set (rationalPoints G))
  have hO : O.Nonempty := ⟨x, 1, H.one_mem, one_smul _ _⟩
  have hbounded : Bornology.IsBounded O :=
    (hH.image (M.continuous_orbit x)).isBounded
  obtain ⟨y, hy⟩ := Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint
    B.ReducedBuilding hNPC hgeo O hO hbounded
  refine ⟨y, fun h hh => hy (IsometryEquiv.constSMul h) ?_⟩
  change (fun z : B.ReducedBuilding => h • z) '' O = O
  ext z
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨h * g, H.mul_mem hh hg, mul_smul h g x⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(h⁻¹ * g) • x, ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) hg, rfl⟩, ?_⟩
    change h • (h⁻¹ * g) • x = g • x
    rw [smul_smul, mul_inv_cancel_left]

set_option maxHeartbeats 1000000 in
private theorem available_compact_open_maximal
    (D : KPBuildingDatum G) (hD : D.SatisfiesGroupAxioms)
    {y : D.base.ReducedBuilding} (hy : D.base.IsSpecialPoint y) :
    SpecialCompact.IsCompactOpenMaximal F (D.base.compactStabilizer y) := by
  let B := D.base
  have hA := hD.affineRootSystem.apartmentAxioms
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨hopen, hbound⟩ := hD.boundedSubgroups y
  have hclosed : IsClosed (B.compactStabilizer y : Set (rationalPoints G)) :=
    (B.compactStabilizer y).isClosed_of_isOpen hopen
  have hcompact : IsCompact (B.compactStabilizer y : Set (rationalPoints G)) := by
    exact (hbound.isCompact_closure G.X).of_isClosed_subset hclosed subset_closure
  obtain ⟨M⟩ := metricRealization F G B.isConnectedReductive B D.realization D.splitting
    hD.building hD.boundedSubgroups hD.affineStructure hD.affineRootSystem.rootReflections
    hA hD.affineRootSystem.compatibleApartmentFacets hD.titsSystem
  refine ⟨hcompact, hopen, hcompact, ?_⟩
  intro H hH hle
  obtain ⟨z, hz⟩ := compact_subgroup_fixes B M H hH
  have hF := rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hE : RelativeRoot.HasOppositeFactorPairs B.i :=
    fun a ha g hg hg1 => (hF a ha g hg hg1).1.exists
  have hzy : z = y := B.toValuationBuildingData.eq_of_compactStabilizer_fixed_of_special_buildingPoint
    hA hE hD.affineRootSystem.compatibleApartmentFacets.injective
    (fun x => D.realization.hasCommonApartmentWith_of_isBuilding hD.building.isBuilding
      (B.apartmentMap x)) hy (fun g hg => hz g (hle hg))
  have hnorm : H ≤ rationalCommonNormKernel G := compactSubgroup_le_rationalCommonNormKernel G H hH
  intro g hg
  exact B.mem_compactStabilizer.mpr ⟨hnorm hg, by simpa only [hzy] using hz g hg⟩

end Topology

private theorem special_in_parahoric_chart
    (hA : B.SatisfiesApartmentAxioms)
    (g : rationalPoints G) (x : B.Apartment)
    (hy : B.IsSpecialPoint (g • B.apartmentMap x)) :
    AffineRootSystem.IsSpecialPoint B.affineRoots x := by
  obtain ⟨h, a, hax, ha⟩ := hy
  have htrans : (g⁻¹ * h) • B.apartmentMap a = B.apartmentMap x := by
    rw [mul_smul, hax, inv_smul_smul]
  obtain ⟨n, hn, -⟩ := B.toValuationBuildingData.exists_normalizer_eq_on_translated_facetClosure
    hA (g⁻¹ * h) htrans
  have hnroot : B.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.rootStabilizer B.affineRoots :=
    (hA.range_le_extendedAffineWeylGroup ⟨n, rfl⟩).1
  have hx := (AffineRootSystem.isSpecialPoint_apply_iff hnroot a).mpr ha
  change AffineRootSystem.IsSpecialPoint B.affineRoots (n • a) at hx
  rwa [hn] at hx

set_option maxHeartbeats 1000000 in
private theorem available_point_conclusions
    (D : KPBuildingDatum G) (hD : D.SatisfiesGroupAxioms)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν)
    (y : D.base.ReducedBuilding) (hy : D.base.IsSpecialPoint y)
    (Q : Subgroup (rationalPoints G)) (hQ : D.base.IsParahoricAt y Q) :
    ParabolicPointProductFamily D.base.i ν Q ∧
      Q ≤ D.base.compactStabilizer y ∧
      ParabolicPointProductFamily D.base.i ν (D.base.compactStabilizer y) ∧
      SpecialCompact.IsCompactOpenMaximal F (D.base.compactStabilizer y) := by
  let B := D.base
  have hA := hD.affineRootSystem.apartmentAxioms
  obtain ⟨g, x, rfl, rfl⟩ := hQ
  have hx := special_in_parahoric_chart B hA g x hy
  have hprod := family_of_minimal B.isConnectedReductive B.i B.isMaximalSplitTorus ν hν
    (minimal_parahoric_products B hA hD.rootGroupAction.zeroFixerGenerators ν hν hx)
  have hprod' := family_conjugate hprod g
  have hle : (B.parahoricAt x).map (MulAut.conj g).toMonoidHom ≤
      B.compactStabilizer (g • B.apartmentMap x) := by
    rintro z ⟨p, hp, rfl⟩
    exact B.toValuationBuildingData.conj_mem_compactStabilizer g
      (B.parahoricAt_le_compactStabilizer hA.topologyCompatible x hp)
  exact ⟨hprod', hle, family_mono hprod' hle, available_compact_open_maximal D hD hy⟩

end Datum

/-- KP Theorem 5.3.4 with the compact-open maximal stabilizer consequences, on
exactly the available corrected Bruhat–Tits data of the published statement. -/
theorem availableIwasawa : AvailableIwasawaStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν
  let D := 𝔅.datum F G hG
  let B := D.base
  have hD : D.SatisfiesGroupAxioms := h𝔅.groupAxioms
  constructor
  · intro x hx
    exact available_point_conclusions D hD ν hν (B.apartmentMap x)
      (B.apartment.isSpecialBuildingPoint_apartmentMap hx.1) (B.parahoricAt x)
      (B.isParahoricAt_apartmentMap x)
  · intro y hy _ Q hQ
    exact available_point_conclusions D hD ν hν y hy Q hQ

end Langlands.BruhatTits.Iwasawa
