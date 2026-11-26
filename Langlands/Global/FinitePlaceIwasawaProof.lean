import Langlands.Global.FinitePlaceIwasawaStatement
import Langlands.Global.FinitePlaceIwasawaLocalInput
import Langlands.Global.FiniteCompletionLocalField
import Langlands.Geometry.Building.RootValuationBuildingConstructionProof
import Langlands.Geometry.Building.RootGroupActionAxiomProof
import Langlands.Geometry.Building.SpecialPointExistence
import Langlands.BruhatTits.Iwasawa.AvailableProof

/-! # Actual finite-place parabolic Iwasawa existence: proof

`Langlands.Global.FinitePlaceGroupPoints.parabolicIwasawaStatement` proves the published
`Langlands.Global.FinitePlaceGroupPoints.ParabolicIwasawaStatement`.

The local input is the norm-one stabilizer of a special point of the Bruhat–Tits building
of the base change of `G` to the finite completion. The building and its axioms come from
the published proofs `Langlands.Geometry.Building.rootValuationBuildingConstruction` and
`Langlands.Geometry.Building.rootGroupActionAxiom`. Compact-open maximality uses the
complete nonpositively curved metric of the building and the bounded-orbit fixed point;
the product with the minimal standard parabolic uses the chamber Iwasawa decomposition of
the relative Tits system and relative Weyl representatives in the special parahoric; every
actual parabolic contains a rational conjugate of the minimal standard one. The base-change
and point-topology adapters of `Langlands.Global.FinitePlaceIwasawaLocalInput` transport the
local subgroup to the actual finite-completion point group. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Global.FinitePlaceGroupPoints.ConstructionReduction

open Langlands.BruhatTits Langlands.BruhatTits.Iwasawa

set_option backward.isDefEq.respectTransparency false

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

set_option maxHeartbeats 1000000 in
/-- The source-left product with the minimal standard parabolic gives the product with every
actual algebraic parabolic: each contains a rational conjugate of the minimal one. -/
private theorem algebraic_of_minimal [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) {K : Subgroup (rationalPoints G)}
    (h : PointProductEqualities (standardParabolicPoints i ν ∅) K) :
    AlgebraicParabolicProducts K := by
  have hB : (standardParabolic i ν ∅) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν
  obtain ⟨P₀, j₀, hj₀, heq₀⟩ := isMinimalParabolicFunctor_iff_exists.mp
    (genericMinimalParabolic F G hG T i hi ν hν)
  have hpoints₀ : (rationalPoints.map j₀).range = standardParabolicPoints i ν ∅ := by
    change (SubgroupFunctor.range j₀).rationalPoints = _
    rw [heq₀, ← hB]
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

end Products

section Datum
variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G)

set_option maxHeartbeats 1000000 in
/-- Chamber Iwasawa decomposition plus relative Weyl representatives in a special parahoric:
the minimal standard parabolic times the parahoric of a special point is everything. -/
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
  obtain ⟨m, hm, hmn⟩ := SpecialCompact.WeylRepresentatives.special_parahoric_normalizer_surjective
    B hA hgen hF ν hν hx (QuotientGroup.mk n)
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

/-- A compact subgroup fixes a point of the reduced building: its orbits are bounded in the
complete nonpositively curved metric, and a bounded set has a canonical fixed center. -/
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
/-- The norm-one stabilizer of a special point is compact, open and maximal among compact
subgroups, from the seven building witnesses. -/
private theorem compact_open_maximal
    (R : B.toValuationBuildingData.PolysimplicialRealization)
    (T : B.toValuationBuildingData.ApartmentSplitting)
    (hbld : B.SatisfiesBuildingAxiom R) (hbdd : B.HasBoundedOpenStabilizers)
    (haff : B.SatisfiesAffineApartmentAxiom T) (hrefl : B.HasRootReflections)
    (hA : B.SatisfiesApartmentAxioms) (hfac : B.HasCompatibleApartmentFacets)
    (htits : B.HasTitsSystem)
    {y : B.ReducedBuilding} (hy : B.IsSpecialPoint y) :
    SpecialCompact.IsCompactOpenMaximal F (B.compactStabilizer y) := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨hopen, hbound⟩ := hbdd y
  have hclosed : IsClosed (B.compactStabilizer y : Set (rationalPoints G)) :=
    (B.compactStabilizer y).isClosed_of_isOpen hopen
  have hcompact : IsCompact (B.compactStabilizer y : Set (rationalPoints G)) := by
    exact (hbound.isCompact_closure G.X).of_isClosed_subset hclosed subset_closure
  obtain ⟨M⟩ := metricRealization F G B.isConnectedReductive B R T
    hbld hbdd haff hrefl hA hfac htits
  refine ⟨hcompact, hopen, hcompact, ?_⟩
  intro H hH hle
  obtain ⟨z, hz⟩ := compact_subgroup_fixes B M H hH
  have hF := rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hE : RelativeRoot.HasOppositeFactorPairs B.i :=
    fun a ha g hg hg1 => (hF a ha g hg hg1).1.exists
  have hzy : z = y :=
    B.toValuationBuildingData.eq_of_compactStabilizer_fixed_of_special_buildingPoint
      hA hE hfac.injective
      (fun x => R.hasCommonApartmentWith_of_isBuilding hbld.isBuilding (B.apartmentMap x))
      hy (fun g hg => hz g (hle hg))
  have hnorm : H ≤ rationalCommonNormKernel G :=
    compactSubgroup_le_rationalCommonNormKernel G H hH
  intro g hg
  exact B.mem_compactStabilizer.mpr ⟨hnorm hg, by simpa only [hzy] using hz g hg⟩

end Topology

end Datum

/-- The local input from the seven building witnesses and the zero-fixer generation clause:
the norm-one stabilizer of the image of a special apartment point is compact-open maximal and
has the source-left product with every actual algebraic parabolic. -/
theorem localExistence_of_witnesses
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G)
    (R : B.toValuationBuildingData.PolysimplicialRealization)
    (T : B.toValuationBuildingData.ApartmentSplitting)
    (hbld : B.SatisfiesBuildingAxiom R) (hbdd : B.HasBoundedOpenStabilizers)
    (haff : B.SatisfiesAffineApartmentAxiom T) (hrefl : B.HasRootReflections)
    (hA : B.SatisfiesApartmentAxioms) (hfac : B.HasCompatibleApartmentFacets)
    (htits : B.HasTitsSystem) (hgen : B.HasZeroFixerGenerators) :
    ∃ K : Subgroup (rationalPoints G),
      SpecialCompact.IsCompactOpenMaximal F K ∧ AlgebraicParabolicProducts K := by
  obtain ⟨x, hx⟩ := hA.isAffineRootSystem_affineRoots.exists_isSpecialPoint
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  obtain ⟨ν, hν⟩ := B.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter B.i
  refine ⟨B.compactStabilizer (B.apartmentMap x),
    compact_open_maximal B R T hbld hbdd haff hrefl hA hfac htits
      (B.apartment.isSpecialBuildingPoint_apartmentMap hx), ?_⟩
  exact algebraic_of_minimal B.isConnectedReductive B.i B.isMaximalSplitTorus ν hν
    (products_mono (minimal_parahoric_products B hA hgen ν hν hx) le_rfl
      (B.parahoricAt_le_compactStabilizer hA.topologyCompatible x))

/-- **Local existence.** For every connected reductive group over a nonarchimedean local
field, some subgroup of its rational points is compact, open and maximal among compact
subgroups, and has the source-left product with every actual algebraic parabolic. -/
theorem localExistence
    (F' : Type u) [Field F'] [ValuativeRel F'] [TopologicalSpace F']
    [IsNonarchimedeanLocalField F'] (G' : GroupScheme (Spec (CommRingCat.of F')))
    (hG' : IsConnectedReductive G') :
    haveI : IsAffineHom G'.X.hom := hG'.isAffineHom
    ∃ K : Subgroup (rationalPoints G'),
      SpecialCompact.IsCompactOpenMaximal F' K ∧ AlgebraicParabolicProducts K := by
  have : IsAffineHom G'.X.hom := hG'.isAffineHom
  obtain ⟨B, R, T, hbld, hbdd, haff, hrefl, hA, hfac, htits⟩ :=
    rootValuationBuildingConstruction F' G' hG'
  exact localExistence_of_witnesses B R T hbld hbdd haff hrefl hA hfac htits
    (rootGroupActionAxiom F' G' B hA).1

end Langlands.Global.FinitePlaceGroupPoints.ConstructionReduction

namespace Langlands.Global.FinitePlaceGroupPoints

open Langlands.GroupScheme Langlands.BruhatTits

set_option backward.isDefEq.respectTransparency false

/-- **Actual finite-place parabolic Iwasawa existence.** For every number field `F`,
connected reductive `G` over `F`, actual parabolic inclusion `p : P ⟶ G` and finite place
`v`, some subgroup of `G(F_v)` is compact in the regular-function evaluation topology,
maximal among compact subgroups, and satisfies `Set.range p_{F_v} * K = Set.univ`. -/
theorem parabolicIwasawaStatement : ParabolicIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp v
  let := FiniteCompletion.valuativeRel v
  have := FiniteCompletion.isNonarchimedeanLocalField v
  obtain ⟨K, hK, hprod⟩ := ConstructionReduction.localExistence (FiniteCompletion F v)
    (baseChangedGroup F G v) (baseChanged_isConnectedReductive F G hG v)
  exact ⟨_, (baseChangeIwasawaCompactOfParabolicProducts F G hG p hp v ⟨K, hK, hprod⟩).2⟩

end Langlands.Global.FinitePlaceGroupPoints
