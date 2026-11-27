import Langlands.Global.AdelicStandardLeviUnipotentFactors
import Langlands.Global.AdelicUnipotentDecayModulo
import Langlands.Global.AdelicStandardLeviHeightRestriction
import Langlands.Global.AdelicSubgroupNormOne
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # Standard Levi contraction modulo the outer unipotent radical -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicGeometry CategoryTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints
  AdelicSiegelFactors PositiveRealTorus RepresentationGrowth

section Displacement

variable {F : Type u} [Field F] [NumberField F]
  {G U H V N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine U.X.left] [IsAffine H.X.left] [IsAffine V.X.left] [IsAffine N.X.left]
  (j : U ⟶ G) (l : H ⟶ G) (v₀ : V ⟶ H) (n₀ : N ⟶ G)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "V∞" => InfiniteAdelicGroupPoints F V
local notation "m" => map F U G j
local notation "mL" => map F H G l
local notation "mV" => map F V G (v₀ ≫ l)
local notation "mN" => map F N G n₀
local notation "R" => MonoidHom.range (ContinuousMonoidHom.toMonoidHom m)
local notation "R₀" => MonoidHom.range (ContinuousMonoidHom.toMonoidHom mN)
local notation "j∞" => V.affinePointsTarget (v₀ ≫ l) (CommAlgCat.of F (InfiniteAdeleRing F))

private theorem archimedeanPart_map {H₁ H₂ : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H₁.X.left] [IsAffine H₂.X.left] (f : H₁ ⟶ H₂) (x : AdelicGroupPoints F H₁) :
    ofInfinite F H₂ (infinite F H₂ (map F H₁ H₂ f x)) =
      map F H₁ H₂ f (ofInfinite F H₁ (infinite F H₁ x)) := by
  rw [map_ofInfinite]
  congr 1

private theorem archimedeanPart_eq_self {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] (x : AdelicGroupPoints F H) (hx : finite F H x = 1) :
    ofInfinite F H (infinite F H x) = x := by
  apply (split F H).injective
  simp only [split_apply, infinite_ofInfinite, finite_ofInfinite, hx]

private theorem map_comp_point {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of F))}
    (f : H₁ ⟶ H₂) (g : H₂ ⟶ H₃) (x : AdelicGroupPoints F H₁) :
    map F H₂ H₃ g (map F H₁ H₂ f x) = map F H₁ H₃ (f ≫ g) x := by
  change (x ≫ f.hom.hom) ≫ g.hom.hom = x ≫ (f ≫ g).hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

private theorem ofInfinite_unipotent_image_mem_normOne
    {H₁ H₂ : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H₁.X.left] [IsAffine H₂.X.left] [LocallyOfFiniteType H₂.X.hom]
    (f : H₁ ⟶ H₂) [IsClosedImmersion f.hom.hom.left]
    (hs : Smooth H₁.X.hom) (hc : ConnectedSpace H₁.X.left) (hu : IsUnipotent H₁)
    (x : InfiniteAdelicGroupPoints F H₁) :
    ofInfinite F H₂ (H₁.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F)) x) ∈
      normOneSubgroup F H₂ := by
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F H₂ (SubgroupFunctor.range f) :
      Set (AdelicGroupPoints F H₂)) := AdelicSubgroupPoints.isClosed_adelicPoints_range F H₂ f
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F H₂ (SubgroupFunctor.range f)) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F f hs hc hu
  rw [← map_ofInfinite]
  exact AdelicSubgroupPoints.adelicPoints_le_normOneSubgroup F H₂ (SubgroupFunctor.range f)
    ⟨ofInfinite F H₁ x, rfl⟩

/-- Push contraction in the Levi through the embedding, and move the outer
radical factor to the left. -/
private theorem hasUnipotentContractionModulo_of_compact_factors
    {X : Type v} {E : Type u} [NormedAddCommGroup E] (Q : V∞ ≃ₜ E)
    (Ω : Set A) (hΩ : IsCompact Ω)
    (hΩU : Ω ⊆ (Subgroup.normalizer (R : Set A) : Set A))
    (hΩN : Ω ⊆ (Subgroup.normalizer (R₀ : Set A) : Set A))
    (hLN : (mL).toMonoidHom.range ≤ Subgroup.normalizer (R₀ : Set A))
    (a : X → AdelicGroupPoints F H) (ha : ∀ t, finite F H (a t) = 1) (ε : X → ℝ)
    (hfactor : ∀ D : Set A, IsCompact D → D ⊆ R →
      ∃ B : Set (AdelicGroupPoints F V), IsCompact B ∧ ∀ w ∈ D,
        ∃ y ∈ B, ∃ z : AdelicGroupPoints F N, w = mV y * mN z)
    (hsmall : ∀ B : Set (AdelicGroupPoints F V), IsCompact B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ B, ∀ t : X, ∃ y' : AdelicGroupPoints F V,
        (a t)⁻¹ * map F V H v₀ y * a t = map F V H v₀ y' ∧
          ‖Q (infinite F V y')‖ ≤ C * ε t) :
    HasUnipotentContractionModulo j Ω (fun t => mL (a t)) R₀
      (fun v => j∞ (Q.symm v)) ε := by
  intro D hD
  let w (pu : A × U∞) := pu.1⁻¹ * m (ofInfinite F U pu.2) * pu.1
  have hw : Continuous w :=
    (continuous_fst.inv.mul (((m).continuous.comp (ofInfinite F U).continuous).comp continuous_snd)).mul
      continuous_fst
  have hwU : w '' (Ω ×ˢ D) ⊆ R := by
    rintro _ ⟨⟨p, u⟩, hp, rfl⟩
    change w (p, u) ∈ R
    have hp' := (Subgroup.normalizer (R : Set A)).inv_mem (hΩU hp.1)
    have hu : m (ofInfinite F U u) ∈ R := ⟨_, rfl⟩
    simpa only [w, inv_inv] using (Subgroup.mem_normalizer_iff.mp hp' _).mp hu
  obtain ⟨B, hB, hfact⟩ := hfactor _ ((hΩ.prod hD).image hw) hwU
  obtain ⟨C, hC, hcoord⟩ := hsmall B hB
  refine ⟨C, hC, fun p hp t u hu => ?_⟩
  let arch (x : A) := ofInfinite F G (infinite F G x)
  let aG := mL (a t)
  obtain ⟨y, hy, z, he⟩ := hfact (w (p, u)) ⟨(p, u), ⟨hp, hu⟩, rfl⟩
  have hwfin : finite F G (w (p, u)) = 1 := by
    simp only [w, map_mul, map_inv, finite_map, finite_ofInfinite, map_one, mul_one, inv_mul_cancel]
  have haGfin : finite F G aG = 1 := by rw [show aG = mL (a t) from rfl, finite_map, ha, map_one]
  have hdecomp : w (p, u) = arch (mV y) * arch (mN z) := by
    have h := congrArg arch he
    simpa only [arch, map_mul, archimedeanPart_eq_self _ hwfin] using h
  obtain ⟨y', hy', hnorm⟩ := hcoord y hy t
  have hv' : aG⁻¹ * mV y * aG = mV y' := by
    have hh := congrArg mL hy'
    simpa only [map_mul, map_inv, map_comp_point, aG] using hh
  have hsmall' : aG⁻¹ * arch (mV y) * aG = ofInfinite F G (j∞ (infinite F V y')) := by
    have hh := congrArg arch hv'
    simp only [arch, map_mul, map_inv, archimedeanPart_eq_self _ haGfin] at hh
    rw [archimedeanPart_map, map_ofInfinite] at hh
    exact hh
  let vG := arch (mV y)
  let nG := arch (mN z)
  have hnG : nG ∈ R₀ := by
    change ofInfinite F G (infinite F G (mN z)) ∈ R₀
    rw [archimedeanPart_map]
    exact ⟨_, rfl⟩
  have hvG : vG ∈ (mL).toMonoidHom.range := by
    change ofInfinite F G (infinite F G (mV y)) ∈ (mL).toMonoidHom.range
    rw [archimedeanPart_map, ← map_comp_point]
    exact ⟨_, rfl⟩
  let n₁ := (p * vG) * nG * (p * vG)⁻¹
  have hpv : p * vG ∈ Subgroup.normalizer (R₀ : Set A) :=
    (Subgroup.normalizer (R₀ : Set A)).mul_mem (hΩN hp) (hLN hvG)
  have hn₁ : n₁ ∈ R₀ := (Subgroup.mem_normalizer_iff.mp hpv _).mp hnG
  refine ⟨Q (infinite F V y'), hnorm, n₁, hn₁, ?_⟩
  simp only [Q.symm_apply_apply]
  change m (ofInfinite F U u) * (p * aG) =
    n₁ * ((p * aG) * ofInfinite F G (j∞ (infinite F V y')))
  rw [← hsmall']
  calc
    m (ofInfinite F U u) * (p * aG) = p * (w (p, u) * aG) := by dsimp [w]; group
    _ = p * ((vG * nG) * aG) := by rw [hdecomp]
    _ = n₁ * ((p * aG) * (aG⁻¹ * vG * aG)) := by dsimp [n₁]; group

end Displacement

section Standard

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  {d : ℕ} (hSmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "IG" => 𝓘(ℝ, smoothModel F d)
local notation "Δ" => simpleRelativeRoots i ν
local notation "Pts" => intrinsicSubgroup F T
local notation "aG" => positiveMap F G T i T (𝟙 T)
local notation "A₀" => MonoidHom.range
  (ContinuousMonoidHom.toMonoidHom (map F _ G (Standard.parabolicHom i ν ∅)))
local notation "U(" S ")" => Standard.unipotentScheme i ν S
local notation "j(" S ")" => Standard.unipotentHom i ν S
local notation "N(" S ")" => MonoidHom.range (ContinuousMonoidHom.toMonoidHom (map F (U(S)) G (j(S))))

variable (F T) in
/-- The weak chamber on the positive torus for the roots in the upper Levi. -/
def standardLeviWeakChamber (S : Set (characterLattice T)) (b : ℝ≥0ˣ) : Set Pts :=
  {a | ∀ α ∈ S, b ≤ normCharacter F T ((𝟙 T) ≫ α) a}

local notation "Ch(" S "," b ")" => standardLeviWeakChamber F T S b

include hG hi hν in
omit [LocallyOfFiniteType G.X.hom] in
private theorem minimalParabolic_le_normalizer_standardRadical
    (S : Set (characterLattice T)) (hS : S ⊆ Δ) :
    A₀ ≤ Subgroup.normalizer (N(S) : Set A) := by
  let B := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))
  change (SubgroupFunctor.range (Standard.parabolicHom i ν ∅)).carrier B ≤
    Subgroup.normalizer ((SubgroupFunctor.range (j(S))).carrier B : Set (B ⟶ G.X))
  rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2, (Standard.isRepresentedBy_unipotentHom i ν S).2,
    Subgroup.le_normalizer_iff]
  intro p hp u hu
  have hpar := (standardParabolicOrder F G hG T i hi ν hν).1 ∅ S (empty_subset Δ) hS
  exact StandardLeviIntersection.conj_mem_standardUnipotent i ν ((hpar.1.mp (empty_subset S)) B hp) hu

include hG hi hν in
/-- For a root of the upper standard Levi, the ambient maximal radical
contracts at the corresponding root rate modulo the outer radical. The
simple-root lower bounds are those in the upper Levi. The right displacement
takes values in the archimedean part of the ambient norm-one group. -/
theorem exists_standardLeviContractionModulo_normOne
    (S : Set (characterLattice T)) (hS : S ⊆ Δ) (α : characterLattice T) (hα : α ∈ S)
    (b : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ A₀) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffine (U(Δ \ {α})).X.left := @isAffine_of_isAffineHom _ _ (U(Δ \ {α})).X.hom
      (Standard.isClosedSubgroup_unipotentHom i ν (Δ \ {α})).isAffineHom_source inferInstance
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hSmooth
    ∃ (n : ℕ) (Ψ : (Fin n → mixedEmbedding.mixedSpace F) → G∞),
      Ψ 0 = 1 ∧ ContMDiff 𝓘(ℝ, Fin n → mixedEmbedding.mixedSpace F) IG ∞ Ψ ∧
      HasUnipotentContractionModulo (j(Δ \ {α})) Ω
        (fun a : Ch(S, b) => aG a.val) N(S) Ψ (fun a => relativeCharacterDecay (𝟙 T) α a.val) ∧
      (∀ v, ofInfinite F G (Ψ v) ∈ normOneSubgroup F G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hSmooth
  let M := Δ \ {α}
  have hM : M ⊆ Δ := sdiff_subset
  let L := Standard.leviScheme i ν S
  let jL := Standard.leviHom i ν S
  let iL := standardLeviTorusFactor i ν S (Standard.isRepresentedBy_leviHom i ν S)
  let : IsAffineHom L.X.hom := (Standard.isClosedSubgroup_leviHom i ν S).isAffineHom_source
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let V := Standard.unipotentScheme iL ν (S ∩ M)
  let jV := Standard.unipotentHom iL ν (S ∩ M)
  let : IsAffine V.X.left := @isAffine_of_isAffineHom _ _ V.X.hom
    (Standard.isClosedSubgroup_unipotentHom iL ν (S ∩ M)).isAffineHom_source inferInstance
  let : IsAffine (U(M)).X.left := @isAffine_of_isAffineHom _ _ (U(M)).X.hom
    (Standard.isClosedSubgroup_unipotentHom i ν M).isAffineHom_source inferInstance
  let : IsAffine (U(S)).X.left := @isAffine_of_isAffineHom _ _ (U(S)).X.hom
    (Standard.isClosedSubgroup_unipotentHom i ν S).isAffineHom_source inferInstance
  let : LocallyOfFiniteType L.X.hom := (Standard.isClosedSubgroup_leviHom i ν S).locallyOfFiniteType
  have hRed := (standardLeviSplitComponentStatement F G hG T i hi ν hν S hS).1
  have hiL := hi.isMaximalSplitTorus_standardLeviTorusFactor i ν S
    (Standard.isRepresentedBy_leviHom i ν S) (Standard.isClosedSubgroup_leviHom i ν S)
  have hFam := standardLeviStandardFamilies dynamicLie standardCocharacter F G hG T i hi ν hν S hS
    L hRed jL (Standard.isRepresentedBy_leviHom i ν S) (Standard.isClosedSubgroup_leviHom i ν S)
  obtain ⟨hΔL, hνL, _⟩ := hFam
  have hVM : S ∩ M = simpleRelativeRoots iL ν \ {α} := by
    rw [hΔL]
    ext β
    simp only [M, Set.mem_inter_iff, Set.mem_sdiff]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hS h.1, h.2⟩⟩
  have hαL : α ∈ simpleRelativeRoots iL ν := hΔL.symm ▸ hα
  have hVIndex : S ∩ M ⊆ simpleRelativeRoots iL ν := by rw [hΔL]; exact inter_subset_left
  have hgeom := (Standard.parabolicStructure iL ν hRed hiL hνL _
    hVIndex).2.2.1
  obtain ⟨dV, hV⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension V.X.left _ V.X.hom
    hgeom.1.smooth hgeom.1.connectedSpace
  let := smoothChartedSpace F V hV
  have hcl : IsClosedImmersion jV.hom.hom.left := Standard.isClosedSubgroup_unipotentHom iL ν (S ∩ M)
  have hStd : SubgroupFunctor.range jV = standardUnipotent iL ν (simpleRelativeRoots iL ν \ {α}) :=
    (Standard.isRepresentedBy_unipotentHom iL ν (S ∩ M)).2.trans
      (congrArg (standardUnipotent iL ν) hVM)
  obtain ⟨n, Q, hQ₀, hQs, hConj⟩ := adelicMaximalUnipotentContraction iL ν (𝟙 T) jV hV
    hRed hiL hνL α hαL hcl hStd
  let archMap := V.affinePointsTarget (jV ≫ jL) (CommAlgCat.of F (InfiniteAdeleRing F))
  let Ψ : (Fin n → mixedEmbedding.mixedSpace F) → G∞ := archMap ∘ Q.symm
  have hΨ : ContMDiff 𝓘(ℝ, Fin n → mixedEmbedding.mixedSpace F) IG ∞ Ψ := by
    have hj : ContMDiff 𝓘(ℝ, smoothModel F dV) IG ∞ archMap := by
      apply (contMDiff_iff_coordinateSmooth F G 𝓘(ℝ, smoothModel F dV) hSmooth _).mpr
      exact ((contMDiff_iff_coordinateSmooth F V 𝓘(ℝ, smoothModel F dV) hV id).mp
        contMDiff_id).postcomp (jV ≫ jL).hom.hom
    exact hj.comp hQs
  have hΨ₀ : Ψ 0 = 1 := by
    change archMap (Q.symm 0) = 1
    rw [← hQ₀, Q.symm_apply_apply, map_one]
  have hΨnorm : ∀ v, ofInfinite F G (Ψ v) ∈ normOneSubgroup F G := by
    let : IsClosedImmersion jV.hom.hom.left := hcl
    let : IsClosedImmersion jL.hom.hom.left := Standard.isClosedSubgroup_leviHom i ν S
    let : IsClosedImmersion (jV ≫ jL).hom.hom.left := by
      rw [Grp.comp_hom_hom]
      change IsClosedImmersion (jV.hom.hom.left ≫ jL.hom.hom.left)
      infer_instance
    intro v
    exact ofInfinite_unipotent_image_mem_normOne (jV ≫ jL) hgeom.1.smooth hgeom.1.connectedSpace
      hgeom.1.isUnipotent (Q.symm v)
  refine ⟨n, Ψ, hΨ₀, hΨ, ?_, hΨnorm⟩
  let aL (a : Ch(S, b)) := positiveMap F L T iL T (𝟙 T) a.val
  have haL (x : Ch(S, b)) : map F L G jL (aL x) = aG x.val := by
    change map F L G jL (map F T.toGrp L (CommGroupScheme.groupHom (𝟙 T) ≫ iL) x.val.val) =
      map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ i) x.val.val
    rw [map_comp_point, Category.assoc, standardLeviTorusFactor_comp]
  have hfin (x : Ch(S, b)) : finite F L (aL x) = 1 :=
    finite_positiveMap F L T iL T (𝟙 T) hi.isSplitSubtorus.1 x.val
  have haCh (x : Ch(S, b)) : x.val ∈ weakSimpleRootChamber F T T (𝟙 T) L iL ν b := by
    intro β hβ
    exact x.prop β (hΔL ▸ hβ)
  have hContraction := hasUnipotentContractionModulo_of_compact_factors
    (j(M)) jL jV (j(S)) Q Ω hΩ
    (fun _ hp => minimalParabolic_le_normalizer_standardRadical hG hi hν M hM (hΩP hp))
    (fun _ hp => minimalParabolic_le_normalizer_standardRadical hG hi hν S hS (hΩP hp))
    (standardLevi_adelic_range_le_normalizer F G T i ν S) aL hfin
    (fun x => relativeCharacterDecay (𝟙 T) α x.val)
    (adelicStandardLeviUnipotentFactors hG hi hν S M hS hM) (fun B hB => by
      obtain ⟨C, hC, hh⟩ := hConj B hB b
      exact ⟨C, hC, fun y hy x => hh y hy x.val (haCh x)⟩)
  have haEq : (fun x : Ch(S, b) => map F L G jL (aL x)) = (fun x : Ch(S, b) => aG x.val) := funext haL
  rw [haEq] at hContraction
  exact hContraction

include hG hi hν in
/-- The standard Levi contraction modulo the outer radical as an estimate
for functions on the ambient adelic group. -/
theorem exists_standardLeviContractionModulo
    (S : Set (characterLattice T)) (hS : S ⊆ Δ) (α : characterLattice T) (hα : α ∈ S)
    (b : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ A₀) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffine (U(Δ \ {α})).X.left := @isAffine_of_isAffineHom _ _ (U(Δ \ {α})).X.hom
      (Standard.isClosedSubgroup_unipotentHom i ν (Δ \ {α})).isAffineHom_source inferInstance
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hSmooth
    ∃ (n : ℕ) (Ψ : (Fin n → mixedEmbedding.mixedSpace F) → G∞),
      Ψ 0 = 1 ∧ ContMDiff 𝓘(ℝ, Fin n → mixedEmbedding.mixedSpace F) IG ∞ Ψ ∧
      HasUnipotentContractionModulo (j(Δ \ {α})) Ω
        (fun a : Ch(S, b) => aG a.val) N(S) Ψ (fun a => relativeCharacterDecay (𝟙 T) α a.val) := by
  obtain ⟨n, Ψ, hΨ₀, hΨ, hContraction, _⟩ :=
    exists_standardLeviContractionModulo_normOne hG hi hν hSmooth S hS α hα b Ω hΩ hΩP
  exact ⟨n, Ψ, hΨ₀, hΨ, hContraction⟩

end Standard

end Langlands.Global
