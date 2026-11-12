import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.Geometry.Building.SpecialCompactLeviMinimalParabolicStatement
import Langlands.GroupScheme.Rational.StandardLeviPointHomeomorph
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.Representation.Aubert.General.Conjugation

/-! # The actual standard Levi subgroups as group schemes

For a connected reductive `G` over a nonarchimedean local field, a maximal split torus `i`, a
generic cocharacter `ν` and `J ⊆ Δ`, the Levi group scheme `L = Standard.leviScheme i ν J` (with its
closed embedding `j`) is connected reductive, `ν` is generic for its maximal split torus, its
minimal standard parabolic and radical are the preimages of `P₀` and `U₀`, its modulus `δ₀` is
`δ₀^{M_J}`, its spherical function `Ξ` for `j⁻¹(K)` is `Ξ^{M_J}` read through `j`
(`rationalXi_leviScheme`), and the height of `ρ ∘ j` is `σ` restricted to `M_J(F)`. The abstract
lemmas `iwasawaWeight_map` and `xi_map` transport `Ξ` along topological group isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Transport

variable {H H' : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [MeasurableSpace H'] [BorelSpace H']
  (e : H ≃ₜ* H') {P K : Subgroup H} {P' K' : Subgroup H'}
  {hPK : IsIwasawaPair P K} {hPK' : IsIwasawaPair P' K'}
  {δ : P →* ℝ≥0ˣ} {δ' : P' →* ℝ≥0ˣ}

omit [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H']
  [MeasurableSpace H'] [BorelSpace H'] in
include e in
/-- Transport of the Iwasawa weight along a topological group isomorphism matching the
subgroups and the characters. -/
theorem iwasawaWeight_map (hδ' : ∀ p : P', (p : H') ∈ K' → δ' p = 1)
    (hP : ∀ p : H, p ∈ P → e p ∈ P') (hK : ∀ k : H, k ∈ K → e k ∈ K')
    (hδ : ∀ p : P, δ' ⟨e p, hP p p.2⟩ = δ p) (g : H) :
    iwasawaWeight hPK' δ' (e g) = iwasawaWeight hPK δ g := by
  obtain ⟨k, hk, hg⟩ := exists_iwasawaFactor hPK g
  have h1 : e g = e (iwasawaFactor hPK g : H) * e k := by
    conv_lhs => rw [hg]
    exact map_mul e _ _
  rw [h1, iwasawaWeight_mul hδ' (hP _ (iwasawaFactor hPK g).2) (hK k hk), hδ]
  rfl

/-- The restriction of `e` to subgroups that it matches. -/
def subgroupContinuousMulEquiv (hK : ∀ k : H, k ∈ K ↔ e k ∈ K') : K ≃ₜ* K' where
  toFun k := ⟨e k, (hK k).1 k.2⟩
  invFun k := ⟨e.symm k, (hK _).2 (by simp)⟩
  left_inv k := Subtype.ext (by simp)
  right_inv k := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (map_mul e _ _)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

include e in
/-- **Transport of `Ξ`** along a topological group isomorphism `e : H ≃ₜ* H'` with
`e(P) = P'`, `e(K) = K'` and `δ' ∘ e = δ`: `Ξ'(e g) = Ξ(g)`. -/
theorem xi_map [CompactSpace K] [CompactSpace K'] (hδ' : ∀ p : P', (p : H') ∈ K' → δ' p = 1)
    (hP : ∀ p : H, p ∈ P → e p ∈ P') (hK : ∀ k : H, k ∈ K ↔ e k ∈ K')
    (hδ : ∀ p : P, δ' ⟨e p, hP p p.2⟩ = δ p) (g : H) :
    xi hPK' δ' (e g) = xi hPK δ g := by
  set eK := subgroupContinuousMulEquiv e hK
  set φ := eK.toHomeomorph.toMeasurableEquiv
  have hmap : (normalizedHaar K).map φ = normalizedHaar K' := by
    have : ((normalizedHaar K).map φ).IsHaarMeasure := eK.isHaarMeasure_map _
    have : IsProbabilityMeasure ((normalizedHaar K).map φ) :=
      (Measure.isProbabilityMeasure_map_iff φ.measurable.aemeasurable).mpr inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  unfold xi
  rw [← hmap, integral_map_equiv φ]
  congr 1
  funext k
  change iwasawaWeight hPK' δ' ((e k : H') * e g) = iwasawaWeight hPK δ ((k : H) * g)
  rw [← map_mul e]
  exact iwasawaWeight_map e hδ' hP (fun k hk => (hK k).1 hk) hδ _

end Transport

section Scheme

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- The actual standard Levi scheme is affine over `F`. -/
theorem leviScheme_isAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

/-- The actual standard Levi scheme is locally of finite type when `G` is. -/
theorem leviScheme_locallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).locallyOfFiniteType

variable {i ν J}

/-- `ν` is generic for the torus of the Levi scheme: its relative roots are relative roots of
`G` (`relativeRoots_subset_of_factor`). -/
theorem isGenericCocharacter_leviTorusHom (hν : IsGenericCocharacter i ν) :
    haveI := leviScheme_isAffineHom i ν J
    IsGenericCocharacter (Standard.leviTorusHom i ν J) ν := by
  have := leviScheme_isAffineHom i ν J
  exact fun α hα => hν α (relativeRoots_subset_of_factor (Standard.isRepresentedBy_leviHom i ν J)
    _ (Standard.leviTorusHom_comp i ν J) hα)

/-- The minimal standard parabolic of the Levi scheme is the preimage of `P₀`. -/
theorem standardParabolic_leviTorusHom_empty (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    haveI := leviScheme_isAffineHom i ν J
    standardParabolic (Standard.leviTorusHom i ν J) ν ∅ =
      (standardParabolic i ν ∅).comap (Standard.leviHom i ν J) := by
  have := leviScheme_isAffineHom i ν J
  have := hi.isSplitSubtorus.mono
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have := hiL.isSplitSubtorus.mono
  obtain ⟨-, hcG⟩ := standardCocharacter F G hG S i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨hPG, -, -⟩ := hcG ν (isStandardCocharacter_empty_self i ν)
  obtain ⟨-, hcL⟩ := standardCocharacter F _ (Langlands.BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν J hJ) S
    _ hiL ν (isGenericCocharacter_leviTorusHom hν) ∅ (Set.empty_subset _)
  obtain ⟨hPL, -, -⟩ := hcL ν (isStandardCocharacter_empty_self _ ν)
  rw [hPL]
  exact Standard.leviGenericParabolic_eq_comap_standard i ν J hPG

/-- The radical of the minimal standard parabolic of the Levi scheme is the preimage of `U₀`. -/
theorem standardUnipotent_leviTorusHom_empty (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    haveI := leviScheme_isAffineHom i ν J
    standardUnipotent (Standard.leviTorusHom i ν J) ν ∅ =
      (standardUnipotent i ν ∅).comap (Standard.leviHom i ν J) := by
  have := leviScheme_isAffineHom i ν J
  have := hi.isSplitSubtorus.mono
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have := hiL.isSplitSubtorus.mono
  obtain ⟨-, hcG⟩ := standardCocharacter F G hG S i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨-, -, hUG⟩ := hcG ν (isStandardCocharacter_empty_self i ν)
  obtain ⟨-, hcL⟩ := standardCocharacter F _ (Langlands.BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν J hJ) S
    _ hiL ν (isGenericCocharacter_leviTorusHom hν) ∅ (Set.empty_subset _)
  obtain ⟨-, -, hUL⟩ := hcL ν (isStandardCocharacter_empty_self _ ν)
  rw [hUL, hUG, Dynamic.unipotent_eq_comap_of_isClosedSubgroup _ _
    (Standard.isClosedSubgroup_leviHom i ν J)]
  simp only [Category.assoc, Standard.leviTorusHom_comp]

end Scheme

section Points

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance leviIsAffineHom (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance leviLocallyOfFiniteType (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- The rational points of the Levi scheme `L = Standard.leviScheme i ν J`, with their canonical
topology, are the actual standard Levi subgroup `M_J(F)` of `G(F)` with the subspace topology
(the Library's `standardLeviRationalPointsHomeomorph`); the map is `x ↦ j(x)`. -/
def leviSchemePointsEquiv :
    rationalPoints (Standard.leviScheme i ν J) ≃ₜ* standardLeviPoints i ν J :=
  standardLeviRationalPointsHomeomorph i ν J (Standard.leviHom i ν J)
    (Standard.isRepresentedBy_leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem leviSchemePointsEquiv_coe (x : rationalPoints (Standard.leviScheme i ν J)) :
    ((leviSchemePointsEquiv i ν J x : standardLeviPoints i ν J) : rationalPoints G) =
      rationalPoints.map (Standard.leviHom i ν J) x :=
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
theorem continuous_map_leviHom :
    Continuous (rationalPoints.map (Standard.leviHom i ν J)) :=
  continuous_subtype_val.comp (leviSchemePointsEquiv i ν J).continuous

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem map_leviSchemePointsEquiv_symm (m : standardLeviPoints i ν J) :
    rationalPoints.map (Standard.leviHom i ν J) ((leviSchemePointsEquiv i ν J).symm m) = m :=
  congrArg Subtype.val ((leviSchemePointsEquiv i ν J).apply_symm_apply m)

variable {i ν J}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- A point of the Levi scheme lies in its minimal standard parabolic if and only if its image
lies in `P₀(F)`. -/
theorem mem_standardParabolicPoints_leviTorusHom_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (x : rationalPoints (Standard.leviScheme i ν J)) :
    x ∈ standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅ ↔
      rationalPoints.map (Standard.leviHom i ν J) x ∈ standardParabolicPoints i ν ∅ := by
  have h := standardParabolic_leviTorusHom_empty hG hi hν hJ
  change x ∈ (standardParabolic (Standard.leviTorusHom i ν J) ν ∅).carrier _ ↔ _
  rw [h]
  exact SubgroupFunctor.mem_comap

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- A point of the Levi scheme lies in the radical of its minimal standard parabolic if and only
if its image lies in `U₀(F)`. -/
theorem mem_standardUnipotentPoints_leviTorusHom_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (x : rationalPoints (Standard.leviScheme i ν J)) :
    x ∈ standardUnipotentPoints (Standard.leviTorusHom i ν J) ν ∅ ↔
      rationalPoints.map (Standard.leviHom i ν J) x ∈ standardUnipotentPoints i ν ∅ := by
  have h := standardUnipotent_leviTorusHom_empty hG hi hν hJ
  change x ∈ (standardUnipotent (Standard.leviTorusHom i ν J) ν ∅).carrier _ ↔ _
  rw [h]
  exact SubgroupFunctor.mem_comap

/-- The radical of the minimal standard parabolic of the Levi scheme is `M_J(F) ∩ U₀(F)`, as
topological groups. -/
def leviSchemeUnipotentEquiv (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardUnipotentPoints (Standard.leviTorusHom i ν J) ν ∅ ≃ₜ*
      (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅ :
        Subgroup (rationalPoints G)) where
  toFun u := ⟨rationalPoints.map (Standard.leviHom i ν J) u,
    Subgroup.mem_inf.mpr ⟨(leviSchemePointsEquiv i ν J u).2,
      (mem_standardUnipotentPoints_leviTorusHom_iff hG hi hν hJ u).1 u.2⟩⟩
  invFun v := ⟨(leviSchemePointsEquiv i ν J).symm ⟨v, (Subgroup.mem_inf.mp v.2).1⟩,
    (mem_standardUnipotentPoints_leviTorusHom_iff hG hi hν hJ _).2 (by
      rw [map_leviSchemePointsEquiv_symm]
      exact (Subgroup.mem_inf.mp v.2).2)⟩
  left_inv u := Subtype.ext ((leviSchemePointsEquiv i ν J).symm_apply_apply u)
  right_inv v := Subtype.ext (by
    change (((leviSchemePointsEquiv i ν J)
      ((leviSchemePointsEquiv i ν J).symm ⟨v, (Subgroup.mem_inf.mp v.2).1⟩) :
        standardLeviPoints i ν J) : rationalPoints G) = v
    rw [ContinuousMulEquiv.apply_symm_apply])
  map_mul' u v := Subtype.ext (map_mul (rationalPoints.map (Standard.leviHom i ν J))
    (u : rationalPoints (Standard.leviScheme i ν J)) (v : rationalPoints (Standard.leviScheme i ν J)))
  continuous_toFun := ((continuous_map_leviHom i ν J).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((leviSchemePointsEquiv i ν J).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem leviSchemeUnipotentEquiv_apply_coe (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (u : standardUnipotentPoints (Standard.leviTorusHom i ν J) ν ∅) :
    ((leviSchemeUnipotentEquiv hG hi hν hJ u : (standardLeviPoints i ν J ⊓
      standardUnipotentPoints i ν ∅ : Subgroup (rationalPoints G))) : rationalPoints G) =
      rationalPoints.map (Standard.leviHom i ν J) u :=
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem map_leviSchemeUnipotentEquiv_symm_apply (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (v : (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅ :
      Subgroup (rationalPoints G))) :
    rationalPoints.map (Standard.leviHom i ν J)
        ((leviSchemeUnipotentEquiv hG hi hν hJ).symm v :
          rationalPoints (Standard.leviScheme i ν J)) = v := by
  have h := congrArg (fun w : (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅ :
      Subgroup (rationalPoints G)) => (w : rationalPoints G))
    ((leviSchemeUnipotentEquiv hG hi hν hJ).apply_symm_apply v)
  exact h

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
theorem map_leviHom_injective :
    Function.Injective (rationalPoints.map (Standard.leviHom i ν J)) := fun _ _ h =>
  (leviSchemePointsEquiv i ν J).injective (Subtype.ext h)

/-- **The modulus `δ₀` of the Levi scheme is `δ₀^{M_J}`**: for `p` in the minimal standard
parabolic of the Levi scheme, the Haar modulus of conjugation by `p` on its radical equals the Haar
modulus of conjugation by `j(p)` on `M_J(F) ∩ U₀(F)`. -/
theorem standardLeviMinimalModulus_leviHom (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (p : standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅) :
    standardLeviMinimalModulus i ν J ⟨rationalPoints.map (Standard.leviHom i ν J) p,
      Subgroup.mem_inf.mpr ⟨(mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ p).1 p.2,
        (leviSchemePointsEquiv i ν J p).2⟩⟩ =
      rationalMinimalModulus (Standard.leviTorusHom i ν J) ν p := by
  set eU := leviSchemeUnipotentEquiv hG hi hν hJ
  have hUL := isClosed_standardUnipotentPoints (Standard.leviTorusHom i ν J) ν ∅
  have hUG := (isClosed_standardLeviPoints i ν J).inter (isClosed_standardUnipotentPoints i ν ∅)
  let : LocallyCompactSpace (standardUnipotentPoints (Standard.leviTorusHom i ν J) ν ∅) :=
    hUL.locallyCompactSpace
  let : LocallyCompactSpace (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅ :
      Subgroup (rationalPoints G)) := hUG.locallyCompactSpace
  let : MeasurableSpace (standardUnipotentPoints (Standard.leviTorusHom i ν J) ν ∅) := borel _
  have : BorelSpace (standardUnipotentPoints (Standard.leviTorusHom i ν J) ν ∅) := ⟨rfl⟩
  let : MeasurableSpace (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅ :
      Subgroup (rationalPoints G)) := borel _
  have : BorelSpace (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅ :
      Subgroup (rationalPoints G)) := ⟨rfl⟩
  apply Units.ext
  unfold standardLeviMinimalModulus rationalMinimalModulus
  simp only [HaarModulus.closedRestrictCharacter, HaarModulus.closedNormalizerCharacter,
    MonoidHom.coe_comp, Function.comp_apply, HaarModulus.normalizerCharacter_apply]
  rw [← Aubert.General.mulEquivHaarChar_trans_symm eU]
  congr 1
  refine ContinuousMulEquiv.ext fun u => Subtype.ext ?_
  apply map_leviHom_injective
  simp only [ContinuousMulEquiv.trans_apply, eU, map_leviSchemeUnipotentEquiv_symm_apply,
    HaarModulus.normalizerConj_apply, leviSchemeUnipotentEquiv_apply_coe, map_mul, map_inv]
  rfl

section Compact

variable (K : Subgroup (rationalPoints G))

/-- **The compact subgroup of the Levi scheme**: the preimage `j⁻¹(K)` of a subgroup `K` of
`G(F)` in the rational points of the Levi scheme, i.e. `K ∩ M_J(F)` read on the Levi scheme
(Waldspurger I.1: "le groupe `M ∩ K` vérifie relativement à `M` les mêmes propriétés que `K`
relativement à `G`"). -/
def leviSchemeCompact (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : Subgroup (rationalPoints (Standard.leviScheme i ν J)) :=
  K.comap (rationalPoints.map (Standard.leviHom i ν J))

variable {K}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
theorem mem_leviSchemeCompact_iff (x : rationalPoints (Standard.leviScheme i ν J)) :
    x ∈ leviSchemeCompact K i ν J ↔ leviSchemePointsEquiv i ν J x ∈ K.subgroupOf
      (standardLeviPoints i ν J) :=
  Iff.rfl

omit [LocallyOfFiniteType G.X.hom] in
theorem compactSpace_leviSchemeCompact (hKc : IsCompact (K : Set (rationalPoints G))) :
    CompactSpace (leviSchemeCompact K i ν J) := by
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  exact (subgroupContinuousMulEquiv (leviSchemePointsEquiv i ν J)
    mem_leviSchemeCompact_iff).toHomeomorph.symm.compactSpace

omit [LocallyOfFiniteType G.X.hom] in
theorem isCompact_leviSchemeCompact (hKc : IsCompact (K : Set (rationalPoints G))) :
    IsCompact (leviSchemeCompact K i ν J : Set (rationalPoints (Standard.leviScheme i ν J))) := by
  have := compactSpace_leviSchemeCompact (i := i) (ν := ν) (J := J) hKc
  exact isCompact_iff_compactSpace.mpr this

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
theorem isOpen_leviSchemeCompact (hKo : IsOpen (K : Set (rationalPoints G))) :
    IsOpen (leviSchemeCompact K i ν J : Set (rationalPoints (Standard.leviScheme i ν J))) :=
  hKo.preimage (continuous_map_leviHom i ν J)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))` gives the Iwasawa decomposition of the rational
points of the Levi scheme for its minimal standard parabolic and `j⁻¹(K)`. -/
theorem isIwasawaPair_leviSchemeCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J))) :
    IsIwasawaPair (standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅)
      (leviSchemeCompact K i ν J) := by
  intro x
  obtain ⟨p, hp, k, hk, hx⟩ := hM (leviSchemePointsEquiv i ν J x)
  refine ⟨(leviSchemePointsEquiv i ν J).symm p,
    (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ _).2 ?_,
    (leviSchemePointsEquiv i ν J).symm k, ?_, ?_⟩
  · rw [map_leviSchemePointsEquiv_symm]
    exact hp
  · rw [mem_leviSchemeCompact_iff, ContinuousMulEquiv.apply_symm_apply]
    exact hk
  · apply (leviSchemePointsEquiv i ν J).injective
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply, hx]

/-- **`Ξ` of the Levi scheme is `Ξ^{M_J}`**: for the compact subgroup `j⁻¹(K)` of the Levi
scheme, its spherical function `rationalXi` at `x` equals `rationalLeviXi` at `j(x)`. -/
theorem rationalXi_leviScheme (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    rationalXi (isCompact_leviSchemeCompact hKc) (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM)
        x = rationalLeviXi hKc hM (leviSchemePointsEquiv i ν J x) := by
  have := compactSpace_leviSchemeCompact (i := i) (ν := ν) (J := J) hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  unfold rationalXi rationalLeviXi
  refine (xi_map (leviSchemePointsEquiv i ν J)
    (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
    (fun p hp => ?_) (fun k => mem_leviSchemeCompact_iff k) (fun p => ?_) x).symm
  · rw [Subgroup.mem_subgroupOf, leviSchemePointsEquiv_coe]
    exact (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ p).1 hp
  · rw [standardLeviMinimalModulusOf_apply]
    exact standardLeviMinimalModulus_leviHom hG hi hν hJ p

end Compact

section Height

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [Nonempty n] in
/-- The restriction `ρ ∘ j` of a closed matrix representation to the Levi scheme is closed. -/
theorem isClosedSubgroup_restrict_leviHom (hρ : IsClosedSubgroup ρ) :
    IsClosedSubgroup (ρ.restrict (Standard.leviHom i ν J)) :=
  (Standard.isClosedSubgroup_leviHom i ν J).comp hρ

omit [LocallyOfFiniteType G.X.hom] in
/-- **Heights on the Levi scheme**: the height of `ρ ∘ j` at `x` is the height of `ρ` at `j(x)`,
i.e. `σ` restricted to `M_J(F)`. -/
theorem rationalHeight_restrict_leviHom (x : rationalPoints (Standard.leviScheme i ν J)) :
    rationalHeight (F := F) (ρ.restrict (Standard.leviHom i ν J)) x =
      rationalHeight (F := F) ρ (rationalPoints.map (Standard.leviHom i ν J) x) := by
  unfold rationalHeight MatrixRepresentation.rationalMatrixNorm
  rw [MatrixRepresentation.rationalMatrix_restrict]
  rfl

omit [LocallyOfFiniteType G.X.hom] in
/-- `ρ(K) ⊆ GL_n(𝒪)` gives `(ρ ∘ j)(j⁻¹(K)) ⊆ GL_n(𝒪)`. -/
theorem leviSchemeCompact_le_rationalHeightSubgroup {K : Subgroup (rationalPoints G)}
    (hKρ : K ≤ rationalHeightSubgroup (F := F) ρ) :
    leviSchemeCompact K i ν J ≤
      rationalHeightSubgroup (F := F) (ρ.restrict (Standard.leviHom i ν J)) := by
  intro x hx
  rw [mem_rationalHeightSubgroup]
  have h := hKρ hx
  rw [mem_rationalHeightSubgroup] at h
  unfold MatrixRepresentation.rationalMatrixNorm at h ⊢
  rw [MatrixRepresentation.rationalMatrix_restrict]
  exact h

end Height

end Points

end Langlands.HarishChandraSchwartz
