import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.GroupScheme.Rational.StandardParabolicOrderReduction
import Langlands.Geometry.Building.SpecialCompactLevi

/-! # Compact-open normal bases on the actual standard Levi schemes

A compact-open normal basis `B` of `G(F)` whose literal intersections with the standard Levi
subgroups are inherited bases gives, by taking literal preimages under the closed immersion
`M_J → G`, a compact-open normal basis of the rational points of the Levi scheme
`Standard.leviScheme i ν J`, relative to `leviSchemeCompact K0 i ν J`. Its literal intersections
with the standard Levi subgroups of the Levi scheme are again inherited bases.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {H : Type*} [Group H] {G : Type*} [Group G] {G' : Type*} [Group G']

/-- The literal preimages `f⁻¹(K)`, `K ∈ B`, of a family of subgroups. -/
def comapFamily (f : H →* G) (B : Set (Subgroup G)) : Set (Subgroup H) :=
  {L | ∃ K ∈ B, L = K.comap f}

theorem mem_comapFamily {f : H →* G} {B : Set (Subgroup G)} {L : Subgroup H} :
    L ∈ comapFamily f B ↔ ∃ K ∈ B, L = K.comap f :=
  Iff.rfl

/-- The inherited family is the preimage family under the subgroup inclusion. -/
theorem intersectionFamily_eq_comapFamily (M : Subgroup G) (B : Set (Subgroup G)) :
    intersectionFamily M B = comapFamily M.subtype B :=
  rfl

theorem comapFamily_comapFamily (f : G →* G') (g : H →* G) (B : Set (Subgroup G')) :
    comapFamily g (comapFamily f B) = comapFamily (f.comp g) B := by
  ext L
  constructor
  · rintro ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    exact ⟨K, hK, Subgroup.comap_comap K f g⟩
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K.comap f, ⟨K, hK, rfl⟩, (Subgroup.comap_comap K f g).symm⟩

variable [TopologicalSpace H] [TopologicalSpace G]

/-- Literal preimages along a topological group isomorphism carry a compact-open normal basis
relative to `K0` to one relative to the preimage of `K0`. -/
theorem CompactOpenNormalBasis.comap_continuousMulEquiv (e : H ≃ₜ* G)
    {K0 : Subgroup G} {B : Set (Subgroup G)} (hB : CompactOpenNormalBasis K0 B) :
    CompactOpenNormalBasis (K0.comap e.toMulEquiv.toMonoidHom)
      (comapFamily e.toMulEquiv.toMonoidHom B) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨K, hK, rfl⟩
    obtain ⟨hle, hnorm, ho, hc⟩ := hB.1 K hK
    refine ⟨Subgroup.comap_mono hle, ?_, ho.preimage e.continuous,
      e.toHomeomorph.isCompact_preimage.mpr hc⟩
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.comap_mono hle)]
    rw [Subgroup.normal_subgroupOf_iff hle] at hnorm
    intro h k hh hk
    have := hnorm _ _ hh hk
    show e.toMulEquiv.toMonoidHom (k * h * k⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact this
  · have h0 : (𝓝 (1 : H)) = comap e (𝓝 (1 : G)) := by
      rw [e.toHomeomorph.isInducing.nhds_eq_comap 1]
      simp
      rfl
    have hb := hB.2.comap e
    rw [← h0] at hb
    rw [Filter.hasBasis_iff]
    intro t
    rw [hb.mem_iff]
    constructor
    · rintro ⟨K, hK, ht⟩
      exact ⟨K.comap e.toMulEquiv.toMonoidHom, ⟨K, hK, rfl⟩, ht⟩
    · rintro ⟨_, ⟨K, hK, rfl⟩, ht⟩
      exact ⟨K, hK, ht⟩

end Groups

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] Langlands.HarishChandraSchwartz.rationalWeightsIsAffine
  Langlands.HarishChandraSchwartz.rationalWeightsTopology
  Langlands.HarishChandraSchwartz.rationalWeightsTopologicalGroup

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

local instance leviBasisTransportAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  Langlands.HarishChandraSchwartz.leviScheme_isAffineHom i ν J
local instance leviBasisTransportFiniteType :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  Langlands.HarishChandraSchwartz.leviScheme_locallyOfFiniteType i ν J
local instance leviBasisTransportAffine : IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

/-- The basis on the Levi scheme: the literal preimages `j⁻¹(K)`, `K ∈ B`, under the closed
immersion `j : M_J → G`. Its members are exactly `leviSchemeCompact K i ν J` for `K ∈ B`. -/
def leviSchemeBasis (B : Set (Subgroup (rationalPoints G))) :
    Set (Subgroup (rationalPoints (Standard.leviScheme i ν J))) :=
  comapFamily (rationalPoints.map (Standard.leviHom i ν J)) B

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem mem_leviSchemeBasis {B : Set (Subgroup (rationalPoints G))}
    {L : Subgroup (rationalPoints (Standard.leviScheme i ν J))} :
    L ∈ leviSchemeBasis i ν J B ↔
      ∃ K ∈ B, L = Langlands.HarishChandraSchwartz.leviSchemeCompact K i ν J :=
  Iff.rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- **The basis on the Levi scheme.** If the literal intersections of `B` with `M_J(F)` form an
inherited compact-open normal basis relative to `K0 ∩ M_J(F)`, then `leviSchemeBasis i ν J B`
is a compact-open normal basis of the rational points of the Levi scheme relative to
`leviSchemeCompact K0 i ν J`. -/
theorem compactOpenNormalBasis_leviScheme {K0 : Subgroup (rationalPoints G)}
    {B : Set (Subgroup (rationalPoints G))}
    (hB : InheritedCompactOpenNormalBasis K0 (standardLeviPoints i ν J) B) :
    CompactOpenNormalBasis (Langlands.HarishChandraSchwartz.leviSchemeCompact K0 i ν J)
      (leviSchemeBasis i ν J B) := by
  have h := CompactOpenNormalBasis.comap_continuousMulEquiv
    (Langlands.HarishChandraSchwartz.leviSchemePointsEquiv i ν J) hB
  have hcomp : (standardLeviPoints i ν J).subtype.comp
      (Langlands.HarishChandraSchwartz.leviSchemePointsEquiv i ν J).toMulEquiv.toMonoidHom =
        rationalPoints.map (Standard.leviHom i ν J) :=
    MonoidHom.ext fun _ => rfl
  rw [intersectionFamily_eq_comapFamily, comapFamily_comapFamily, hcomp, Subgroup.comap_comap,
    hcomp] at h
  exact h

variable {i ν J}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- For `R ⊆ J ⊆ Δ`, a point of the Levi scheme lies in its standard Levi subgroup for `R` if and
only if its image lies in `M_R(F)`. -/
theorem mem_standardLeviPoints_leviTorusHom_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {R : Set (characterLattice S)} (hRJ : R ⊆ J)
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    x ∈ standardLeviPoints (Standard.leviTorusHom i ν J) ν R ↔
      rationalPoints.map (Standard.leviHom i ν J) x ∈ standardLeviPoints i ν R := by
  have hL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  obtain ⟨-, -, hfam⟩ :=
    standardLeviStandardFamilies dynamicLie standardCocharacter F G hG S i hi ν hν J hJ
      (Standard.leviScheme i ν J) hL (Standard.leviHom i ν J)
      (Standard.isRepresentedBy_leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)
  have h : standardLevi (Standard.leviTorusHom i ν J) ν R =
      (standardLevi i ν R).comap (Standard.leviHom i ν J) := (hfam R hRJ).2.1
  change x ∈ (standardLevi (Standard.leviTorusHom i ν J) ν R).carrier _ ↔ _
  rw [h]
  exact SubgroupFunctor.mem_comap

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The simple roots of the Levi torus of `M_J` are exactly `J`. -/
theorem simpleRelativeRoots_leviTorusHom_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    simpleRelativeRoots (Standard.leviTorusHom i ν J) ν = J := by
  have hL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  exact (standardLeviStandardFamilies dynamicLie standardCocharacter F G hG S i hi ν hν J hJ
      (Standard.leviScheme i ν J) hL (Standard.leviHom i ν J)
      (Standard.isRepresentedBy_leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)).1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- For `R ⊆ J ⊆ Δ`, `M_R(F) ⊆ M_J(F)`. -/
theorem standardLeviPoints_le_of_subset (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {R : Set (characterLattice S)} (hRJ : R ⊆ J) :
    standardLeviPoints i ν R ≤ standardLeviPoints i ν J := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hle : standardLevi i ν R ≤ standardLevi i ν J :=
    standardLevi_mono_of_exists i ν hRJ
      (standardCocharacter F G hG S i hi ν hν R (hRJ.trans hJ)).1
  exact SubgroupFunctor.le_def.mp hle _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- For `R ⊆ J ⊆ Δ`, the inclusion `M_J → G` identifies the standard Levi subgroup of the Levi
scheme for `R` with `M_R(F)`, as topological groups with their subspace topologies. -/
def leviSchemeStandardLeviEquiv (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {R : Set (characterLattice S)} (hRJ : R ⊆ J) :
    standardLeviPoints (Standard.leviTorusHom i ν J) ν R ≃ₜ* standardLeviPoints i ν R where
  toFun x := ⟨rationalPoints.map (Standard.leviHom i ν J) x,
    (mem_standardLeviPoints_leviTorusHom_iff hG hi hν hJ hRJ x).1 x.2⟩
  invFun y := ⟨(Langlands.HarishChandraSchwartz.leviSchemePointsEquiv i ν J).symm
      ⟨y, standardLeviPoints_le_of_subset hG hi hν hJ hRJ y.2⟩,
    (mem_standardLeviPoints_leviTorusHom_iff hG hi hν hJ hRJ _).2 (by
      rw [Langlands.HarishChandraSchwartz.map_leviSchemePointsEquiv_symm]
      exact y.2)⟩
  left_inv x := Subtype.ext (by
    apply Langlands.HarishChandraSchwartz.map_leviHom_injective
    rw [Langlands.HarishChandraSchwartz.map_leviSchemePointsEquiv_symm])
  right_inv y := Subtype.ext
    (Langlands.HarishChandraSchwartz.map_leviSchemePointsEquiv_symm i ν J _)
  map_mul' a b := Subtype.ext (map_mul (rationalPoints.map (Standard.leviHom i ν J))
    (a : rationalPoints (Standard.leviScheme i ν J)) (b : rationalPoints (Standard.leviScheme i ν J)))
  continuous_toFun :=
    ((Langlands.HarishChandraSchwartz.continuous_map_leviHom i ν J).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((Langlands.HarishChandraSchwartz.leviSchemePointsEquiv i ν J).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem leviSchemeStandardLeviEquiv_apply_coe (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {R : Set (characterLattice S)} (hRJ : R ⊆ J)
    (x : standardLeviPoints (Standard.leviTorusHom i ν J) ν R) :
    ((leviSchemeStandardLeviEquiv hG hi hν hJ hRJ x : standardLeviPoints i ν R) :
        rationalPoints G) =
      rationalPoints.map (Standard.leviHom i ν J) x :=
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- **The inherited bases on the Levi scheme.** For `R ⊆ J ⊆ Δ`, if the literal intersections of
`B` with `M_R(F)` form an inherited compact-open normal basis relative to `K0 ∩ M_R(F)`, then the
literal intersections of `leviSchemeBasis i ν J B` with the standard Levi subgroup of the Levi
scheme for `R` form an inherited compact-open normal basis relative to
`leviSchemeCompact K0 i ν J`. -/
theorem inheritedCompactOpenNormalBasis_leviScheme (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {R : Set (characterLattice S)} (hRJ : R ⊆ J)
    {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
    (hB : InheritedCompactOpenNormalBasis K0 (standardLeviPoints i ν R) B) :
    InheritedCompactOpenNormalBasis (Langlands.HarishChandraSchwartz.leviSchemeCompact K0 i ν J)
      (standardLeviPoints (Standard.leviTorusHom i ν J) ν R) (leviSchemeBasis i ν J B) := by
  have h := CompactOpenNormalBasis.comap_continuousMulEquiv
    (leviSchemeStandardLeviEquiv hG hi hν hJ hRJ) hB
  have hcomp : (standardLeviPoints i ν R).subtype.comp
      (leviSchemeStandardLeviEquiv hG hi hν hJ hRJ).toMulEquiv.toMonoidHom =
        (rationalPoints.map (Standard.leviHom i ν J)).comp
          (standardLeviPoints (Standard.leviTorusHom i ν J) ν R).subtype :=
    MonoidHom.ext fun _ => rfl
  rw [intersectionFamily_eq_comapFamily, comapFamily_comapFamily, hcomp, Subgroup.comap_comap,
    hcomp] at h
  unfold InheritedCompactOpenNormalBasis leviSchemeBasis
    Langlands.HarishChandraSchwartz.leviSchemeCompact
  rw [intersectionFamily_eq_comapFamily, comapFamily_comapFamily, Subgroup.comap_comap]
  exact h

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The two basis clauses of `SimultaneousStandardBasisAt` for the Levi scheme, from the
inherited clauses of the ambient basis: `leviSchemeBasis i ν J B` is a compact-open normal basis
relative to `leviSchemeCompact K0 i ν J`, and its literal intersections with every standard Levi
subgroup of the Levi scheme are inherited bases. -/
theorem leviSchemeBasis_basisClauses (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
    (hB : ∀ R : Set (characterLattice S), R ⊆ simpleRelativeRoots i ν →
      InheritedCompactOpenNormalBasis K0 (standardLeviPoints i ν R) B) :
    CompactOpenNormalBasis (Langlands.HarishChandraSchwartz.leviSchemeCompact K0 i ν J)
        (leviSchemeBasis i ν J B) ∧
      ∀ R : Set (characterLattice S), R ⊆ simpleRelativeRoots (Standard.leviTorusHom i ν J) ν →
        InheritedCompactOpenNormalBasis
          (Langlands.HarishChandraSchwartz.leviSchemeCompact K0 i ν J)
          (standardLeviPoints (Standard.leviTorusHom i ν J) ν R) (leviSchemeBasis i ν J B) := by
  refine ⟨compactOpenNormalBasis_leviScheme i ν J (hB J hJ), fun R hR => ?_⟩
  rw [simpleRelativeRoots_leviTorusHom_eq hG hi hν hJ] at hR
  exact inheritedCompactOpenNormalBasis_leviScheme hG hi hν hJ hR (hB R (hR.trans hJ))

end Rational

end Langlands.BruhatTits.SpecialCompact
