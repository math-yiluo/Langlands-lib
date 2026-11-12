import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalLevi
import Langlands.Representation.Aubert.General.DynamicInductionNormalization

/-! # `Ξ` through a standard Levi subgroup on actual rational points (Lemma II.1.6)

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter, a compact open subgroup `K` with `G(F) = P₀(F) K` and a standard parabolic
`P_J = M_J U_J ⊇ P₀`, this module proves that `δ₀` is trivial on `U₀(F)`, assembles the Library's
`LeviData` for `(K, P₀, P_J, M_J)`, defines Waldspurger's `Ξ^M` for `M = M_J` (`rationalLeviXi`)
and proves Lemma II.1.6: `Ξ(g) = ∫_K δ_{U_J}(m_P(kg))^{1/2} Ξ^{M_J}(m_P(kg)) dk`. The `LeviData`
and the Iwasawa decomposition of `M_J(F)` are first derived for an abstract semidirect
decomposition `P = M ⋉ U` with `P₀ ⊆ P` and `U ⊆ P₀`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalLeviSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalLeviNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `LeviData` for a semidirect decomposition `P = M ⋉ U` with `P₀ ⊆ P` and `U ⊆ P₀`. -/
theorem leviData_of_isSemidirectDecomposition {H : Type*} [Group H] {K P₀ P M U : Subgroup H}
    (h : Aubert.General.IsSemidirectDecomposition P M U) (hP₀ : P₀ ≤ P) (hUP₀ : U ≤ P₀)
    {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
    (hδ₀U : ∀ p : P₀, (p : H) ∈ U → δ₀ p = 1)
    (hδ₀M : ∀ (p : P₀) (hp : (p : H) ∈ M), δ₀ p = δP ⟨p, hp⟩ * δ₀M ⟨⟨p, hp⟩, p.2⟩)
    (hδP : ∀ m : M, (m : H) ∈ K → δP m = 1) :
    LeviData K P₀ P M δ₀ δP δ₀M h.projection where
  le_P₀ := hP₀
  le_M := h.levi_le
  apply_inclusion m := h.projection_levi m
  mem_of_apply_eq_one p hp := hUP₀ ((h.projection_eq_one_iff p).mp hp)
  δ₀_of_apply_eq_one p hp := hδ₀U p ((h.projection_eq_one_iff _).mp hp)
  δ₀_of_mem := hδ₀M
  δP_of_mem := hδP

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `M = (P₀ ∩ M)(K ∩ M)` for a semidirect decomposition `P = M ⋉ U` with `P₀ ⊆ P`, `U ⊆ P₀`,
`G = P₀ K`, when the projection `P → M` maps `P ∩ K` into `K`. -/
theorem isIwasawaPair_of_isSemidirectDecomposition {H : Type*} [Group H]
    {K P₀ P M U : Subgroup H} (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hP₀ : P₀ ≤ P) (hUP₀ : U ≤ P₀) (hP₀K : IsIwasawaPair P₀ K)
    (hmK : ∀ p : P, (p : H) ∈ K → (h.projection p : H) ∈ K) :
    IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M) := by
  refine (leviData_of_isSemidirectDecomposition (K := K) (δ₀ := 1) (δP := 1) (δ₀M := 1) h hP₀
    hUP₀ (fun _ _ => rfl) (fun _ _ => (mul_one 1).symm) (fun _ _ => rfl)).isIwasawaPair hP₀K
    (fun p => ?_) hmK
  have hU : ((h.projection (Subgroup.inclusion hP₀ p) : M) : H)⁻¹ * (p : H) ∈ P₀ :=
    hUP₀ (h.projection_inv_mul_mem (Subgroup.inclusion hP₀ p))
  have e : ((h.projection (Subgroup.inclusion hP₀ p) : M) : H) =
      (p : H) * (((h.projection (Subgroup.inclusion hP₀ p) : M) : H)⁻¹ * (p : H))⁻¹ := by group
  rw [e]
  exact P₀.mul_mem p.2 (P₀.inv_mem hU)

section Unipotent

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- Transport of the unimodularity of a closed subgroup along an equality of subgroups. -/
theorem closedNormalizerCharacter_eq_one_of_eq [TopologicalSpace (rationalPoints G)]
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    {U V : Subgroup (rationalPoints G)} (hUV : U = V)
    (hU : IsClosed (U : Set (rationalPoints G))) (hV : IsClosed (V : Set (rationalPoints G)))
    (h : Aubert.General.IsUnimodularModulus V hV) (u : U) :
    HaarModulus.closedNormalizerCharacter U hU ⟨u, Subgroup.le_normalizer u.2⟩ = 1 := by
  subst hUV
  exact h u

/-- **`δ₀` is trivial on `U₀(F)`**, for connected reductive `G`: `U₀(F)` is the actual dynamic
radical of the generic cocharacter `ν` (the Library's `standardCocharacter` for `J = ∅`), which
is a limit of compact subgroups and hence unimodular (`dynamicUnipotent_isUnimodular`). -/
theorem rationalMinimalModulus_eq_one_of_mem_standardUnipotent (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (p : standardParabolicPoints i ν ∅)
    (hp : (p : rationalPoints G) ∈ standardUnipotentPoints i ν ∅) :
    rationalMinimalModulus i ν p = 1 := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨-, hcompare⟩ := standardCocharacter F G hG S i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨-, -, hU⟩ := hcompare ν (isStandardCocharacter_empty_self i ν)
  set χ := CommGroupScheme.groupHom ν ≫ i
  have hU' : standardUnipotentPoints i ν ∅ =
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
    change (standardUnipotent i ν ∅).carrier _ = _
    rw [hU]
  have hUc : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
      Set (rationalPoints G)) := by
    rw [← hU']
    exact isClosed_standardUnipotentPoints i ν ∅
  have hunimod := Aubert.General.DynamicNormalization.dynamicUnipotent_isUnimodular F G hG χ hUc
  exact closedNormalizerCharacter_eq_one_of_eq hU' (isClosed_standardUnipotentPoints i ν ∅) hUc
    hunimod ⟨p, hp⟩

end Unipotent

section Levi

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- `δ_{U_J}` is trivial on `M_J(F) ∩ K` for every compact open subgroup `K`: conjugation by such
an element preserves the compact open subgroup `K ∩ U_J(F)` of `U_J(F)`. -/
theorem standardUnipotentModulus_eq_one {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (m : standardLeviPoints i ν J) (hm : (m : rationalPoints G) ∈ K) :
    standardUnipotentModulus i ν J m = 1 := by
  have hU : IsClosed (standardUnipotentPoints i ν J : Set (rationalPoints G)) :=
    isClosed_standardUnipotentPoints i ν J
  have : LocallyCompactSpace (standardUnipotentPoints i ν J) := hU.locallyCompactSpace
  let KU : OpenSubgroup (standardUnipotentPoints i ν J) :=
    (⟨K, hKo⟩ : OpenSubgroup (rationalPoints G)).comap (standardUnipotentPoints i ν J).subtype
      continuous_subtype_val
  have hKU : IsCompact (KU : Set (standardUnipotentPoints i ν J)) :=
    hU.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hmn : (m : rationalPoints G) ∈
      Subgroup.normalizer (standardUnipotentPoints i ν J : Set (rationalPoints G)) :=
    standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J m.2
  have h := HaarModulus.normalizerCharacter_eq_one_of_preimage
    (standardUnipotentPoints i ν J) KU hKU ⟨m, hmn⟩ ?_
  · exact h
  · ext u
    change (m : rationalPoints G) * (u : rationalPoints G) * (m : rationalPoints G)⁻¹ ∈ K ↔
      (u : rationalPoints G) ∈ K
    constructor
    · intro hu
      have h1 : (u : rationalPoints G) = (m : rationalPoints G)⁻¹ *
          ((m : rationalPoints G) * (u : rationalPoints G) * (m : rationalPoints G)⁻¹) *
            (m : rationalPoints G) := by group
      rw [h1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hm) hu) hm
    · intro hu
      exact K.mul_mem (K.mul_mem hm hu) (K.inv_mem hm)

/-- `δ₀^{M_J}` (`standardLeviMinimalModulus`) on the minimal parabolic `P₀(F) ∩ M_J(F)` of
`M_J(F)`, viewed as the subgroup `P₀(F).subgroupOf M_J(F)` of `M_J(F)`. -/
def standardLeviMinimalModulusOf :
    (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J) →* ℝ≥0ˣ :=
  (standardLeviMinimalModulus i ν J).comp
    { toFun := fun x => ⟨((x : standardLeviPoints i ν J) : rationalPoints G),
        Subgroup.mem_inf.mpr ⟨x.2, (x : standardLeviPoints i ν J).2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem standardLeviMinimalModulusOf_apply
    (x : (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J)) :
    standardLeviMinimalModulusOf i ν J x =
      standardLeviMinimalModulus i ν J ⟨((x : standardLeviPoints i ν J) : rationalPoints G),
        Subgroup.mem_inf.mpr ⟨x.2, (x : standardLeviPoints i ν J).2⟩⟩ :=
  rfl

variable {i ν J}

/-- **The Library's `LeviData` for an actual standard parabolic `P_J ⊇ P₀`**, for connected
reductive `G`: the Levi projection of `P_J(F) = M_J(F) ⋉ U_J(F)`, `δ₀`, `δ_P = δ_{U_J}` and
`δ₀^{M_J}`. The clauses are `P₀(F) ⊆ P_J(F)`, `ker m_P = U_J(F) ⊆ U₀(F) ⊆ P₀(F)`, `δ₀ = 1` on
`U₀(F)`, `δ₀ = δ_{U_J} δ₀^{M_J}` on `P₀(F) ∩ M_J(F)` (`rationalMinimalModulus_eq_mul`) and
`δ_{U_J} = 1` on `M_J(F) ∩ K`. -/
theorem rationalLeviData (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G))) :
    LeviData K (standardParabolicPoints i ν ∅) (standardParabolicPoints i ν J)
      (standardLeviPoints i ν J) (rationalMinimalModulus i ν) (standardUnipotentModulus i ν J)
      (standardLeviMinimalModulusOf i ν J)
      (isSemidirectDecomposition_standard hG hi hν hJ).projection :=
  leviData_of_isSemidirectDecomposition (isSemidirectDecomposition_standard hG hi hν hJ)
    (standardParabolicPoints_empty_le hG hi hν hJ)
    (fun _ hu => standardUnipotent_le_standardParabolic i ν ∅ _
      (standardUnipotentPoints_le_empty_of_subset hG hi hν hJ hu))
    (fun p hp => rationalMinimalModulus_eq_one_of_mem_standardUnipotent hG hi hν p
      (standardUnipotentPoints_le_empty_of_subset hG hi hν hJ hp))
    (fun p hp => by
      rw [standardLeviMinimalModulusOf_apply, mul_comm]
      exact rationalMinimalModulus_eq_mul hG hi hν hJ ⟨p, Subgroup.mem_inf.mpr ⟨p.2, hp⟩⟩)
    (fun m hm => standardUnipotentModulus_eq_one i ν J hKo hKc m hm)

omit [LocallyOfFiniteType G.X.hom] in
/-- `K ∩ M_J(F)` is compact. -/
theorem compactSpace_subgroupOf_standardLevi {K : Subgroup (rationalPoints G)}
    (hKc : IsCompact (K : Set (rationalPoints G))) :
    CompactSpace (K.subgroupOf (standardLeviPoints i ν J)) :=
  isCompact_iff_compactSpace.mp
    ((isClosed_standardLeviPoints i ν J).isClosedEmbedding_subtypeVal.isCompact_preimage hKc)

/-- **Waldspurger's `Ξ^M` for `M = M_J`** (II.1, printed p. 252: "On définit une fonction `Ξ^M`
sur `M` comme on vient de définir `Ξ` sur `G`"): the Library's generic spherical function `xi` of
the group `M_J(F)` for its minimal parabolic `P₀(F) ∩ M_J(F)`, the compact subgroup
`K ∩ M_J(F)` with `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))` (`hM`) and the modulus `δ₀^{M_J}`, i.e.
`Ξ^{M_J}(m) = ∫_{K ∩ M_J} δ₀^{M_J}(p(km))^{1/2} dk`. -/
def rationalLeviXi {K : Subgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (m : standardLeviPoints i ν J) : ℝ :=
  haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  xi hM (standardLeviMinimalModulusOf i ν J) m

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))` when the Levi projection maps `P_J(F) ∩ K` into `K`
(Renard V.5.1 (3), `K ∩ P = (K ∩ M)(K ∩ U)`, for a special `K`). -/
theorem isIwasawaPair_standardLevi (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {K : Subgroup (rationalPoints G)} (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hmK : ∀ p : standardParabolicPoints i ν J, (p : rationalPoints G) ∈ K →
      ((isSemidirectDecomposition_standard hG hi hν hJ).projection p : rationalPoints G) ∈ K) :
    IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)) :=
  isIwasawaPair_of_isSemidirectDecomposition (isSemidirectDecomposition_standard hG hi hν hJ)
    (standardParabolicPoints_empty_le hG hi hν hJ)
    (fun _ hu => standardUnipotent_le_standardParabolic i ν ∅ _
      (standardUnipotentPoints_le_empty_of_subset hG hi hν hJ hu)) hPK hmK

/-- **Waldspurger, Lemme II.1.6** (printed p. 252) on actual rational points, for a standard
parabolic `P_J ⊇ P₀` of a connected reductive group:
`Ξ(g) = ∫_K δ_{U_J}(m_P(kg))^{1/2} Ξ^{M_J}(m_P(kg)) dk`, where `m_P(x) ∈ M_J(F)` is the Levi
component of a factorization `x = p k'`, `p ∈ P_J(F)`, `k' ∈ K` (`leviComponent`), `δ_{U_J}` the
Haar modulus of conjugation on `U_J(F)` and `dk` the Haar probability measure of `K`. This is the
Library's generic `LeviData.xi_eq_integral` for `rationalLeviData`. -/
theorem rationalXi_eq_integral_rationalLeviXi (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J))) (g : rationalPoints G) :
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    rationalXi hKc hPK g =
      ∫ k : K, NNReal.sqrt (standardUnipotentModulus i ν J
          (leviComponent (hPK.mono (standardParabolicPoints_empty_le hG hi hν hJ))
            (isSemidirectDecomposition_standard hG hi hν hJ).projection
              ((k : rationalPoints G) * g)) : ℝ≥0) *
        rationalLeviXi hKc hM
          (leviComponent (hPK.mono (standardParabolicPoints_empty_le hG hi hν hJ))
            (isSemidirectDecomposition_standard hG hi hν hJ).projection
              ((k : rationalPoints G) * g))
        ∂(normalizedHaar K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  exact (rationalLeviData hG hi hν hJ hKo hKc).xi_eq_integral hKo hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) g

end Levi

end Langlands.HarishChandraSchwartz
