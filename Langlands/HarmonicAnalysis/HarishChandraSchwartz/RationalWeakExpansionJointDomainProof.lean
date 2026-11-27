import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionJointDomain
import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryThreshold
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionSpecialCompact
import Langlands.Representation.Unitary.ConjugateEquiv
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket

/-! # The joint convergence domain of the c-family has nonempty interior -/

noncomputable section


open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily DynamicCommonLeviComposition

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance jointProofAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance jointProofLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance jointProofLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance jointProofLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  cFamilyRadicalMeasurableSpace cFamilyRadicalBorelSpace cFamilyIntersectionMeasurableSpace
  cFamilyIntersectionBorelSpace cFamilyQuotientMeasurableSpace cFamilyQuotientBorelSpace

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "θs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

/-- An isomorphism of group schemes preserves and reflects the actual common norm kernels. -/
theorem map_iso_mem_rationalCommonNormKernel_iff {H K : GroupScheme (Spec (CommRingCat.of F))}
    (e : H ≅ K) (y : rationalPoints H) :
    rationalPoints.map e.hom y ∈ rationalCommonNormKernel K ↔ y ∈ rationalCommonNormKernel H := by
  constructor
  · intro hy
    have h := rationalCommonNormKernel_le_comap e.inv hy
    simpa only [Subgroup.mem_comap, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using h
  · exact fun hy => rationalCommonNormKernel_le_comap _ hy

/-- Full convergence of the standard integral for one parabolic and two literally equal Levi
subgroups, along a linear equivalence intertwining the two actions on the same ambient points. -/
theorem domain_eq_top_iff_of_levi_eq {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H] {P M₀ M₁ U : Subgroup H} (h : M₀ = M₁)
    (h₀ : IsSemidirectDecomposition P M₀ U) (h₁ : IsSemidirectDecomposition P M₁ U)
    (hU : IsClosed (U : Set H)) (U' : Subgroup H)
    [MeasurableSpace (StandardIntertwining.QuotientSpace (U := U) U')]
    (qν : Measure (StandardIntertwining.QuotientSpace (U := U) U'))
    (A₀ : SmoothRep.{0, u, uV} ℂ M₀) (A₁ : SmoothRep.{0, u, uV} ℂ M₁) (e : A₀ ≃ₗ[ℂ] A₁)
    (he : ∀ (m : M₀) (v : A₀), e (A₀.representation m v) =
      A₁.representation ⟨m, h ▸ m.2⟩ (e v)) :
    StandardIntertwining.domain h₀ hU U' A₀ qν = ⊤ ↔
      StandardIntertwining.domain h₁ hU U' A₁ qν = ⊤ := by
  subst h
  exact StandardIntertwining.domain_eq_top_iff_equiv h₀ hU U' qν
    (Representation.Equiv.mk e fun m => LinearMap.ext fun v => he m v)

/-! ### Conjugation of the inducing Levi and of its unramified characters -/

section Conjugation

include hG hi hν hζ in
/-- Forward conjugation by `n` carries `M_I(F)` onto `(s·M)(F) = Z_G(θ_s)(F)`. -/
theorem thetaLevi_conj_mem_iff (x : rationalPoints G) :
    GroupScheme.rationalPointsConjHomeomorph G (n : rationalPoints G) x ∈ DynamicOppositeStandardIntertwining.levi θs ↔
      x ∈ standardLeviPoints i ν (rootSet i ν I) := by
  rw [mem_conjugatedLevi_iff_of_centralizer_eq hG hi hν I hζ n rfl,
    GroupScheme.rationalPointsConjHomeomorph_apply]
  have h : ((n : rationalPoints G))⁻¹ * ((n : rationalPoints G) * x * (n : rationalPoints G)⁻¹) *
      (n : rationalPoints G) = x := by group
  rw [h]

/-- **The conjugation `M_I(F) ≃ (s·M)(F)`**, `m ↦ n m n⁻¹`, as a topological group
isomorphism onto the literal dynamic Levi of `θ_s`. -/
def thetaLeviConjugation : 𝐌 ≃ₜ* DynamicOppositeStandardIntertwining.levi θs :=
  QuotientIntegration.subgroupContinuousMulEquiv
    (GroupScheme.rationalPointsConjHomeomorph G (n : rationalPoints G))
    (standardLeviPoints i ν (rootSet i ν I)) (DynamicOppositeStandardIntertwining.levi θs)
    (thetaLevi_conj_mem_iff hG hi hν I hζ n)

theorem thetaLeviConjugation_apply_coe (m : 𝐌) :
    (thetaLeviConjugation hG hi hν I hζ n m : rationalPoints G) =
      (n : rationalPoints G) * m * (n : rationalPoints G)⁻¹ := by
  change GroupScheme.rationalPointsConjHomeomorph G (n : rationalPoints G) m = _
  rw [GroupScheme.rationalPointsConjHomeomorph_apply]

theorem thetaLeviConjugation_symm_apply_coe (m : DynamicOppositeStandardIntertwining.levi θs) :
    ((thetaLeviConjugation hG hi hν I hζ n).symm m : rationalPoints G) =
      (n : rationalPoints G)⁻¹ * m * (n : rationalPoints G) := by
  change (GroupScheme.rationalPointsConjHomeomorph G (n : rationalPoints G)).symm m = _
  rw [ContinuousMulEquiv.symm_apply_eq, GroupScheme.rationalPointsConjHomeomorph_apply]
  group

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] in
/-- `Z_G(θ_s)` is the preimage of the centralizer of `groupHom ζ ≫ i` under `Int(n)⁻¹`. -/
theorem theta_centralizer_comap :
    (Dynamic.centralizer θs).comap (G.innerIso (n : rationalPoints G)).hom =
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) := by
  rw [conjugatedCocharacter, groupHom_cocharacterAut_comp]
  exact (Dynamic.centralizer_eq_comap_of_iso _ _).symm

/-- **The conjugated Levi scheme of `θ_s`.** The actual centralizer scheme of `θ_s` is
identified with the standard Levi scheme `M_I` through `Int(n)⁻¹`. -/
def thetaLeviParameterIso :
    parameterScheme θs ≅ Standard.leviScheme i ν (rootSet i ν I) :=
  (SubgroupFunctor.IsRepresentedBy.isoOfComap
    (Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ i))
    (Dynamic.Affine.isRepresentedBy_centralizerHom θs)
    (G.innerIso (n : rationalPoints G)) (theta_centralizer_comap n)).symm ≪≫
    Langlands.Plancherel.standardLeviParameterIso hG hi hν I hζ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Over `G`, the identification is conjugation by `n⁻¹`. -/
theorem thetaLeviParameterIso_hom_comp :
    (thetaLeviParameterIso hG hi hν I hζ n).hom ≫ Standard.leviHom i ν (rootSet i ν I) =
      Dynamic.Affine.centralizerHom θs ≫ (G.innerIso (n : rationalPoints G)).inv := by
  simp only [thetaLeviParameterIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Langlands.Plancherel.standardLeviParameterIso_hom_comp,
    SubgroupFunctor.IsRepresentedBy.isoOfComap_inv_comp]

/-- On points, the identification is the inverse conjugation. -/
theorem leviRationalPointHomeomorph_thetaLeviParameterIso
    (y : rationalPoints (parameterScheme θs)) :
    ((leviRationalPointHomeomorph i ν I
        (rationalPoints.map (thetaLeviParameterIso hG hi hν I hζ n).hom y) : levi i ν I) :
        rationalPoints G) =
      ((thetaLeviConjugation hG hi hν I hζ n).symm (parameterHomeomorph θs y) :
        rationalPoints G) := by
  rw [leviRationalPointHomeomorph_apply_coe, thetaLeviConjugation_symm_apply_coe,
    rationalPoints.map_apply, rationalPoints.map_apply, parameterHomeomorph_apply_coe]
  have h := congrArg (fun f => y ≫ f.hom.hom) (thetaLeviParameterIso_hom_comp hG hi hν I hζ n)
  simp only [Grp.comp_hom_hom, Category.assoc] at h ⊢
  rw [h]
  have hc := DFunLike.congr_fun (rationalPoints_map_innerIso_inv (n : rationalPoints G))
    (y ≫ (Dynamic.Affine.centralizerHom θs).hom.hom)
  rw [rationalPoints.map_apply] at hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Category.assoc] at hc
  exact hc

omit [LocallyOfFiniteType G.X.hom] in
/-- The identification preserves and reflects the actual norm-one subgroups. -/
theorem map_thetaLeviParameterIso_mem_iff (y : rationalPoints (parameterScheme θs)) :
    rationalPoints.map (thetaLeviParameterIso hG hi hν I hζ n).hom y ∈
        rationalCommonNormKernel (Standard.leviScheme i ν (rootSet i ν I)) ↔
      y ∈ rationalCommonNormKernel (parameterScheme θs) :=
  map_iso_mem_rationalCommonNormKernel_iff _ y

/-- **`(s·M)(F)¹ = n M_I(F)¹ n⁻¹`** for the norm characters of the actual centralizer scheme of
`θ_s`. -/
theorem commonNormKernel_thetaTransport :
    commonNormKernel (fun ψ => (leviRationalNormCharacters i ν I ψ).comp
        (thetaLeviConjugation hG hi hν I hζ n).symm.toMulEquiv.toMonoidHom) =
      commonNormKernel (leviNormCharacters θs) := by
  ext m'
  obtain ⟨y, rfl⟩ := (parameterHomeomorph θs).surjective m'
  have key : (thetaLeviConjugation hG hi hν I hζ n).symm (parameterHomeomorph θs y) =
      leviRationalPointHomeomorph i ν I
        (rationalPoints.map (thetaLeviParameterIso hG hi hν I hζ n).hom y) :=
    Subtype.ext (leviRationalPointHomeomorph_thetaLeviParameterIso hG hi hν I hζ n y).symm
  rw [mem_commonNormKernel, mem_commonNormKernel]
  show (∀ ψ, leviRationalNormCharacters i ν I ψ
      ((thetaLeviConjugation hG hi hν I hζ n).symm (parameterHomeomorph θs y)) = 1) ↔
    ∀ ψ, normCharacters θs ψ ((parameterHomeomorph θs).symm (parameterHomeomorph θs y)) = 1
  rw [key, ContinuousMulEquiv.symm_apply_apply]
  simp only [leviRationalNormCharacters_apply_points]
  exact (mem_commonNormKernel _ _).symm.trans
    ((map_thetaLeviParameterIso_mem_iff hG hi hν I hζ n y).trans (mem_commonNormKernel _ _))

/-- **The conjugation `z ↦ z ∘ e⁻¹` of unramified characters**, `X(M_I) ≃ X(Z_G(θ_s))`, read in
the actual parameters of the centralizer scheme of `θ_s`. -/
def thetaCharacterTransport :
    unramifiedCharacters νM ≃ₜ* unramifiedCharacters (normCharacters θs) :=
  ((unramifiedCharactersHomeomorph (thetaLeviConjugation hG hi hν I hζ n) νM).trans
    (unramifiedCharactersCongr (commonNormKernel_thetaTransport hG hi hν I hζ n))).trans
    (parameterTransport θs).symm

/-- The transported parameter evaluates on `(s·M)(F)` as `z ∘ e⁻¹`. -/
theorem parameterTransport_thetaCharacterTransport (z : unramifiedCharacters νM)
    (m : DynamicOppositeStandardIntertwining.levi θs) :
    (parameterTransport θs (thetaCharacterTransport hG hi hν I hζ n z)).val m =
      z.val ((thetaLeviConjugation hG hi hν I hζ n).symm m) := by
  simp only [thetaCharacterTransport, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.apply_symm_apply]
  rfl

end Conjugation

/-! ### The two factors on the common Levi of `θ_s` -/

section Factors

/-- The conjugate `ⁿB = B(n⁻¹ · n)` of a representation of `M_I(F)`, on the literal Levi of
`θ_s`. -/
abbrev thetaConjugateRep (B : SmoothRep.{0, u, uV} ℂ 𝐌) :
    SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi θs) :=
  SmoothRep.pullback (thetaLeviConjugation hG hi hν I hζ n).symm B

/-- Isomorphic representations have equivalent conjugates. -/
def thetaConjugateEquivOfIso {B B' : SmoothRep.{0, u, uV} ℂ 𝐌} (e : B ≅ B') :
    (thetaConjugateRep hG hi hν I hζ n B).representation.Equiv
      (thetaConjugateRep hG hi hν I hζ n B').representation :=
  SmoothRep.equivOfIso
    ((SmoothRep.pullbackFunctor (thetaLeviConjugation hG hi hν I hζ n).symm).mapIso e)

/-- The conjugate of a twist is the twist of the conjugate by the transported parameter. -/
def thetaConjugateTwistEquiv (B : SmoothRep.{0, u, uV} ℂ 𝐌) (z : unramifiedCharacters νM) :
    (thetaConjugateRep hG hi hν I hζ n
        (B.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM z))).representation.Equiv
      ((thetaConjugateRep hG hi hν I hζ n B).twist
        (parameterTransport θs (thetaCharacterTransport hG hi hν I hζ n z)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters θs)
          (parameterTransport θs (thetaCharacterTransport hG hi hν I hζ n z)))).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ B) fun m => by
    apply LinearMap.ext
    intro v
    change (z.val ((thetaLeviConjugation hG hi hν I hζ n).symm m) : ℂ) •
        B.representation ((thetaLeviConjugation hG hi hν I hζ n).symm m) v =
      ((parameterTransport θs (thetaCharacterTransport hG hi hν I hζ n z)).val m : ℂ) •
        B.representation ((thetaLeviConjugation hG hi hν I hζ n).symm m) v
    rw [parameterTransport_thetaCharacterTransport]

/-- The same, for any monoid homomorphism agreeing pointwise with the parameter. -/
def thetaConjugateTwistEquiv' (B : SmoothRep.{0, u, uV} ℂ 𝐌) (z : unramifiedCharacters νM)
    (χ : 𝐌 →* ℂˣ) (hχ : IsOpen (χ.ker : Set 𝐌)) (h : ∀ m, χ m = z.val m) :
    (thetaConjugateRep hG hi hν I hζ n (B.twist χ hχ)).representation.Equiv
      ((thetaConjugateRep hG hi hν I hζ n B).twist
        (parameterTransport θs (thetaCharacterTransport hG hi hν I hζ n z)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters θs)
          (parameterTransport θs (thetaCharacterTransport hG hi hν I hζ n z)))).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ B) fun m => by
    apply LinearMap.ext
    intro v
    change (χ ((thetaLeviConjugation hG hi hν I hζ n).symm m) : ℂ) •
        B.representation ((thetaLeviConjugation hG hi hν I hζ n).symm m) v =
      ((parameterTransport θs (thetaCharacterTransport hG hi hν I hζ n z)).val m : ℂ) •
        B.representation ((thetaLeviConjugation hG hi hν I hζ n).symm m) v
    rw [parameterTransport_thetaCharacterTransport, h]

section Auxiliary

variable (α : cocharacterLattice T)
  (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "ψα" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i

include hG hi hν hζ hn hα in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The literal Levis of `θ_s` and of the auxiliary cocharacter agree. -/
theorem thetaLevi_eq_auxiliaryLevi :
    DynamicOppositeStandardIntertwining.levi θs = DynamicOppositeStandardIntertwining.levi ψα :=
  congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
    (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).symm

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

/-- **One factor of the c-family on the Levi of `θ_s`.** Convergence of `J_{P_α|s·P}` on the
conjugate `ⁿB` is full convergence of the actual standard integral from `P(θ_s)` to `P(ψ_α)`
with common Levi cocharacter `θ_s` on `thetaConjugateRep B`. -/
theorem factorConverges_iff (B : SmoothRep.{0, u, uV} ℂ 𝐌) :
    FactorConverges hG hi hν I I' hζ n hn α hα K hK (conjugateRep hG hi hν I I' hζ n hn α hα B) ↔
      StandardIntertwining.domain (DynamicCommonLeviComposition.commonDecomposition θs θs rfl)
        (radical_isClosed θs) (radical ψα) (thetaConjugateRep hG hi hν I hζ n B)
        (pairQuotientMeasure K hK θs ψα) = ⊤ := by
  unfold FactorConverges
  refine (domain_eq_top_iff_of_levi_eq (thetaLevi_eq_auxiliaryLevi hG hi hν I I' hζ n hn α hα)
    (DynamicCommonLeviComposition.commonDecomposition θs θs rfl)
    (DynamicCommonLeviComposition.commonDecomposition ψα θs
      (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).symm) (radical_isClosed θs) (radical ψα)
    (pairQuotientMeasure K hK θs ψα) (thetaConjugateRep hG hi hν I hζ n B)
    (conjugateRep hG hi hν I I' hζ n hn α hα B) (LinearEquiv.refl ℂ B) fun m v => ?_).symm
  change B.representation ((thetaLeviConjugation hG hi hν I hζ n).symm m) v =
    B.representation (Aubert.General.conjugationEquiv (n : rationalPoints G)
      (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)
      ⟨m, thetaLevi_eq_auxiliaryLevi hG hi hν I I' hζ n hn α hα ▸ m.2⟩) v
  refine congrArg (fun x => B.representation x v) ?_
  apply Subtype.ext
  rw [thetaLeviConjugation_symm_apply_coe, Aubert.General.conjugationEquiv_apply]

end Auxiliary

section Joint

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "ψpos" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i ζ' (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "ψneg" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i (-ζ') (conjugatedCocharacter i ζ n)) ≫ i

/-- **The joint convergence domain from the two actual full domains on the Levi of `θ_s`.**
If the transported parameter `w` of `z` lies in the full domain of the standard integral from
`P(θ_s)` to `P(ψ₊)` for the conjugate of `A`, and `w⁻¹` in the full domain from `P(θ_s)` to
`P(ψ₋)` for the conjugate of the smooth dual of `A`, then both integrals of the c-family
converge at `A ⊗ z`. -/
theorem mem_cDomain_of_mem_pairFullDomainRegion (A : SmoothRep.{0, u, uV} ℂ 𝐌)
    (z : unramifiedCharacters νM)
    (hpos : thetaCharacterTransport hG hi hν I hζ n z ∈
      pairFullDomainRegion θs K hK θs rfl ψpos (thetaConjugateRep hG hi hν I hζ n A))
    (hneg : (thetaCharacterTransport hG hi hν I hζ n z)⁻¹ ∈
      pairFullDomainRegion θs K hK θs rfl ψneg
        (thetaConjugateRep hG hi hν I hζ n A.contragredient)) :
    z ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A := by
  constructor
  · rw [factorConverges_iff hG hi hν I I' hζ n hn ζ' (outerCentralizer_pos hG hi hν I' hζ') K hK]
    exact (StandardIntertwining.domain_eq_top_iff_equiv _ _ _ _
      (thetaConjugateTwistEquiv hG hi hν I hζ n A z)).mpr hpos
  · rw [factorConverges_iff hG hi hν I I' hζ n hn (-ζ') (outerCentralizer_neg hG hi hν I' hζ') K hK]
    have e₁ := thetaConjugateEquivOfIso hG hi hν I hζ n
      (SmoothRep.contragredientTwistIso z.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM z) A)
    have e₂ := thetaConjugateTwistEquiv' hG hi hν I hζ n A.contragredient z⁻¹
      (z.val.toMonoidHom)⁻¹ (isOpen_ker_inv (unramifiedCharacter_isOpen_ker νM z))
      (fun m => rfl)
    rw [StandardIntertwining.domain_eq_top_iff_equiv _ _ _ _ e₁,
      StandardIntertwining.domain_eq_top_iff_equiv _ _ _ _ e₂, map_inv]
    exact hneg

end Joint

end Factors

/-! ### Signs of the split-component roots -/

section Sign

/-- Additive combinations of cocharacters are compatible with homomorphisms that agree on the
summands. -/
theorem groupHom_zsmul_add_comp {S : Scheme.{u}} {A B : CommGroupScheme S} {M : GroupScheme S}
    (a : A.toGrp ⟶ M) (b : B.toGrp ⟶ M) (x y : cocharacterLattice A)
    (x' y' : cocharacterLattice B) (N : ℤ)
    (hx : CommGroupScheme.groupHom x ≫ a = CommGroupScheme.groupHom x' ≫ b)
    (hy : CommGroupScheme.groupHom y ≫ a = CommGroupScheme.groupHom y' ≫ b) :
    CommGroupScheme.groupHom (N • x + y) ≫ a = CommGroupScheme.groupHom (N • x' + y') ≫ b := by
  apply GroupScheme.hom_ext_points
  intro U t
  have h1 := congrArg (fun f => t ≫ f.hom.hom) hx
  have h2 := congrArg (fun f => t ≫ f.hom.hom) hy
  simp only [Grp.comp_hom_hom, ← Category.assoc] at h1 h2 ⊢
  rw [comp_groupHom_add, comp_groupHom_zsmul, MonObj.mul_comp, GrpObj.zpow_comp, h1, h2,
    comp_groupHom_add, comp_groupHom_zsmul, MonObj.mul_comp, GrpObj.zpow_comp]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The maximal split torus factors through the centralizer scheme of `θ_s`. -/
def torusThetaFactor : T.toGrp ⟶ parameterScheme θs :=
  SubgroupFunctor.IsRepresentedBy.factorHom (Dynamic.Affine.isRepresentedBy_centralizerHom θs) i
    ((GroupScheme.range_le_torusCentralizer i).trans
      (GroupScheme.torusCentralizer_le_dynamicCentralizer i
        (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n))))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem torusThetaFactor_comp :
    torusThetaFactor (ζ := ζ) n ≫ Dynamic.Affine.centralizerHom θs = i :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

variable {Ts : CommGroupScheme (Spec (CommRingCat.of F))} (a : Ts.toGrp ⟶ parameterScheme θs)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- A cocharacter of the maximal split torus whose centralizer contains `Z_G(θ_s)` factors
through every split component of `Z_G(θ_s)`. -/
theorem exists_splitComponent_cocharacter (ha : IsSplitComponent a) (ξ : cocharacterLattice T)
    (hξ : Dynamic.centralizer θs ≤ Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i)) :
    ∃ ξT : cocharacterLattice Ts, CommGroupScheme.groupHom ξT ≫ a =
      CommGroupScheme.groupHom ξ ≫ torusThetaFactor (ζ := ζ) n := by
  have hc := (GroupScheme.isCentral_comp_iff_le_dynamicCentralizer
    (Dynamic.Affine.isRepresentedBy_centralizerHom θs) (torusThetaFactor (ζ := ζ) n)
    (torusThetaFactor_comp n) ξ).mpr hξ
  obtain ⟨f, hf⟩ := ha.exists_factor isSplitTorus_gm hc
  exact ⟨Additive.ofMul f, hf⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The auxiliary cocharacter of a split-component combination. -/
theorem groupHom_auxiliary_comp (α' : cocharacterLattice T) (N : ℤ) (θT αT : cocharacterLattice Ts)
    (hθ : CommGroupScheme.groupHom θT ≫ a =
      CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ torusThetaFactor (ζ := ζ) n)
    (hα : CommGroupScheme.groupHom αT ≫ a =
      CommGroupScheme.groupHom α' ≫ torusThetaFactor (ζ := ζ) n) :
    CommGroupScheme.groupHom (N • αT + θT) ≫ a ≫ Dynamic.Affine.centralizerHom θs =
      CommGroupScheme.groupHom (N • α' + conjugatedCocharacter i ζ n) ≫ i := by
  rw [← Category.assoc, groupHom_zsmul_add_comp a (torusThetaFactor (ζ := ζ) n) αT θT α'
    (conjugatedCocharacter i ζ n) N hα hθ, Category.assoc, torusThetaFactor_comp]

variable {a}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG in
/-- **Root signs of a presentation.** For a presentation of `P(ψ) ⊇ Z_G(θ_s)` on the split
component `a`, and a split-component cocharacter `ψ_T` with
`groupHom ψT ≫ a ≫ Dynamic.Affine.centralizerHom θs = ψ`, the presentation's split-component
cocharacter and `ψ_T` have positive pairing with the same roots. -/
theorem pos_iff_of_parabolicData (ha : IsSplitComponent a)
    {ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} (d : DynamicCommonLeviPresentations.ParabolicData θs ψ Ts a)
    (ψT : cocharacterLattice Ts)
    (hψT : CommGroupScheme.groupHom ψT ≫ a ≫ Dynamic.Affine.centralizerHom θs = ψ)
    (α : characterLattice Ts) (hα : α ∈ relativeRoots (a ≫ d.l ≫ d.p)) :
    0 < latticePairing Ts α d.r.splitComponentCocharacter ↔ 0 < latticePairing Ts α ψT := by
  have := hG.smooth
  have hTs : IsSplitTorus Ts.toGrp := ha.1.1.1
  have h1 := d.r.subgroupRelativeRoots_radical d.radical
  rw [d.realizes.radical] at h1
  have h2 := RelativeRoot.subgroupRelativeRoots_dynamicUnipotent (a ≫ d.l ≫ d.p) hTs ψT
  rw [d.levi_comp, hψT, ← d.levi_comp, h1] at h2
  have h3 := Set.ext_iff.mp h2 α
  simp only [positiveRelativeRoots, Set.mem_ofPred_eq] at h3
  exact ⟨fun h => (h3.mp ⟨hα, h⟩).2, fun h => (h3.mpr ⟨hα, h⟩).2⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG in
/-- The same for negative pairings, by negation of the root. -/
theorem neg_iff_of_parabolicData (ha : IsSplitComponent a)
    {ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} (d : DynamicCommonLeviPresentations.ParabolicData θs ψ Ts a)
    (ψT : cocharacterLattice Ts)
    (hψT : CommGroupScheme.groupHom ψT ≫ a ≫ Dynamic.Affine.centralizerHom θs = ψ)
    (α : characterLattice Ts) (hα : α ∈ relativeRoots (a ≫ d.l ≫ d.p)) :
    latticePairing Ts α d.r.splitComponentCocharacter < 0 ↔ latticePairing Ts α ψT < 0 := by
  let : Mono d.r.data.i.hom.hom.left := d.r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hneg := parabolic_neg_mem_relativeRoots d.r
    (relativeRootSystem F G hG d.r.data.T d.r.data.i d.r.isCompatible.maximalSplit) ha.1.1.1
    d.r.isCompatible.maximalSplit.isSplitSubtorus.1 hα
  have h := pos_iff_of_parabolicData hG n ha d ψT hψT (-α) hneg
  simp only [map_neg, LinearMap.neg_apply, Left.neg_pos_iff] at h
  exact h

set_option hygiene false in
local notation "ψpos" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i ζ' (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "ψneg" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i (-ζ') (conjugatedCocharacter i ζ n)) ≫ i

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν hζ hζ' hn in
/-- **The sign relation between the two factors.** A root of the split component of `s·M`
that is positive for `s·P` and negative for `P_s = (M' ∩ s·P)U'` is positive for
`P̃_s = (M' ∩ s·P)Ū'`: such roots lie in `Ū'`. -/
theorem sign_relation (ha : IsSplitComponent a)
    (dθ : DynamicCommonLeviPresentations.ParabolicData θs θs Ts a)
    (dp : DynamicCommonLeviPresentations.ParabolicData θs ψpos Ts a)
    (dm : DynamicCommonLeviPresentations.ParabolicData θs ψneg Ts a)
    (α : characterLattice Ts) (hα : α ∈ relativeRoots (a ≫ dθ.l ≫ dθ.p))
    (h1 : 0 < latticePairing Ts α dθ.r.splitComponentCocharacter)
    (h2 : latticePairing Ts α dp.r.splitComponentCocharacter < 0) :
    0 < latticePairing Ts α dm.r.splitComponentCocharacter := by
  obtain ⟨θT, hθT⟩ := exists_splitComponent_cocharacter n a ha (conjugatedCocharacter i ζ n) le_rfl
  have hζle : Dynamic.centralizer θs ≤ Dynamic.centralizer (CommGroupScheme.groupHom ζ' ≫ i) := by
    rw [(conjugatedCocharacter_dynamic i ν (rootSet i ν I) hG hi hν (rootSet_subset i ν I) ζ hζ
      n).2.1, outerCentralizer_pos hG hi hν I' hζ']
    exact hn
  obtain ⟨ζT, hζT⟩ := exists_splitComponent_cocharacter n a ha ζ' hζle
  have hθ' : CommGroupScheme.groupHom θT ≫ a ≫ Dynamic.Affine.centralizerHom θs = θs := by
    rw [← Category.assoc, hθT, Category.assoc, torusThetaFactor_comp]
  have hpos := groupHom_auxiliary_comp n a ζ' (auxiliaryMultiplicity i ζ' (conjugatedCocharacter i ζ n))
    θT ζT hθT hζT
  have hneg := groupHom_auxiliary_comp n a ζ'
    (-(auxiliaryMultiplicity i (-ζ') (conjugatedCocharacter i ζ n) : ℤ)) θT ζT hθT hζT
  rw [show (-(auxiliaryMultiplicity i (-ζ') (conjugatedCocharacter i ζ n) : ℤ)) • ζ' =
      (auxiliaryMultiplicity i (-ζ') (conjugatedCocharacter i ζ n) : ℤ) • (-ζ') by
    rw [neg_smul, smul_neg]] at hneg
  have hroot : ∀ d : Σ ψ, DynamicCommonLeviPresentations.ParabolicData θs ψ Ts a,
      α ∈ relativeRoots (a ≫ d.2.l ≫ d.2.p) := by
    intro d
    rw [d.2.levi_comp, ← dθ.levi_comp]
    exact hα
  have e1 := pos_iff_of_parabolicData hG n ha dθ θT hθ' α hα
  have e2 := neg_iff_of_parabolicData hG n ha dp _ hpos α (hroot ⟨_, dp⟩)
  have e3 := pos_iff_of_parabolicData hG n ha dm _ hneg α (hroot ⟨_, dm⟩)
  rw [e3]
  have k1 := e1.mp h1
  have k2 := e2.mp h2
  simp only [map_add, map_zsmul, smul_eq_mul] at k2 ⊢
  have hN : (0 : ℤ) ≤ (auxiliaryMultiplicity i ζ' (conjugatedCocharacter i ζ n) : ℤ) :=
    Int.natCast_nonneg _
  have hM : (0 : ℤ) ≤ (auxiliaryMultiplicity i (-ζ') (conjugatedCocharacter i ζ n) : ℤ) :=
    Int.natCast_nonneg _
  rcases le_or_gt 0 ((latticePairing Ts) α ζT) with hz | hz
  · nlinarith [mul_nonneg hN hz]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hM hz.le]

include hG hi hν hζ hζ' hn in
/-- **A common point of the two convergence regions.** For presentations of `s·P`, `P_s` and
`P̃_s` on one split component, with the Weyl-induced form of the presentation of `s·P`, and any
two thresholds, there is an unramified parameter `w` of `Z_G(θ_s)` in the strict region of the
first integral whose inverse lies in the strict region of the second. -/
theorem exists_joint_region_point (ha : IsSplitComponent a)
    (dθ : DynamicCommonLeviPresentations.ParabolicData θs θs Ts a)
    (dp : DynamicCommonLeviPresentations.ParabolicData θs ψpos Ts a)
    (dm : DynamicCommonLeviPresentations.ParabolicData θs ψneg Ts a)
    (op : DynamicCommonLeviPresentations.OppositeData
      (CommGroupScheme.groupHom (-dp.r.splitComponentCocharacter) ≫ a ≫ dp.l ≫ dp.p))
    (om : DynamicCommonLeviPresentations.OppositeData
      (CommGroupScheme.groupHom (-dm.r.splitComponentCocharacter) ≫ a ≫ dm.l ≫ dm.p))
    [Fintype (relativeWeylGroup dθ.r.data.i)] (Rp Rm : ℝ) :
    haveI : Mono dθ.r.data.i.hom.hom.left := dθ.r.isCompatible.maximalSplit.isSplitSubtorus.mono
    haveI : Mono (CommGroupScheme.groupHom dθ.r.data.f).hom.hom.left := by
      let := dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.mono
      let := dθ.r.isCompatible.levi.isClosedSubgroup.mono
      let := dθ.r.isCompatible.parabolic.isClosedSubgroup.mono
      have : Mono (a ≫ dθ.l ≫ dθ.p).hom.hom.left := by
        change Mono (a.hom.hom.left ≫ dθ.l.hom.hom.left ≫ dθ.p.hom.hom.left)
        infer_instance
      exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) dθ.r.isCompatible.factor_comp)
    ∃ w : unramifiedCharacters (normCharacters θs),
      w ∈ parabolicUnramifiedIntertwiningRegion dθ.r
          (weylInducedCharacterForm dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.1
            dθ.r.isCompatible.maximalSplit.isSplitSubtorus.1 dθ.r.data.f dθ.r.data.i)
          dθ.n op.q op.v Rp ∧
      w⁻¹ ∈ parabolicUnramifiedIntertwiningRegion dθ.r
          (weylInducedCharacterForm dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.1
            dθ.r.isCompatible.maximalSplit.isSplitSubtorus.1 dθ.r.data.f dθ.r.data.i)
          dθ.n om.q om.v Rm := by
  have := hG.smooth
  let : Mono dθ.r.data.i.hom.hom.left := dθ.r.isCompatible.maximalSplit.isSplitSubtorus.mono
  let : Mono (CommGroupScheme.groupHom dθ.r.data.f).hom.hom.left := by
    let := dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.mono
    let := dθ.r.isCompatible.levi.isClosedSubgroup.mono
    let := dθ.r.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a ≫ dθ.l ≫ dθ.p).hom.hom.left := by
      change Mono (a.hom.hom.left ≫ dθ.l.hom.hom.left ≫ dθ.p.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) dθ.r.isCompatible.factor_comp)
  have hA : IsSplitTorus Ts.toGrp := dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.1
  let B := weylInducedCharacterForm dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.1
    dθ.r.isCompatible.maximalSplit.isSplitSubtorus.1 dθ.r.data.f dθ.r.data.i
  have hB : B.Nondegenerate := weylInducedCharacterForm_nondegenerate _ _ _ _
  let roots : Set (characterLattice Ts) :=
    {α | α ∈ relativeRoots (a ≫ dθ.l ≫ dθ.p) ∧
        0 < latticePairing Ts α dθ.r.splitComponentCocharacter ∧
          latticePairing Ts α dp.r.splitComponentCocharacter < 0} ∪
      {β | -β ∈ relativeRoots (a ≫ dθ.l ≫ dθ.p) ∧
        0 < latticePairing Ts (-β) dθ.r.splitComponentCocharacter ∧
          latticePairing Ts (-β) dm.r.splitComponentCocharacter < 0}
  have hν : ∀ α ∈ roots, 0 < latticePairing Ts α dm.r.splitComponentCocharacter := by
    rintro α (⟨hα, h1, h2⟩ | ⟨hα, h1, h2⟩)
    · exact sign_relation hG hi hν I I' hζ hζ' n hn ha dθ dp dm α hα h1 h2
    · simp only [map_neg, LinearMap.neg_apply, Left.neg_neg_iff] at h2
      exact h2
  obtain ⟨x, hx⟩ := rootThresholdRegion_nonempty_of_positivePairing hA B hB roots
    dm.r.splitComponentCocharacter hν (max Rp Rm)
  obtain ⟨psi, hpsi⟩ := exists_positiveImageCharacter_extension_of_injective hA a
    (rationalValuationImageMap_injective a dθ.r.isCompatible.levi.isConnectedReductive
      dθ.r.isCompatible.splitComponent) x
  let w := rationalCanonicalImageUnramifiedContinuousEquiv (parameterScheme θs)
    (rationalImagePositiveCharacter (parameterScheme θs) psi)
  have hre : SplitTorus.normalizedRealPart hA (w.val.toMonoidHom.comp (rationalPoints.map a)) =
      x := by
    change SplitTorus.normalizedRealPart hA
      ((rationalImageCharacterPullback (parameterScheme θs)
        (rationalImagePositiveCharacter (parameterScheme θs) psi)).comp (rationalPoints.map a)) = x
    rw [hpsi, SplitTorus.normalizedRealPart_positiveCharacter]
  have hre' : SplitTorus.normalizedRealPart hA ((w⁻¹).val.toMonoidHom.comp (rationalPoints.map a)) =
      -x := by
    rw [← hre, ← SplitTorus.normalizedRealPart_inv]
    rfl
  refine ⟨w, ?_, ?_⟩
  · rw [mem_parabolicUnramifiedIntertwiningRegion dθ.r dp.r (dθ.levi_comp.trans dp.levi_comp.symm)
      dθ.radical op.represented op.radical]
    intro α hα h1 h2
    rw [hre]
    exact lt_of_le_of_lt (le_max_left _ _) (hx α (Or.inl ⟨hα, h1, h2⟩))
  · rw [mem_parabolicUnramifiedIntertwiningRegion dθ.r dm.r (dθ.levi_comp.trans dm.levi_comp.symm)
      dθ.radical om.represented om.radical]
    intro α hα h1 h2
    rw [hre']
    have h := hx (-α) (Or.inr ⟨by rwa [neg_neg], by rwa [neg_neg], by rwa [neg_neg]⟩)
    rw [TensorProduct.tmul_neg, map_neg] at h
    rw [map_neg, LinearMap.neg_apply]
    exact lt_of_le_of_lt (le_max_right _ _) h

end Sign


/-! ### The Iwasawa decomposition for `s·P` and the final assembly -/

section Final

omit [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ in
/-- **`G(F) = (s·P)(F) K` for the special maximal compact subgroup.** The Weyl element of `n` has
a representative `k₀ ∈ K`; then `n⁻¹k₀` centralizes the maximal split torus, so
`s·P = k₀ P_I(F) k₀⁻¹`, and `G(F) = P_I(F) K` gives the decomposition. -/
theorem theta_parabolic_mul_compact {K : OpenSubgroup (rationalPoints G)}
    (hspec : IsSpecialVertexCompact ν hi K)
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
    (g : rationalPoints G) :
    ∃ p : DynamicOppositeStandardIntertwining.parabolic θs, ∃ k : K,
      g = (p : rationalPoints G) * (k : rationalPoints G) := by
  obtain ⟨-, hW⟩ := standardLeviIwasawaFactorsAt_and_weylRepresentatives_of_special hG hi hν hspec hPK
  obtain ⟨k₀, hk₀K, hk₀⟩ := hW (QuotientGroup.mk n)
  have ht : ((n : rationalPoints G)⁻¹ * (k₀ : rationalPoints G)) ∈ centralizerPoints i := by
    have h := QuotientGroup.eq.mp hk₀.symm
    rw [Subgroup.mem_subgroupOf] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have htP := GroupScheme.centralizerPoints_le_standardParabolicPoints i ν (rootSet i ν I) ht
  obtain ⟨q, hq, k, hk, hg⟩ := exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK
    ((k₀ : rationalPoints G)⁻¹ * g)
  refine ⟨⟨(k₀ : rationalPoints G) * q * (k₀ : rationalPoints G)⁻¹, ?_⟩,
    ⟨(k₀ : rationalPoints G) * k, (K : Subgroup (rationalPoints G)).mul_mem hk₀K hk⟩, ?_⟩
  · rw [mem_conjugatedParabolic_iff hG hi hν I hζ n]
    have e : (n : rationalPoints G)⁻¹ * ((k₀ : rationalPoints G) * q * (k₀ : rationalPoints G)⁻¹) *
        (n : rationalPoints G) = ((n : rationalPoints G)⁻¹ * k₀) * q *
          ((n : rationalPoints G)⁻¹ * k₀)⁻¹ := by group
    rw [e]
    exact (standardParabolicPoints i ν (rootSet i ν I)).mul_mem
      ((standardParabolicPoints i ν (rootSet i ν I)).mul_mem htP hq)
      ((standardParabolicPoints i ν (rootSet i ν I)).inv_mem htP)
  · change g = (k₀ : rationalPoints G) * q * (k₀ : rationalPoints G)⁻¹ *
      ((k₀ : rationalPoints G) * k)
    calc g = (k₀ : rationalPoints G) * ((k₀ : rationalPoints G)⁻¹ * g) := by group
      _ = (k₀ : rationalPoints G) * (q * k) := by rw [hg]
      _ = _ := by group

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (hs : IsSplitComponent sc)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs
set_option hygiene false in
local notation "ψpos" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i ζ' (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "ψneg" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i (-ζ') (conjugatedCocharacter i ζ n)) ≫ i

variable [(CM).Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]


include hG hi hν hs in
/-- **Every Haar measure on `M_I(F)/A_{M_I}(F)` is invariant under inversion.** The Levi points
are unimodular (reductive unimodularity of the Levi scheme, transported along
`leviRationalPointHomeomorph`), `A_{M_I}(F)` is closed and central, so the Haar measure of the
quotient is right invariant, hence invariant under inversion. -/
theorem leviSplitQuotientHaar_isInvInvariant [BorelSpace (𝐌 ⧸ CM)] : mu.IsInvInvariant := by
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  have hsc : SecondCountableTopology (rationalPoints G) :=
    Aubert.General.rationalPoint_secondCountableTopology F G
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have : LocallyCompactSpace (RationalPoint F (Standard.leviScheme i ν (rootSet i ν I)).X) :=
    rationalPoint_locallyCompactSpace F (Standard.leviScheme i ν (rootSet i ν I))
  have : IsTopologicalGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
    rationalPoint_isTopologicalGroup F (Standard.leviScheme i ν (rootSet i ν I))
  have : LocallyCompactSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
    rationalPoint_locallyCompactSpace F (Standard.leviScheme i ν (rootSet i ν I))
  have : NonarchimedeanGroup (RationalPoint F (Standard.leviScheme i ν (rootSet i ν I)).X) :=
    RationalPointFamily.affineRationalPoint_nonarchimedeanGroup
      (Standard.leviScheme i ν (rootSet i ν I))
  have hM := isClosed_standardLeviPoints i ν (rootSet i ν I)
  have : LocallyCompactSpace 𝐌 := hM.locallyCompactSpace
  let : MeasurableSpace 𝐌 := borel _
  have : BorelSpace 𝐌 := ⟨rfl⟩
  let e := leviRationalPointHomeomorph i ν I
  have hL := isConnectedReductive_leviScheme_rootSet hG hi hν I
  have hmod : ∀ g : 𝐌, Measure.modularCharacter g = 1 := by
    intro g
    have hm := RationalPointFamily.rationalReductiveUnimodularity F
      (Standard.leviScheme i ν (rootSet i ν I)) hL standardCocharacter (e.symm g)
    simpa only [ContinuousMulEquiv.apply_symm_apply] using
      (modularCharacter_continuousMulEquiv e (e.symm g)).trans hm
  have hAc : IsClosed ((CM : Subgroup 𝐌) : Set 𝐌) := by
    have h := isClosed_range_splitComponent (Standard.leviScheme i ν (rootSet i ν I)) sc hs
    have h' := (e.toHomeomorph.isClosed_image).mpr h
    unfold rationalLeviSplitCenter
    rw [Subgroup.coe_map]
    exact h'
  have : IsClosed ((CM : Subgroup 𝐌) : Set 𝐌) := hAc
  have : SecondCountableTopology 𝐌 := @TopologicalSpace.Subtype.secondCountableTopology _ _
    (standardLeviPoints i ν (rootSet i ν I) : Set (rationalPoints G)) hsc
  have : SecondCountableTopology (𝐌 ⧸ CM) := QuotientGroup.instSecondCountableTopology CM
  have : LocallyCompactSpace (𝐌 ⧸ CM) := inferInstance
  have : SigmaCompactSpace (𝐌 ⧸ CM) := inferInstance
  have : TopologicalSpace.PseudoMetrizableSpace (𝐌 ⧸ CM) := inferInstance
  have : mu.Regular := inferInstance
  have : mu.IsMulRightInvariant :=
    Haar.centralSubgroupQuotient_isMulRightInvariant _ hCM hAc hmod mu
  exact Langlands.isInvInvariant_of_isMulRightInvariant mu

/-- **The joint convergence domain from presentations, admissibility and unitarizability.**
For presentations of `s·P`, `P_s` and `P̃_s` on one split component of the centralizer scheme of
`θ_s`, if the conjugates to the Levi of `θ_s` of `B` and of its smooth dual are admissible and
unitarizable, and `G(F) = (s·P)(F) K`, then the joint convergence domain of the c-family of `B`
has nonempty interior. The full domain of the first factor contains the cone region of
threshold `R₊` and that of the second factor the cone region of threshold `R₋`
(`exists_threshold_mem_pairFullDomainRegion_of_data`). The intersection of the first region
with the preimage of the second region under inversion `w ↦ w⁻¹` is open and nonempty
(`exists_joint_region_point`); its preimage under `thetaCharacterTransport` is an open set
inside the joint convergence domain. -/
theorem cDomain_interior_nonempty_of_data {Ts : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : Ts.toGrp ⟶ parameterScheme θs} (ha : IsSplitComponent a)
    (hpos : Dynamic.centralizer ψpos = Dynamic.centralizer θs)
    (hneg : Dynamic.centralizer ψneg = Dynamic.centralizer θs)
    (dθ : DynamicCommonLeviPresentations.ParabolicData θs θs Ts a)
    (dp : DynamicCommonLeviPresentations.ParabolicData θs ψpos Ts a)
    (dm : DynamicCommonLeviPresentations.ParabolicData θs ψneg Ts a)
    (op : DynamicCommonLeviPresentations.OppositeData
      (CommGroupScheme.groupHom (-dp.r.splitComponentCocharacter) ≫ a ≫ dp.l ≫ dp.p))
    (om : DynamicCommonLeviPresentations.OppositeData
      (CommGroupScheme.groupHom (-dm.r.splitComponentCocharacter) ≫ a ≫ dm.l ≫ dm.p))
    [Fintype (relativeWeylGroup dθ.r.data.i)] (B : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hadmp : (thetaConjugateRep hG hi hν I hζ n B).IsAdmissible)
    (hunitp : IsUnitarizable (thetaConjugateRep hG hi hν I hζ n B).representation)
    (hadmm : (thetaConjugateRep hG hi hν I hζ n B.contragredient).IsAdmissible)
    (hunitm : IsUnitarizable (thetaConjugateRep hG hi hν I hζ n B.contragredient).representation)
    (hθK : ∀ g : rationalPoints G, ∃ p : DynamicOppositeStandardIntertwining.parabolic θs,
      ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G)) :
    (interior (cDomain hG hi hν I I' hζ hζ' n hn K hKc B)).Nonempty := by
  have := hG.smooth
  obtain ⟨Rp, hRp⟩ := ActualCommonLeviV3.exists_threshold_mem_pairFullDomainRegion_of_data
    θs hG K hKc θs rfl hθK ψpos hpos (thetaConjugateRep hG hi hν I hζ n B) dθ dp op
    hadmp hunitp
  obtain ⟨Rm, hRm⟩ := ActualCommonLeviV3.exists_threshold_mem_pairFullDomainRegion_of_data
    θs hG K hKc θs rfl hθK ψneg hneg (thetaConjugateRep hG hi hν I hζ n B.contragredient)
    dθ dm om hadmm hunitm
  obtain ⟨w₀, hw₀p, hw₀m⟩ :=
    exists_joint_region_point hG hi hν I I' hζ hζ' n hn ha dθ dp dm op om Rp Rm
  have : Mono dθ.r.data.i.hom.hom.left := dθ.r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have : Mono (CommGroupScheme.groupHom dθ.r.data.f).hom.hom.left := by
    let := dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.mono
    let := dθ.r.isCompatible.levi.isClosedSubgroup.mono
    let := dθ.r.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a ≫ dθ.l ≫ dθ.p).hom.hom.left := by
      change Mono (a.hom.hom.left ≫ dθ.l.hom.hom.left ≫ dθ.p.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) dθ.r.isCompatible.factor_comp)
  have hV := (isOpen_parabolicUnramifiedIntertwiningRegion dθ.r
      (weylInducedCharacterForm dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.1
        dθ.r.isCompatible.maximalSplit.isSplitSubtorus.1 dθ.r.data.f dθ.r.data.i)
      dθ.n op.q op.v Rp).inter
    ((isOpen_parabolicUnramifiedIntertwiningRegion dθ.r
      (weylInducedCharacterForm dθ.r.isCompatible.splitComponent.1.isSplitSubtorus.1
        dθ.r.isCompatible.maximalSplit.isSplitSubtorus.1 dθ.r.data.f dθ.r.data.i)
      dθ.n om.q om.v Rm).preimage continuous_inv)
  have htr := (thetaCharacterTransport hG hi hν I hζ n).continuous
  obtain ⟨z₀, rfl⟩ := (thetaCharacterTransport hG hi hν I hζ n).surjective w₀
  refine ⟨z₀, mem_interior.mpr ⟨_, ?_, hV.preimage htr, ⟨hw₀p, hw₀m⟩⟩⟩
  intro z hz
  exact mem_cDomain_of_mem_pairFullDomainRegion hG hi hν I I' hζ hζ' n hn K hKc B z
    (hRp _ hz.1) (hRm _ hz.2)

include hn in
/-- **The joint convergence domain from admissibility and unitarizability of the conjugates.**
`cDomain_interior_nonempty_of_data` for one split component of the centralizer scheme of `θ_s`
and the presentations of `DynamicCommonLeviPresentations`. -/
theorem cDomain_interior_nonempty_of_unitarizable (B : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hadmp : (thetaConjugateRep hG hi hν I hζ n B).IsAdmissible)
    (hunitp : IsUnitarizable (thetaConjugateRep hG hi hν I hζ n B).representation)
    (hadmm : (thetaConjugateRep hG hi hν I hζ n B.contragredient).IsAdmissible)
    (hunitm : IsUnitarizable (thetaConjugateRep hG hi hν I hζ n B.contragredient).representation)
    (hθK : ∀ g : rationalPoints G, ∃ p : DynamicOppositeStandardIntertwining.parabolic θs,
      ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G)) :
    (interior (cDomain hG hi hν I I' hζ hζ' n hn K hKc B)).Nonempty := by
  obtain ⟨Ts, a, ha⟩ := (splitComponentStatement F (parameterScheme θs)
    (parameterScheme_isConnectedReductive θs hG)).1
  have hpos : Dynamic.centralizer ψpos = Dynamic.centralizer θs :=
    centralizer_auxiliary hG hi hν I I' hζ n hn ζ' (outerCentralizer_pos hG hi hν I' hζ')
  have hneg : Dynamic.centralizer ψneg = Dynamic.centralizer θs :=
    centralizer_auxiliary hG hi hν I I' hζ n hn (-ζ') (outerCentralizer_neg hG hi hν I' hζ')
  have dθ := DynamicCommonLeviPresentations.parabolicData θs θs hG rfl Ts a ha
  have dp := DynamicCommonLeviPresentations.parabolicData θs ψpos hG hpos Ts a ha
  have dm := DynamicCommonLeviPresentations.parabolicData θs ψneg hG hneg Ts a ha
  have op := DynamicCommonLeviPresentations.oppositeData hG
    (CommGroupScheme.groupHom (-dp.r.splitComponentCocharacter) ≫ a ≫ dp.l ≫ dp.p)
  have om := DynamicCommonLeviPresentations.oppositeData hG
    (CommGroupScheme.groupHom (-dm.r.splitComponentCocharacter) ≫ a ≫ dm.l ≫ dm.p)
  have : Finite (relativeWeylGroup dθ.r.data.i) :=
    hG.finite_relativeWeylGroup dθ.r.data.i dθ.r.isCompatible.maximalSplit
  let : Fintype (relativeWeylGroup dθ.r.data.i) := Fintype.ofFinite _
  exact cDomain_interior_nonempty_of_data hG hi hν I I' hζ hζ' n hn hKc ha hpos hneg dθ dp dm op
    om B hadmp hunitp hadmm hunitm hθK

/-- **The joint convergence domain of the c-family has nonempty interior**
(`CDomainInteriorNonemptyStatement`). A square-integrable `π` is unitarizable
(`isUnitarizable_of_isSquareIntegrableModCentralSubgroup`, the Haar measure being invariant under
inversion by `leviSplitQuotientHaar_isInvInvariant`), so is its smooth dual, and both are
admissible; conjugation to the Levi of `θ_s` preserves these properties, and
`theta_parabolic_mul_compact` gives `G(F) = (s·P)(F) K`. Then
`cDomain_interior_nonempty_of_unitarizable` applies. -/
theorem cDomainInteriorNonempty [BorelSpace (𝐌 ⧸ CM)] :
    CDomainInteriorNonemptyStatement hG hi hν I I' hζ hζ' n hn hKc sc hs π mu := by
  intro hsq hspec hPK
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  have : LocallyCompactSpace 𝐌 :=
    (isClosed_standardLeviPoints i ν (rootSet i ν I)).locallyCompactSpace
  have : mu.IsInvInvariant := leviSplitQuotientHaar_isInvInvariant hG hi hν I sc hs mu
  let hcof := compactOpenCofinal_of_nonarchimedean 𝐌
  have hunit : IsUnitarizable π.obj.representation :=
    HarishChandraSchwartz.isUnitarizable_of_isSquareIntegrableModCentralSubgroup CM hCM mu hcof hsq
  have hadm : π.obj.IsAdmissible := hsq.1
  have hdadm := (SmoothRep.isAdmissible_contragredient_iff hcof π.obj).mpr hadm
  have hdunit : IsUnitarizable π.obj.contragredient.representation := by
    obtain ⟨b⟩ := hunit
    let e := b.smoothDualEquiv hcof hadm
    exact (isUnitarizable_iff_of_conjugateEquiv
      (ρ := π.obj.representation) (σ := π.obj.contragredient.representation) e
      (b.toSmoothDual_apply_action hadm.1)).mp ⟨b⟩
  let e := thetaLeviConjugation hG hi hν I hζ n
  exact cDomain_interior_nonempty_of_unitarizable hG hi hν I I' hζ hζ' n hn hKc π.obj
    (isAdmissible_comp_continuousMulEquiv _ e.symm hadm) (hunit.comp e.symm.toMonoidHom)
    (isAdmissible_comp_continuousMulEquiv _ e.symm hdadm) (hdunit.comp e.symm.toMonoidHom)
    (theta_parabolic_mul_compact hG hi hν I hζ n hspec hPK)

end Final

end Langlands.HarishChandraSchwartz.WeakExpansion
