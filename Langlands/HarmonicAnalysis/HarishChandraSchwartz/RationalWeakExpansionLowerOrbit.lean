import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionLowerGeometry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitPlancherelWeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.GroupScheme.Rational.KernelCentralizerRootReduction
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar

/-! # The conjugated representation `sπ` and its orbit `sO` in the lower Levi `M'`

Waldspurger V.1 (printed pp.287–289) and the weak-part step of VI.3.1 (printed p.304) use, for
`s ∈ W(M'|G|M)` with representative `n ∈ N_G(S)(F)`, the representation `sω` of `(s·M)(F)`, its
orbit `sO` under `Im X(s·M)` and the map `χ ↦ sχ`. Here `M = M_I`, `M' = M_{I'}` is the actual
standard Levi scheme, and `s·M` is the literal Levi `levi χ_s` of the lower cocharacter
`χ_s = lowerCocharacter i ν I' ζ n` of `M'` (module `RationalWeakExpansionLowerGeometry`).

* `lowerParameterIso`: the actual centralizer scheme of `χ_s` in `M'` is isomorphic to the
  standard Levi scheme `M_I`; over `G` the isomorphism is conjugation by `n⁻¹`.
* `commonNormKernel_lowerTransport` and `lowerCharacterConjugation`: `(s·M)(F)¹ = n M_I(F)¹ n⁻¹`,
  hence `χ ↦ sχ = χ ∘ e⁻¹` is a homeomorphic isomorphism `Im X(M_I) ≃ Im X(s·M)`, where
  `e = lowerLeviConjugation : M_I(F) ≅ (s·M)(F)`, `m ↦ n m n⁻¹`.
* `lowerCentral`, `lowerMeasure`, `lowerRepresentation`: `sC = e(C)`, the image `sμ` of the Haar
  measure `μ` on `M_I(F)/C`, and `sπ = π ∘ e⁻¹`, square integrable modulo `sC`.
* `lowerClass`, `lowerOrbitMap`: `ω ↦ sω` on classes and the map `O → sO`, with
  `s(π ⊗ z) = sπ ⊗ sz`.
* `LowerDensityPackage`, `lowerPlancherelWeight`: the lower density `µ^{M'}` on `sO`.
* `lowerCharacterMeasure`: the image of a measure on `Im X(M_I)` under `χ ↦ sχ`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

/-- Two norm families with the same common kernel have the same unitary unramified
characters. -/
theorem unitaryUnramifiedCharacters_congr {M : Type*} [Group M] [TopologicalSpace M]
    {ι₁ ι₂ : Type*} {ν₁ : ι₁ → (M →* ℝ≥0ˣ)} {ν₂ : ι₂ → (M →* ℝ≥0ˣ)}
    (h : commonNormKernel ν₁ = commonNormKernel ν₂) :
    unitaryUnramifiedCharacters ν₁ = unitaryUnramifiedCharacters ν₂ := by
  ext χ
  simp only [unitaryUnramifiedCharacters, Subgroup.mem_inf]
  refine and_congr_left' ?_
  change commonNormKernel ν₁ ≤ _ ↔ commonNormKernel ν₂ ≤ _
  rw [h]

/-- The identity of `Im X` for two norm families with the same common kernel, as a
homeomorphic group isomorphism. -/
def unitaryUnramifiedCharactersCongr {M : Type*} [Group M] [TopologicalSpace M]
    {ι₁ ι₂ : Type*} {ν₁ : ι₁ → (M →* ℝ≥0ˣ)} {ν₂ : ι₂ → (M →* ℝ≥0ˣ)}
    (h : commonNormKernel ν₁ = commonNormKernel ν₂) :
    unitaryUnramifiedCharacters ν₁ ≃ₜ* unitaryUnramifiedCharacters ν₂ where
  toMulEquiv := MulEquiv.subgroupCongr (unitaryUnramifiedCharacters_congr h)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- Two norm families with the same common kernel have the same unramified characters. -/
theorem unramifiedCharacters_congr {M : Type*} [Group M] [TopologicalSpace M]
    {ι₁ ι₂ : Type*} {ν₁ : ι₁ → (M →* ℝ≥0ˣ)} {ν₂ : ι₂ → (M →* ℝ≥0ˣ)}
    (h : commonNormKernel ν₁ = commonNormKernel ν₂) :
    unramifiedCharacters ν₁ = unramifiedCharacters ν₂ := by
  ext χ
  change commonNormKernel ν₁ ≤ _ ↔ commonNormKernel ν₂ ≤ _
  rw [h]

/-- The identity of `X` for two norm families with the same common kernel, as a homeomorphic
group isomorphism. -/
def unramifiedCharactersCongr {M : Type*} [Group M] [TopologicalSpace M]
    {ι₁ ι₂ : Type*} {ν₁ : ι₁ → (M →* ℝ≥0ˣ)} {ν₂ : ι₂ → (M →* ℝ≥0ˣ)}
    (h : commonNormKernel ν₁ = commonNormKernel ν₂) :
    unramifiedCharacters ν₁ ≃ₜ* unramifiedCharacters ν₂ where
  toMulEquiv := MulEquiv.subgroupCongr (unramifiedCharacters_congr h)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerOrbitAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance lowerOrbitLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerOrbitLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "jI'" => Standard.leviHom i ν (rootSet i ν I')

/-! ### The conjugated Levi scheme -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The lower cocharacter, followed by the inclusion `M' ⊂ G`, is the conjugated cocharacter
of `T` followed by `i`. -/
theorem lowerCocharacter_comp_leviHom :
    χs ≫ jI' = CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i := by
  rw [lowerCocharacter, Category.assoc, Standard.leviTorusHom_comp]

include hG hi hν hζ hn in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The centralizer in `G` of the conjugated cocharacter lies in `M'`. -/
theorem range_centralizerHom_le_leviHom :
    SubgroupFunctor.range (Dynamic.Affine.centralizerHom (χs ≫ jI')) ≤
      SubgroupFunctor.range jI' := by
  rw [(Dynamic.Affine.isRepresentedBy_centralizerHom _).2,
    (Standard.isRepresentedBy_leviHom i ν _).2, lowerCocharacter_comp_leviHom,
    (conjugatedCocharacter_dynamic i ν (rootSet i ν I) hG hi hν (rootSet_subset i ν I) ζ hζ
      n).2.1]
  exact hn

/-- The factorization through `M'` of the centralizer scheme in `G` of the conjugated
cocharacter. -/
def lowerCentralizerFactor :
    parameterScheme (χs ≫ jI') ⟶ Standard.leviScheme i ν (rootSet i ν I') :=
  (show (SubgroupFunctor.range jI').IsRepresentedBy jI' from
    ⟨(Standard.isRepresentedBy_leviHom i ν _).1, rfl⟩).factorHom
    (Dynamic.Affine.centralizerHom (χs ≫ jI'))
    (range_centralizerHom_le_leviHom hG hi hν I I' hζ n hn)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem lowerCentralizerFactor_comp :
    lowerCentralizerFactor hG hi hν I I' hζ n hn ≫ jI' =
      Dynamic.Affine.centralizerHom (χs ≫ jI') :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- **The centralizer of `χ_s` in `M'` is the centralizer of `χ_s` in `G`.** The two actual
centralizer schemes are identified compatibly with their maps to `G`. -/
def lowerParameterIso₁ :
    parameterScheme χs ≅ parameterScheme (χs ≫ jI') :=
  haveI : Mono (jI').hom.hom := (Standard.isRepresentedBy_leviHom i ν _).1
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_centralizerHom χs)
    (Dynamic.isRepresentedBy_factorHom_centralizer jI' χs
      (Dynamic.Affine.centralizerHom (χs ≫ jI'))
      (Dynamic.Affine.isRepresentedBy_centralizerHom _)
      (range_centralizerHom_le_leviHom hG hi hν I I' hζ n hn))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem lowerParameterIso₁_hom_comp :
    (lowerParameterIso₁ hG hi hν I I' hζ n hn).hom ≫ Dynamic.Affine.centralizerHom (χs ≫ jI') =
      Dynamic.Affine.centralizerHom χs ≫ jI' := by
  have : Mono (jI').hom.hom := (Standard.isRepresentedBy_leviHom i ν _).1
  rw [← lowerCentralizerFactor_comp hG hi hν I I' hζ n hn, ← Category.assoc]
  congr 1
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- **Conjugation by `n`** identifies the centralizer scheme of `ζ ∘ i` with that of the
conjugated cocharacter `χ_s` (viewed in `G`), by the inner automorphism `Int(n)` of `G`. -/
def lowerParameterIso₂ :
    parameterScheme (CommGroupScheme.groupHom ζ ≫ i) ≅ parameterScheme (χs ≫ jI') :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap
    (Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ i))
    (Dynamic.Affine.isRepresentedBy_centralizerHom (χs ≫ jI'))
    (G.innerIso (n : rationalPoints G)) (by
      rw [lowerCocharacter_comp]
      exact (Dynamic.centralizer_eq_comap_of_iso _ _).symm)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem lowerParameterIso₂_inv_comp :
    (lowerParameterIso₂ I' n).inv ≫ Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.Affine.centralizerHom (χs ≫ jI') ≫ (G.innerIso (n : rationalPoints G)).inv :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap_inv_comp _ _ _ _

/-- **The conjugated Levi scheme.** The actual centralizer scheme of the lower cocharacter
`χ_s` in `M'` is identified with the standard Levi scheme `M_I`. On points it is
`m' ↦ n⁻¹ m' n` (`lowerParameterIso_hom_comp`). -/
def lowerParameterIso :
    parameterScheme χs ≅ Standard.leviScheme i ν (rootSet i ν I) :=
  lowerParameterIso₁ hG hi hν I I' hζ n hn ≪≫ (lowerParameterIso₂ I' n).symm ≪≫
    Langlands.Plancherel.standardLeviParameterIso hG hi hν I hζ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Over `G`, the conjugated Levi scheme identification is conjugation by `n⁻¹`. -/
theorem lowerParameterIso_hom_comp :
    (lowerParameterIso hG hi hν I I' hζ n hn).hom ≫ Standard.leviHom i ν (rootSet i ν I) =
      Dynamic.Affine.centralizerHom χs ≫ jI' ≫ (G.innerIso (n : rationalPoints G)).inv := by
  simp only [lowerParameterIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Langlands.Plancherel.standardLeviParameterIso_hom_comp, lowerParameterIso₂_inv_comp]
  rw [← Category.assoc, lowerParameterIso₁_hom_comp, Category.assoc]

/-! ### The conjugation `M_I(F) ≅ (s·M)(F)` on points and characters -/

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

set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

/-- On points, the conjugated Levi scheme identification is the inverse of the conjugation
`m ↦ n m n⁻¹` of `lowerLeviConjugation`. -/
theorem leviRationalPointHomeomorph_lowerParameterIso (y : rationalPoints (parameterScheme χs)) :
    ((leviRationalPointHomeomorph i ν I
        (rationalPoints.map (lowerParameterIso hG hi hν I I' hζ n hn).hom y) : levi i ν I) :
        rationalPoints G) =
      ((eₛ).symm (parameterHomeomorph χs y) : rationalPoints G) := by
  rw [leviRationalPointHomeomorph_apply_coe, lowerLeviConjugation_symm_coe,
    rationalPoints.map_apply, rationalPoints.map_apply, parameterHomeomorph_apply_coe]
  have h := congrArg (fun f => y ≫ f.hom.hom) (lowerParameterIso_hom_comp hG hi hν I I' hζ n hn)
  simp only [Grp.comp_hom_hom, Category.assoc] at h ⊢
  rw [h]
  have hc := DFunLike.congr_fun (rationalPoints_map_innerIso_inv (n : rationalPoints G))
    (y ≫ (Dynamic.Affine.centralizerHom χs).hom.hom ≫ (jI').hom.hom)
  rw [rationalPoints.map_apply] at hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Category.assoc] at hc
  exact hc

omit [LocallyOfFiniteType G.X.hom] in
/-- The conjugated Levi scheme identification preserves and reflects the actual norm-one
subgroups `(s·M)¹` and `M_I¹`. -/
theorem map_lowerParameterIso_mem_iff (y : rationalPoints (parameterScheme χs)) :
    rationalPoints.map (lowerParameterIso hG hi hν I I' hζ n hn).hom y ∈
        rationalCommonNormKernel (Standard.leviScheme i ν (rootSet i ν I)) ↔
      y ∈ rationalCommonNormKernel (parameterScheme χs) := by
  constructor
  · intro hy
    have h := rationalCommonNormKernel_le_comap (lowerParameterIso hG hi hν I I' hζ n hn).inv hy
    simpa only [Subgroup.mem_comap, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using h
  · exact fun hy => rationalCommonNormKernel_le_comap _ hy

/-- **`(s·M)(F)¹ = n M_I(F)¹ n⁻¹`.** The norm-one subgroup of the literal Levi `(s·M)(F)` for
its own rational characters is the one obtained from `M_I(F)` by the conjugation `e`. -/
theorem commonNormKernel_lowerTransport :
    commonNormKernel (fun ψ => (leviRationalNormCharacters i ν I ψ).comp
        (eₛ).symm.toMulEquiv.toMonoidHom) =
      commonNormKernel (leviNormCharacters χs) := by
  ext m'
  obtain ⟨y, rfl⟩ := (parameterHomeomorph χs).surjective m'
  have key : (eₛ).symm (parameterHomeomorph χs y) = leviRationalPointHomeomorph i ν I
      (rationalPoints.map (lowerParameterIso hG hi hν I I' hζ n hn).hom y) :=
    Subtype.ext (leviRationalPointHomeomorph_lowerParameterIso hG hi hν I I' hζ n hn y).symm
  rw [mem_commonNormKernel, mem_commonNormKernel]
  show (∀ ψ, leviRationalNormCharacters i ν I ψ ((eₛ).symm (parameterHomeomorph χs y)) = 1) ↔
    ∀ ψ, normCharacters χs ψ ((parameterHomeomorph χs).symm (parameterHomeomorph χs y)) = 1
  rw [key, ContinuousMulEquiv.symm_apply_apply]
  simp only [leviRationalNormCharacters_apply_points]
  exact (mem_commonNormKernel _ _).symm.trans
    ((map_lowerParameterIso_mem_iff hG hi hν I I' hζ n hn y).trans (mem_commonNormKernel _ _))


/-- **The conjugation `χ ↦ sχ` of unitary unramified characters**, `Im X(M_I) ≃ Im X(s·M)`,
`z ↦ z ∘ e⁻¹`, where `e : M_I(F) ≅ (s·M)(F)` is `m ↦ n m n⁻¹`. -/
def lowerCharacterConjugation :
    unitaryUnramifiedCharacters (leviRationalNormCharacters i ν I) ≃ₜ*
      unitaryUnramifiedCharacters (leviNormCharacters χs) :=
  (unitaryUnramifiedCharactersHomeomorph eₛ (leviRationalNormCharacters i ν I)).trans
    (unitaryUnramifiedCharactersCongr (commonNormKernel_lowerTransport hG hi hν I I' hζ n hn))

/-- The conjugated character is `z ∘ e⁻¹`. -/
theorem lowerCharacterConjugation_apply
    (z : unitaryUnramifiedCharacters (leviRationalNormCharacters i ν I)) (m' : levi χs) :
    (lowerCharacterConjugation hG hi hν I I' hζ n hn z).val m' = z.val ((eₛ).symm m') :=
  rfl

/-- **The conjugation `χ ↦ sχ` of unramified characters**, `X(M_I) ≃ X(s·M)`, `z ↦ z ∘ e⁻¹`:
the complex version of `lowerCharacterConjugation`, used for the c-family at non-unitary
points. -/
def lowerUnramifiedCharacterConjugation :
    unramifiedCharacters (leviRationalNormCharacters i ν I) ≃ₜ*
      unramifiedCharacters (leviNormCharacters χs) :=
  (unramifiedCharactersHomeomorph eₛ (leviRationalNormCharacters i ν I)).trans
    (unramifiedCharactersCongr (commonNormKernel_lowerTransport hG hi hν I I' hζ n hn))

/-- The conjugated character is `z ∘ e⁻¹`. -/
theorem lowerUnramifiedCharacterConjugation_apply
    (z : unramifiedCharacters (leviRationalNormCharacters i ν I)) (m' : levi χs) :
    (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z).val m' = z.val ((eₛ).symm m') :=
  rfl

/-! ### The conjugated representation `sπ` and its orbit `sO` -/

-- `M_I(F)` as a subtype of `G(F)`, written as in `standardLeviPlancherelWeight`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}

variable (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)

/-- The conjugated central subgroup `sC = n C n⁻¹` of `(s·M)(F)`. -/
def lowerCentral : Subgroup (levi χs) :=
  C.map (eₛ).toMulEquiv.toMonoidHom

instance lowerCentral_normal : (lowerCentral hG hi hν I I' hζ n hn C).Normal :=
  Subgroup.Normal.map inferInstance _ (eₛ).surjective

omit [C.Normal] in
include hC in
theorem lowerCentral_le_center :
    lowerCentral hG hi hν I I' hζ n hn C ≤ Subgroup.center (levi χs) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨m, rfl⟩ := (eₛ).surjective g
  have h := Subgroup.mem_center_iff.mp (hC hc) m
  change eₛ m * eₛ c = eₛ c * eₛ m
  rw [← map_mul, ← map_mul, h]

omit [C.Normal] in
theorem lowerCentral_map_symm :
    (lowerCentral hG hi hν I I' hζ n hn C).map (eₛ).symm.toMulEquiv.toMonoidHom = C := by
  rw [lowerCentral, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id C]
  congr 1
  exact MonoidHom.ext fun m => (eₛ).symm_apply_apply m

/-- The quotient isomorphism `(s·M)(F)/sC ≅ M_I(F)/C` induced by `e⁻¹`. -/
abbrev lowerQuotientEquiv :
    (levi χs ⧸ lowerCentral hG hi hν I I' hζ n hn C) ≃ₜ* (𝐌 ⧸ C) :=
  quotientContinuousMulEquiv (eₛ).symm C (lowerCentral hG hi hν I I' hζ n hn C)
    (lowerCentral_map_symm hG hi hν I I' hζ n hn C)

instance lowerQuotientMeasurableSpace :
    MeasurableSpace (levi χs ⧸ lowerCentral hG hi hν I I' hζ n hn C) := borel _
instance lowerQuotientBorelSpace :
    BorelSpace (levi χs ⧸ lowerCentral hG hi hν I I' hζ n hn C) := ⟨rfl⟩

variable [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C))
  [mu.IsHaarMeasure]

/-- The transported Haar measure `sμ` on `(s·M)(F)/sC`: the image of `μ` under the quotient
isomorphism induced by `e`. -/
def lowerMeasure : Measure (levi χs ⧸ lowerCentral hG hi hν I I' hζ n hn C) :=
  mu.map (lowerQuotientEquiv hG hi hν I I' hζ n hn C).symm

instance lowerMeasure_isHaarMeasure :
    (lowerMeasure hG hi hν I I' hζ n hn C mu).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map _ _

omit [mu.IsHaarMeasure] in
theorem lowerMeasure_map :
    (lowerMeasure hG hi hν I I' hζ n hn C mu).map (lowerQuotientEquiv hG hi hν I I' hζ n hn C) =
      mu := by
  rw [lowerMeasure, Measure.map_map
    (map_continuous (lowerQuotientEquiv hG hi hν I I' hζ n hn C)).measurable
    (map_continuous (lowerQuotientEquiv hG hi hν I I' hζ n hn C).symm).measurable]
  convert Measure.map_id
  ext x
  exact (lowerQuotientEquiv hG hi hν I I' hζ n hn C).apply_symm_apply x

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- **The conjugated representation `sπ`** of `(s·M)(F)`: `sπ(m') = π(n⁻¹ m' n)` on the space
of `π`. -/
def lowerRepresentation : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi χs) :=
  IrreducibleAdmissibleRep.pullback (eₛ).symm π

include hsq in
/-- `sπ` is square integrable modulo `sC` for `sμ`. -/
theorem lowerRepresentation_isSquareIntegrable :
    IsSquareIntegrableModCentralSubgroup (lowerCentral hG hi hν I I' hζ n hn C)
      (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
      (lowerRepresentation hG hi hν I I' hζ n hn π).obj.representation
      (lowerMeasure hG hi hν I I' hζ n hn C mu) :=
  (isSquareIntegrableModCentralSubgroup_comp_iff (eₛ).symm C hC
    (lowerCentral hG hi hν I I' hζ n hn C) (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
    (lowerCentral_map_symm hG hi hν I I' hζ n hn C) mu (lowerMeasure hG hi hν I I' hζ n hn C mu)
    (lowerMeasure_map hG hi hν I I' hζ n hn C mu) π.obj.representation).mpr hsq

/-- The conjugation `ω ↦ sω = ω ∘ e⁻¹` of discrete-series classes modulo `C` and `sC`. -/
def lowerClass :
    DiscreteSeriesClass.{u, uV} C hC mu →
      DiscreteSeriesClass.{u, uV} (lowerCentral hG hi hν I I' hζ n hn C)
        (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
        (lowerMeasure hG hi hν I I' hζ n hn C mu) :=
  DiscreteSeriesClass.pullback (eₛ).symm C hC (lowerCentral hG hi hν I I' hζ n hn C)
    (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
    (lowerCentral_map_symm hG hi hν I I' hζ n hn C) mu (lowerMeasure hG hi hν I I' hζ n hn C mu)
    (lowerMeasure_map hG hi hν I I' hζ n hn C mu)

/-- Conjugation of classes is compatible with twisting: `s(ω ⊗ z) = sω ⊗ sz`. -/
theorem lowerClass_smul (z : unitaryUnramifiedCharacters (leviRationalNormCharacters i ν I))
    (ω : DiscreteSeriesClass.{u, uV} C hC mu) :
    lowerClass hG hi hν I I' hζ n hn C hC mu (z • ω) =
      lowerCharacterConjugation hG hi hν I I' hζ n hn z •
        lowerClass hG hi hν I I' hζ n hn C hC mu ω := by
  apply Subtype.ext
  exact SmoothDualClass.pullback_twist (eₛ).symm _ _ _ ω.val

/-- The class of `π` is carried to the class of `sπ`. -/
theorem lowerClass_discreteSeriesClass :
    lowerClass hG hi hν I I' hζ n hn C hC mu (discreteSeriesClass C hC mu π hsq) =
      discreteSeriesClass (lowerCentral hG hi hν I I' hζ n hn C)
        (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
        (lowerMeasure hG hi hν I I' hζ n hn C mu) (lowerRepresentation hG hi hν I I' hζ n hn π)
        (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C hC mu π hsq) :=
  rfl

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu (leviRationalNormCharacters i ν I)
  (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "sOπ" => discreteSeriesOrbit (lowerCentral hG hi hν I I' hζ n hn C)
  (lowerCentral_le_center hG hi hν I I' hζ n hn C hC) (lowerMeasure hG hi hν I I' hζ n hn C mu)
  (leviNormCharacters χs)
  (discreteSeriesClass (lowerCentral hG hi hν I I' hζ n hn C)
    (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
    (lowerMeasure hG hi hν I I' hζ n hn C mu) (lowerRepresentation hG hi hν I I' hζ n hn π)
    (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C hC mu π hsq))

/-- **The conjugated orbit map `O → sO`**, `ω ↦ sω`. -/
def lowerOrbitMap : Oπ → sOπ := fun ω =>
  ⟨lowerClass hG hi hν I I' hζ n hn C hC mu ω.val, by
    obtain ⟨z, hz⟩ := ω.property
    refine ⟨lowerCharacterConjugation hG hi hν I I' hζ n hn z, ?_⟩
    change _ = lowerClass hG hi hν I I' hζ n hn C hC mu ω.val
    rw [← hz, lowerClass_smul]
    rfl⟩

/-- On the orbit parameterization, `s(π ⊗ z) = sπ ⊗ sz`. -/
theorem lowerOrbitMap_orbitMap
    (z : unitaryUnramifiedCharacters (leviRationalNormCharacters i ν I)) :
    lowerOrbitMap hG hi hν I I' hζ n hn C hC mu π hsq
        (discreteSeriesOrbitMap C hC mu (leviRationalNormCharacters i ν I)
          (discreteSeriesClass C hC mu π hsq) z) =
      discreteSeriesOrbitMap (lowerCentral hG hi hν I I' hζ n hn C)
        (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
        (lowerMeasure hG hi hν I I' hζ n hn C mu) (leviNormCharacters χs)
        (discreteSeriesClass (lowerCentral hG hi hν I I' hζ n hn C)
          (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
          (lowerMeasure hG hi hν I I' hζ n hn C mu) (lowerRepresentation hG hi hν I I' hζ n hn π)
          (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C hC mu π hsq))
        (lowerCharacterConjugation hG hi hν I I' hζ n hn z) := by
  apply Subtype.ext
  exact lowerClass_smul hG hi hν I I' hζ n hn C hC mu z _

/-- The unitary stabilizer of `sπ` is finite when that of `π` is: conjugation of characters
carries the first injectively into the second. -/
theorem finite_lowerStabilizer
    [Finite (discreteSeriesStabilizer C hC mu (leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC mu π hsq))] :
    Finite (discreteSeriesStabilizer (lowerCentral hG hi hν I I' hζ n hn C)
      (lowerCentral_le_center hG hi hν I I' hζ n hn C hC) (lowerMeasure hG hi hν I I' hζ n hn C mu)
      (leviNormCharacters χs)
      (discreteSeriesClass (lowerCentral hG hi hν I I' hζ n hn C)
        (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
        (lowerMeasure hG hi hν I I' hζ n hn C mu) (lowerRepresentation hG hi hν I I' hζ n hn π)
        (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C hC mu π hsq))) := by
  let c := lowerCharacterConjugation hG hi hν I I' hζ n hn
  refine Finite.of_injective (β := discreteSeriesStabilizer C hC mu
    (leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq))
    (fun τ => ⟨c.symm τ.val, ?_⟩) ?_
  · change c.symm τ.val • discreteSeriesClass C hC mu π hsq = discreteSeriesClass C hC mu π hsq
    apply DiscreteSeriesClass.pullback_injective (eₛ).symm C hC
      (lowerCentral hG hi hν I I' hζ n hn C) (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
      (lowerCentral_map_symm hG hi hν I I' hζ n hn C) mu (lowerMeasure hG hi hν I I' hζ n hn C mu)
      (lowerMeasure_map hG hi hν I I' hζ n hn C mu)
    change lowerClass hG hi hν I I' hζ n hn C hC mu (c.symm τ.val • _) =
      lowerClass hG hi hν I I' hζ n hn C hC mu _
    rw [lowerClass_smul, ContinuousMulEquiv.apply_symm_apply]
    exact τ.property
  · intro τ τ' h
    exact Subtype.ext (c.symm.injective (congrArg Subtype.val h))

/-! ### The lower Plancherel density `µ^{M'}` and the transported character measure -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
/-- The lower ambient group `M' = M_{I'}` is connected reductive. -/
theorem lowerAmbient_isConnectedReductive :
    IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I')) :=
  BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν (rootSet i ν I')
    (rootSet_subset i ν I')

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hi in
/-- The torus of `M'` through which `χ_s` factors is a maximal split torus of `M'`, so the
package weight of `DynamicOrbitPlancherelWeight` is Waldspurger's density `µ^{M'}`. -/
theorem lowerTorus_isMaximalSplitTorus :
    IsMaximalSplitTorus (Standard.leviTorusHom i ν (rootSet i ν I')) :=
  Standard.isMaximalSplitTorus_leviTorusHom i ν _ hi

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

/-- **The lower density package for `s`** (Waldspurger V.2, printed p.292, for the ambient group
`M'` and its parabolic `M' ∩ s·P`): the explicit analytic inputs of the Plancherel density of
`sπ` relative to `M' ∩ s·P` inside `M'`, for the maximal split torus
`Standard.leviTorusHom i ν I'` of `M'` and the conjugated cocharacter `sζ`. -/
abbrev LowerDensityPackage :=
  DynamicInducedOrbit.DensityPackage (Standard.leviTorusHom i ν (rootSet i ν I'))
    (conjugatedCocharacter i ζ n) hRefl hCST (lowerAmbient_isConnectedReductive hG hi hν I')
    (lowerRepresentation hG hi hν I I' hζ n hn π).obj

/-- **The lower density `µ^{M'}` on `sO`**: `sω ↦ µ^{M'}(sω)`, the Plancherel weight of the
lower density package on the orbit of `sπ`. -/
def lowerPlancherelWeight (P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST) :
    sOπ → ℂ :=
  @DynamicInducedOrbit.orbitPlancherelWeight _ _ _ _ _ _ _ _ _
    (Standard.leviTorusHom i ν (rootSet i ν I'))
    (conjugatedCocharacter i ζ n) hRefl hCST (lowerAmbient_isConnectedReductive hG hi hν I')
    (lowerRepresentation hG hi hν I I' hζ n hn π) (lowerCentral hG hi hν I I' hζ n hn C)
    (lowerCentral_normal hG hi hν I I' hζ n hn C)
    (lowerCentral_le_center hG hi hν I I' hζ n hn C hC)
    (lowerQuotientMeasurableSpace hG hi hν I I' hζ n hn C) (lowerMeasure hG hi hν I I' hζ n hn C mu)
    (lowerMeasure_isHaarMeasure hG hi hν I I' hζ n hn C mu)
    (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C hC mu π hsq) P

/-- **The transported character measure** on `Im X(s·M)`: the image of a measure `ρ` on
`Im X(M_I)` under `χ ↦ sχ`. -/
def lowerCharacterMeasure
    (ρ : Measure (unitaryUnramifiedCharacters (leviRationalNormCharacters i ν I))) :
    Measure (unitaryUnramifiedCharacters (leviNormCharacters χs)) :=
  ρ.map (lowerCharacterConjugation hG hi hν I I' hζ n hn)

end WeakExpansion

end Langlands.HarishChandraSchwartz
