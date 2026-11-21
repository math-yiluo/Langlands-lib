import Langlands.Analysis.FundamentalDomainConjugateTranslation
import Langlands.Global.AdelicStandardConstantTermIntegral
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Translation by a centralizing adelic point on the fundamental domain of `P₀(F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.GroupScheme.StandardLeviFactorization

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- On every test scheme, every point of `P_J` is a point of `L_J` times a point of `U_J`. -/
theorem exists_levi_mul_unipotent (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {X : Over (Spec (CommRingCat.of k))} {g : X ⟶ G.X}
    (hg : g ∈ (standardParabolic i ν J).carrier X) :
    ∃ z ∈ (standardLevi i ν J).carrier X, ∃ x ∈ (standardUnipotent i ν J).carrier X, g = z * x := by
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  obtain ⟨hP, hL, hU⟩ := heq ζ hζ
  rw [hP] at hg
  rw [hL, hU]
  let χ := CommGroupScheme.groupHom ζ ≫ i
  let p : (Dynamic.parabolic χ).carrier X := ⟨g, hg⟩
  have hz := Dynamic.limit_mem_centralizer χ p
  have hu := Dynamic.mul_inv_limit_mem_unipotent χ p
  refine ⟨Dynamic.limit χ p, hz, (Dynamic.limit χ p)⁻¹ * (g * (Dynamic.limit χ p)⁻¹) *
    Dynamic.limit χ p, ?_, by group⟩
  have hzP := Dynamic.centralizer_le_parabolic χ X hz
  have h := Dynamic.conj_mem_unipotent χ ((Dynamic.parabolic χ).carrier X |>.inv_mem hzP) hu
  simpa using h

/-- On every test scheme, `L_J ∩ U_J` is trivial. -/
theorem eq_one_of_mem_levi_of_mem_unipotent (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {X : Over (Spec (CommRingCat.of k))} {g : X ⟶ G.X}
    (hz : g ∈ (standardLevi i ν J).carrier X) (hu : g ∈ (standardUnipotent i ν J).carrier X) :
    g = 1 := by
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  obtain ⟨_, hL, hU⟩ := heq ζ hζ
  rw [hL] at hz
  rw [hU] at hu
  exact Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent _
    (fun _ _ _ _ hl hl' => hl.unique _ hl') hz hu

end Langlands.GroupScheme.StandardLeviFactorization

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The Levi part `Λ₀ ∩ L_J(𝔸)` of `Λ₀ = P₀(F)`. -/
def leviPart (J : Set (characterLattice T)) : Subgroup (AdelicGroupPoints F G) :=
  minimalParabolicImage F G i ν ⊓ adelicPoints F G (standardLevi i ν J)

variable {hG : IsConnectedReductive G} {hi : IsMaximalSplitTorus i} {hν : IsGenericCocharacter i ν}

include hG hi hν in
theorem leviPart_mul_mem {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    (x : leviPart F G i ν J) (c : rationalSubgroup F G (standardUnipotent i ν J)) :
    (x : AdelicGroupPoints F G) *
        ((c : adelicPoints F G (standardUnipotent i ν J)) : AdelicGroupPoints F G) ∈
      minimalParabolicImage F G i ν :=
  (minimalParabolicImage F G i ν).mul_mem x.2.1
    (rationalSubgroup_standardUnipotent_le F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ _ c.2)

include hG hi hν in
/-- Uniqueness of the factorization `Λ₀ ∋ x · c`, `x ∈ L_J(𝔸)`, `c ∈ U_J(𝔸)`. -/
theorem leviPart_mul_injective {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {x₁ x₂ c₁ c₂ : AdelicGroupPoints F G}
    (hx₁ : x₁ ∈ adelicPoints F G (standardLevi i ν J)) (hx₂ : x₂ ∈ adelicPoints F G (standardLevi i ν J))
    (hc₁ : c₁ ∈ adelicPoints F G (standardUnipotent i ν J))
    (hc₂ : c₂ ∈ adelicPoints F G (standardUnipotent i ν J)) (h : x₁ * c₁ = x₂ * c₂) :
    x₁ = x₂ ∧ c₁ = c₂ := by
  have heq : x₂⁻¹ * x₁ = c₂ * c₁⁻¹ := by
    calc x₂⁻¹ * x₁ = x₂⁻¹ * (x₁ * c₁) * c₁⁻¹ := by group
      _ = x₂⁻¹ * (x₂ * c₂) * c₁⁻¹ := by rw [h]
      _ = c₂ * c₁⁻¹ := by group
  have hL : x₂⁻¹ * x₁ ∈ adelicPoints F G (standardLevi i ν J) :=
    (adelicPoints F G (standardLevi i ν J)).mul_mem
      ((adelicPoints F G (standardLevi i ν J)).inv_mem hx₂) hx₁
  have hU : x₂⁻¹ * x₁ ∈ adelicPoints F G (standardUnipotent i ν J) := by
    rw [heq]
    exact (adelicPoints F G (standardUnipotent i ν J)).mul_mem hc₂
      ((adelicPoints F G (standardUnipotent i ν J)).inv_mem hc₁)
  have h1 : x₂⁻¹ * x₁ = 1 :=
    StandardLeviFactorization.eq_one_of_mem_levi_of_mem_unipotent i ν hG hi hν hJ hL hU
  have hx : x₁ = x₂ := by
    have := congrArg (x₂ * ·) h1
    simpa using this
  refine ⟨hx, ?_⟩
  rw [hx] at h
  exact mul_left_cancel h

include hG hi hν in
/-- Existence of the factorization of points of `Λ₀`. -/
theorem exists_leviPart_mul {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {l : AdelicGroupPoints F G} (hl : l ∈ minimalParabolicImage F G i ν) :
    ∃ x : leviPart F G i ν J, ∃ c : rationalSubgroup F G (standardUnipotent i ν J),
      l = (x : AdelicGroupPoints F G) *
        ((c : adelicPoints F G (standardUnipotent i ν J)) : AdelicGroupPoints F G) := by
  obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hl
  have hqJ := minimalParabolic_le_standardParabolic F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ
    _ q.2
  obtain ⟨z, hz, x, hx, hzx⟩ :=
    StandardLeviFactorization.exists_levi_mul_unipotent i ν hG hi hν hJ hqJ
  let cx : rationalSubgroup F G (standardUnipotent i ν J) :=
    ⟨rational F G (standardUnipotent i ν J) ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
  have hcxΛ := rationalSubgroup_standardUnipotent_le F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ
    _ cx.2
  have hzval : AdelicGroupPoints.rational F G z =
      AdelicGroupPoints.rational F G q.val * (AdelicGroupPoints.rational F G x)⁻¹ := by
    rw [hzx, map_mul]
    group
  have hzΛ : AdelicGroupPoints.rational F G z ∈ minimalParabolicImage F G i ν := by
    rw [hzval]
    exact (minimalParabolicImage F G i ν).mul_mem
      (mem_minimalParabolicImage_of_rational F G i ν q.2)
      ((minimalParabolicImage F G i ν).inv_mem hcxΛ)
  refine ⟨⟨AdelicGroupPoints.rational F G z, hzΛ,
    (rational F G (standardLevi i ν J) ⟨z, hz⟩).2⟩, cx, ?_⟩
  change AdelicGroupPoints.rational F G q.val =
    AdelicGroupPoints.rational F G z * AdelicGroupPoints.rational F G x
  rw [hzx, map_mul]

/-- The bijection `(Λ₀ ∩ L_J(𝔸)) × U_J(F) ≃ Λ₀`, `(x, c) ↦ x c`. -/
def leviUnipotentEquiv (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    leviPart F G i ν J × rationalSubgroup F G (standardUnipotent i ν J) ≃
      minimalParabolicImage F G i ν :=
  Equiv.ofBijective
    (fun p => ⟨(p.1 : AdelicGroupPoints F G) *
        ((p.2 : adelicPoints F G (standardUnipotent i ν J)) : AdelicGroupPoints F G),
      leviPart_mul_mem F G i ν (hG := hG) (hi := hi) (hν := hν) hJ p.1 p.2⟩)
    ⟨by
      rintro ⟨x₁, c₁⟩ ⟨x₂, c₂⟩ h
      have h' := congrArg Subtype.val h
      obtain ⟨hx, hc⟩ := leviPart_mul_injective F G i ν (hG := hG) (hi := hi) (hν := hν) hJ
        x₁.2.2 x₂.2.2 (c₁ : adelicPoints F G (standardUnipotent i ν J)).2
        (c₂ : adelicPoints F G (standardUnipotent i ν J)).2 h'
      exact Prod.ext (Subtype.ext hx) (Subtype.ext (Subtype.ext hc)),
     by
      rintro ⟨l, hl⟩
      obtain ⟨x, c, hxc⟩ := exists_leviPart_mul F G i ν (hG := hG) (hi := hi) (hν := hν) hJ hl
      exact ⟨(x, c), Subtype.ext hxc.symm⟩⟩

theorem leviUnipotentEquiv_apply (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (p) :
    ((leviUnipotentEquiv F G i ν hG hi hν hJ p : minimalParabolicImage F G i ν) :
        AdelicGroupPoints F G) =
      (p.1 : AdelicGroupPoints F G) *
        (adelicPoints F G (standardUnipotent i ν J)).subtype p.2 := rfl

section Translation

variable (a : AdelicGroupPoints F G) {U : SubgroupFunctor G}
  (ha : ∀ w ∈ adelicPoints F G U, a * w * a⁻¹ ∈ adelicPoints F G U)
  (ha' : ∀ w ∈ adelicPoints F G U, a⁻¹ * w * a ∈ adelicPoints F G U)

/-- Conjugation by `a` on `U(𝔸)`, when `a` normalizes `U(𝔸)`. -/
def conjPoints : adelicPoints F G U ≃ₜ* adelicPoints F G U where
  toFun w := ⟨a * w * a⁻¹, ha _ w.2⟩
  invFun w := ⟨a⁻¹ * w * a, ha' _ w.2⟩
  left_inv w := Subtype.ext (by simp only; group)
  right_inv w := Subtype.ext (by simp only; group)
  map_mul' v w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

theorem coe_conjPoints (w : adelicPoints F G U) :
    ((conjPoints F G a ha ha' w : adelicPoints F G U) : AdelicGroupPoints F G) = a * w * a⁻¹ :=
  rfl

end Translation

include hG hi hν in
/-- **Translation by a point centralizing the Levi factor.** Let `a ∈ G(𝔸)` commute with every point
of `L_J(𝔸)` and normalize `U_J(𝔸)`. For every measurable `φ ≥ 0` left-invariant under `P₀(F)` and
`U_J(𝔸)`, `∫_{D₀} φ(a g) dg = c · ∫_{D₀} φ`, where `c = mulEquivHaarChar (conjPoints a)` is the factor
by which conjugation by `a` scales Haar measure on `U_J(𝔸)`. -/
theorem setLIntegral_mul_left_eq {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    (a : AdelicGroupPoints F G)
    (hlevi : ∀ x ∈ adelicPoints F G (standardLevi i ν J), a * x = x * a)
    (ha : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a * w * a⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
    (ha' : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a⁻¹ * w * a ∈ adelicPoints F G (standardUnipotent i ν J))
    {φ : AdelicGroupPoints F G → ℝ≥0∞} (hφ : Measurable φ)
    (hφΛ : ∀ l ∈ minimalParabolicImage F G i ν, ∀ x, φ (l * x) = φ x)
    (hφU : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J), ∀ x, φ (w * x) = φ x) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
      hcl.locallyCompactSpace
    ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
        (isDiscrete_minimalParabolicImage F G i ν), φ (a * g) ∂Measure.haar =
      (mulEquivHaarChar (conjPoints F G a ha ha') : ℝ≥0∞) *
        ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
          (isDiscrete_minimalParabolicImage F G i ν), φ g ∂Measure.haar := by
  let U := standardUnipotent i ν J
  let hcl : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_standardUnipotent F G i ν J
  let : LocallyCompactSpace (adelicPoints F G U) := hcl.locallyCompactSpace
  let : CompactSpace (RationalQuotient F G U) := compactSpace_standardUnipotent F G i ν hG hi hν J hJ
  let Λ := minimalParabolicImage F G i ν
  have hΛ := isDiscrete_minimalParabolicImage F G i ν
  let : Countable Λ := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  let : Countable (rationalSubgroup F G U) :=
    LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_rationalSubgroup F G U)
  have hΓ := And.intro
    (rationalSubgroup_standardUnipotent_le F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
    (conj_rationalSubgroup_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
  have hnorm := conj_adelicPoints_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ
  let : (Measure.haar : Measure (adelicPoints F G U)).IsMulRightInvariant :=
    haar_isMulRightInvariant_of_compactRationalQuotient F G U
  let : (Measure.haar : Measure (adelicPoints F G U)).IsInvInvariant :=
    ConstantTermAverage.isInvInvariant_of_isMulRightInvariant _
  have hCm : MeasurableSet (ConstantTermAverage.rationalFundamentalDomain F G U) :=
    LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_rationalSubgroup F G U)
  have hC : IsFundamentalDomain (rationalSubgroup F G U)
      (ConstantTermAverage.rationalFundamentalDomain F G U) Measure.haar :=
    LeftCosetSpace.isFundamentalDomain _ (isDiscrete_rationalSubgroup F G U) _
  let α := conjPoints F G a ha ha'
  -- conjugation scales Haar measure
  have hcomap := mulEquivHaarChar_smul_eq_comap (Measure.haar : Measure (adelicPoints F G U)) α
  have hmapsymm : Measure.map α.symm (Measure.haar : Measure (adelicPoints F G U)) =
      (Measure.haar : Measure (adelicPoints F G U)).comap α := by
    exact α.toHomeomorph.toMeasurableEquiv.map_symm
  have hqmp : Measure.QuasiMeasurePreserving α.symm (Measure.haar : Measure (adelicPoints F G U))
      Measure.haar := by
    refine ⟨α.symm.continuous.measurable, ?_⟩
    rw [hmapsymm, ← hcomap]
    exact Measure.smul_absolutelyContinuous
  have key := Langlands.Analysis.LatticeComparison.mul_setLIntegral_mul_left_eq
    (Measure.haar : Measure (AdelicGroupPoints F G)) Λ
    (LeftCosetSpace.measurableSet_fundamentalDomain Λ hΛ)
    (LeftCosetSpace.fundamentalDomain_unique Λ hΛ) (adelicPoints F G U).subtype
    continuous_subtype_val.measurable Subtype.val_injective (rationalSubgroup F G U)
    (fun w hw => hΓ.1 w hw) (fun l => ConstantTermAverage.conjEquiv F G U Λ hnorm l)
    (fun _ _ => rfl)
    (fun l w hw => (ConstantTermAverage.mem_rationalSubgroup_conjEquiv_iff F G U Λ hΓ hnorm l w).mp hw)
    Measure.haar (ConstantTermAverage.measurePreserving_conjEquiv F G U Λ hΓ hnorm) hCm hC
    (fun x : leviPart F G i ν J => (x : AdelicGroupPoints F G))
    (leviUnipotentEquiv F G i ν hG hi hν hJ) (fun p => rfl) a
    (fun x => hlevi _ x.2.2) α.toMulEquiv (fun _ => rfl) hqmp hφ (fun l x => hφΛ l l.2 x)
    (fun v x => hφU v v.2 x)
  have hC' : (Measure.haar : Measure (adelicPoints F G U))
      (α.toMulEquiv.symm ⁻¹' ConstantTermAverage.rationalFundamentalDomain F G U) =
      mulEquivHaarChar α * Measure.haar (ConstantTermAverage.rationalFundamentalDomain F G U) := by
    have himg : α.toMulEquiv.symm ⁻¹' ConstantTermAverage.rationalFundamentalDomain F G U =
        α '' ConstantTermAverage.rationalFundamentalDomain F G U :=
      (α.toHomeomorph.toEquiv.image_eq_preimage_symm _).symm
    have h1 : (Measure.haar : Measure (adelicPoints F G U)).comap α
        (ConstantTermAverage.rationalFundamentalDomain F G U) =
        Measure.haar (α '' ConstantTermAverage.rationalFundamentalDomain F G U) :=
      α.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comap_apply _ _
    rw [himg, ← h1, ← hcomap, Measure.coe_nnreal_smul_apply]
  rw [hC', mul_assoc] at key
  exact (ENNReal.mul_right_inj (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_zero U)
    (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_top U)).mp (key.trans (by ring))

end Langlands.Global.StandardConstantTerm

namespace Langlands.Global

open Langlands.GroupScheme AdelicSubgroupPoints StandardConstantTerm

/-- **Statement form.** For connected reductive `G` over a number field, a maximal split torus `i`,
a generic cocharacter `ν`, `J ⊆ Δ₀`, and `a ∈ G(𝔸)` commuting with every point of `L_J(𝔸)` and
normalizing `U_J(𝔸)`: for every measurable `φ ≥ 0` on `G(𝔸)` left-invariant under `P₀(F)` and
`U_J(𝔸)`, the integral of `φ(a ·)` over the Borel fundamental domain `D₀` of `P₀(F)` is
`mulEquivHaarChar (conjPoints a)` times the integral of `φ` over `D₀`. -/
def SplitComponentTranslationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
    ∀ J ⊆ simpleRelativeRoots i ν, ∀ (a : AdelicGroupPoints F G),
    (∀ x ∈ adelicPoints F G (standardLevi i ν J), a * x = x * a) →
    ∀ (ha : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a * w * a⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
      (ha' : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a⁻¹ * w * a ∈ adelicPoints F G (standardUnipotent i ν J))
      {φ : AdelicGroupPoints F G → ℝ≥0∞}, Measurable φ →
    (∀ l ∈ minimalParabolicImage F G i ν, ∀ x, φ (l * x) = φ x) →
    (∀ w ∈ adelicPoints F G (standardUnipotent i ν J), ∀ x, φ (w * x) = φ x) →
      haveI hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
      haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
        hcl.locallyCompactSpace
      ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
          (isDiscrete_minimalParabolicImage F G i ν), φ (a * g) ∂Measure.haar =
        (mulEquivHaarChar (conjPoints F G a ha ha') : ℝ≥0∞) *
          ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
            (isDiscrete_minimalParabolicImage F G i ν), φ g ∂Measure.haar

/-- Proof of `SplitComponentTranslationStatement`. -/
theorem splitComponentTranslation : SplitComponentTranslationStatement.{u} := by
  intro F _ _ G _ _ _ T i ν hG hi hν J hJ a hlevi ha ha' φ hφ hφΛ hφU
  exact setLIntegral_mul_left_eq F G i ν (hG := hG) (hi := hi) (hν := hν) hJ a hlevi ha ha' hφ hφΛ hφU

end Langlands.Global
