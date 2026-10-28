import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData
import Langlands.HarmonicAnalysis.StableIntegral
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.LocalFactor.Abelian.Padic

/-!
# Stabilized lower Jacquet data for the strict rank-one extension

JPSS (1983), Lemma (5.5), printed page 424, formula (1): the Whittaker functional
of the lower induction is the limit, over an exhaustion by compact open subgroups,
of truncated integrals of the scalar contraction of a section against the character.
This module defines the actual scalar integrand on the row coordinates of the upper
cell, its compact-open stable graph, the domain of sections where it stabilizes, the
linear stable value on that domain and a conditional extension. It asserts no
stabilization for any particular section.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg

open HarmonicAnalysis

universe uF uW

section Row

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The integral rows `𝒪^(t+1)` form a compact open additive subgroup of the actual
row space, so the generic stable-integral domain is available. -/
theorem rankOneExtensionRow_exists_compactOpen (t : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ∃ K : OpenAddSubgroup (Fin (t + 1) → F.Carrier),
      IsCompact (K : Set (Fin (t + 1) → F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let L : Set (Fin (t + 1) → F.Carrier) :=
    Set.univ.pi fun _ => (T.Integers : Set F.Carrier)
  have hL (y : Fin (t + 1) → F.Carrier) : y ∈ L ↔ ∀ i, y i ∈ T.Integers := by
    simp [L]
  refine ⟨{ carrier := L
            zero_mem' := (hL 0).mpr fun _ => T.Integers.zero_mem
            add_mem' := fun {x y} hx hy => (hL (x + y)).mpr fun i =>
              T.Integers.add_mem ((hL x).mp hx i) ((hL y).mp hy i)
            neg_mem' := fun {x} hx => (hL (-x)).mpr fun i =>
              T.Integers.neg_mem ((hL x).mp hx i)
            isOpen' := isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_integers }, ?_⟩
  exact isCompact_univ_pi fun _ => T.isCompact_integers

end Row

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
  (ψ : letI := F.canonicalTopologicalData.topology;
    UnitaryAdditiveCharacter F.Carrier)
  (ℓ : letI := F.canonicalTopologicalData.topology;
    Whittaker.glInverseFunctionals ψ t σ)

/-- The actual induced right action of `h` on the section carrier, transported through
`asModuleEquiv`. -/
def rankOneExtensionLowerTranslate (h : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    rankOneExtensionLowerSection F t χ σ →ₗ[ℂ] rankOneExtensionLowerSection F t χ σ :=
  (rankOneExtensionLowerModel F t χ σ).asModuleEquiv.symm.toLinearMap ∘ₗ
    rankOneExtensionLowerModel F t χ σ h ∘ₗ
      (rankOneExtensionLowerModel F t χ σ).asModuleEquiv.toLinearMap

theorem rankOneExtensionLowerTranslate_asModuleEquiv
    (h : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionLowerSection F t χ σ) :
    (rankOneExtensionLowerModel F t χ σ).asModuleEquiv
        (rankOneExtensionLowerTranslate F t χ σ h f) =
      rankOneExtensionLowerModel F t χ σ h
        ((rankOneExtensionLowerModel F t χ σ).asModuleEquiv f) :=
  rfl

/-- The translate by `h` evaluates at `g` as the original section at `g * h`. -/
theorem rankOneExtensionLowerSectionEval_translate
    (h g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionLowerSection F t χ σ) :
    rankOneExtensionLowerSectionEval F t χ σ (rankOneExtensionLowerTranslate F t χ σ h f) g =
      rankOneExtensionLowerSectionEval F t χ σ f (g * h) :=
  rfl

/-- The scalar integrand `y ↦ ℓ(f(u(y) g)) ψ(y_last)` on the row coordinates of the
complementary upper cell, with the positive character. -/
def rankOneExtensionStableIntegrand (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (y : Fin (t + 1) → F.Carrier) : ℂ :=
  letI := F.canonicalTopologicalData.topology
  rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f (rankOneExtensionUpperCell t y * g) *
    ψ.complex (y (Fin.last t))

theorem rankOneExtensionStableIntegrand_apply (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) (y : Fin (t + 1) → F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g y =
      rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
          (rankOneExtensionUpperCell t y * g) *
        ψ.complex (y (Fin.last t)) :=
  rfl

/-- The integrand at a fixed ambient element, as a complex linear map of the section. -/
def rankOneExtensionStableIntegrandMap
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    rankOneExtensionLowerSection F t χ σ →ₗ[ℂ] (Fin (t + 1) → F.Carrier) → ℂ where
  toFun f := rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g
  map_add' f f' := by
    funext y
    change rankOneExtensionWhittakerContraction F t σ ψ ℓ
        (rankOneExtensionLowerSectionEval F t χ σ f (rankOneExtensionUpperCell t y * g) +
          rankOneExtensionLowerSectionEval F t χ σ f' (rankOneExtensionUpperCell t y * g)) *
        _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' c f := by
    funext y
    change rankOneExtensionWhittakerContraction F t σ ψ ℓ
        (c • rankOneExtensionLowerSectionEval F t χ σ f
          (rankOneExtensionUpperCell t y * g)) * _ = _
    rw [map_smul, smul_eq_mul, mul_assoc]
    rfl

@[simp] theorem rankOneExtensionStableIntegrandMap_apply
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionLowerSection F t χ σ) :
    rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ g f =
      rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g :=
  rfl

/-- Translating the section by `h` under the actual induced right action replaces the
ambient element `g` by `g * h`. -/
theorem rankOneExtensionStableIntegrand_translate
    (h g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionLowerSection F t χ σ) :
    rankOneExtensionStableIntegrand F t χ σ ψ ℓ (rankOneExtensionLowerTranslate F t χ σ h f) g =
      rankOneExtensionStableIntegrand F t χ σ ψ ℓ f (g * h) := by
  funext y
  change rankOneExtensionWhittakerContraction F t σ ψ ℓ
      (rankOneExtensionLowerSectionEval F t χ σ f (rankOneExtensionUpperCell t y * g * h)) *
      _ = _
  rw [mul_assoc]
  rfl

variable (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- The stable graph: the integrand at `(f, g)` has compact-open stable integral `z`
against the product of the supplied self-dual measure on the rows. -/
def HasRankOneExtensionStableJacquetAt (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) (z : ℂ) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  HasStableIntegral (rowMeasure ν.val (t + 1))
    (rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g) z

variable {F t χ σ ψ ℓ ν}

/-- The stable value at `(f, g)` is unique. -/
theorem HasRankOneExtensionStableJacquetAt.unique
    {f : rankOneExtensionLowerSection F t χ σ}
    {g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier} {z w : ℂ}
    (hz : HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f g z)
    (hw : HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f g w) : z = w :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  HasStableIntegral.unique hz hw

/-- The graph is compatible with the actual induced right action. -/
theorem hasRankOneExtensionStableJacquetAt_translate_iff
    (h g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionLowerSection F t χ σ) (z : ℂ) :
    HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν
        (rankOneExtensionLowerTranslate F t χ σ h f) g z ↔
      HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f (g * h) z := by
  unfold HasRankOneExtensionStableJacquetAt
  rw [rankOneExtensionStableIntegrand_translate]

variable (F t χ σ ψ ℓ ν)

/-- Sections whose integrand stabilizes at the fixed ambient element `g`. -/
def rankOneExtensionStableDomainAt
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    Submodule ℂ (rankOneExtensionLowerSection F t χ σ) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  (stableIntegrableSubmodule (rowMeasure ν.val (t + 1))
    (rankOneExtensionRow_exists_compactOpen F t)).comap
      (rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ g)

/-- Sections whose integrand stabilizes at every ambient element. -/
def rankOneExtensionStableDomain : Submodule ℂ (rankOneExtensionLowerSection F t χ σ) :=
  ⨅ g, rankOneExtensionStableDomainAt F t χ σ ψ ℓ ν g

variable {F t χ σ ψ ℓ ν}

theorem mem_rankOneExtensionStableDomainAt
    {g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier}
    {f : rankOneExtensionLowerSection F t χ σ} :
    f ∈ rankOneExtensionStableDomainAt F t χ σ ψ ℓ ν g ↔
      ∃ z, HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f g z :=
  Iff.rfl

theorem mem_rankOneExtensionStableDomain {f : rankOneExtensionLowerSection F t χ σ} :
    f ∈ rankOneExtensionStableDomain F t χ σ ψ ℓ ν ↔
      ∀ g, ∃ z, HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f g z := by
  simp only [rankOneExtensionStableDomain, Submodule.mem_iInf,
    mem_rankOneExtensionStableDomainAt]

/-- The global stable domain is the whole section space exactly when every section
stabilizes at every ambient element. -/
theorem rankOneExtensionStableDomain_eq_top_iff :
    rankOneExtensionStableDomain F t χ σ ψ ℓ ν = ⊤ ↔
      ∀ (f : rankOneExtensionLowerSection F t χ σ)
        (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier),
        ∃ z, HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f g z := by
  rw [Submodule.eq_top_iff']
  exact forall_congr' fun _ => mem_rankOneExtensionStableDomain

/-- The global stable domain is invariant under the actual induced right action. -/
theorem rankOneExtensionLowerTranslate_mem_stableDomain
    (h : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    {f : rankOneExtensionLowerSection F t χ σ}
    (hf : f ∈ rankOneExtensionStableDomain F t χ σ ψ ℓ ν) :
    rankOneExtensionLowerTranslate F t χ σ h f ∈ rankOneExtensionStableDomain F t χ σ ψ ℓ ν := by
  rw [mem_rankOneExtensionStableDomain] at hf ⊢
  intro g
  obtain ⟨z, hz⟩ := hf (g * h)
  exact ⟨z, (hasRankOneExtensionStableJacquetAt_translate_iff h g f z).mpr hz⟩

theorem rankOneExtensionStableDomain_le_at
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    rankOneExtensionStableDomain F t χ σ ψ ℓ ν ≤
      rankOneExtensionStableDomainAt F t χ σ ψ ℓ ν g :=
  iInf_le _ g

variable (F t χ σ ψ ℓ ν)

/-- The actual induced right action restricted to the global stable domain. -/
def rankOneExtensionStableDomainTranslate
    (h : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    rankOneExtensionStableDomain F t χ σ ψ ℓ ν →ₗ[ℂ]
      rankOneExtensionStableDomain F t χ σ ψ ℓ ν :=
  (rankOneExtensionLowerTranslate F t χ σ h).restrict fun _ hf =>
    rankOneExtensionLowerTranslate_mem_stableDomain h hf

/-- The stable value at `g` on the global stable domain, chosen through the published
`stableIntegral` from the proved stabilization; no default value is used. -/
def rankOneExtensionStableValueAt
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    rankOneExtensionStableDomain F t χ σ ψ ℓ ν →ₗ[ℂ] ℂ :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  (stableIntegral (rowMeasure ν.val (t + 1)) (rankOneExtensionRow_exists_compactOpen F t)).comp
    (LinearMap.codRestrict _
      ((rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ g).comp
        (rankOneExtensionStableDomain F t χ σ ψ ℓ ν).subtype)
      fun f => rankOneExtensionStableDomain_le_at g f.property)

/-- The stable functional: the stable value at the identity. -/
def rankOneExtensionStableFunctional :
    rankOneExtensionStableDomain F t χ σ ψ ℓ ν →ₗ[ℂ] ℂ :=
  rankOneExtensionStableValueAt F t χ σ ψ ℓ ν 1

variable {F t χ σ ψ ℓ ν}

@[simp] theorem rankOneExtensionStableDomainTranslate_val
    (h : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionStableDomain F t χ σ ψ ℓ ν) :
    (rankOneExtensionStableDomainTranslate F t χ σ ψ ℓ ν h f).val =
      rankOneExtensionLowerTranslate F t χ σ h f.val :=
  rfl

/-- The stable value satisfies the defining stable graph. -/
theorem hasRankOneExtensionStableJacquetAt_stableValueAt
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionStableDomain F t χ σ ψ ℓ ν) :
    HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f.val g
      (rankOneExtensionStableValueAt F t χ σ ψ ℓ ν g f) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  hasStableIntegral_stableIntegral (rankOneExtensionRow_exists_compactOpen F t)
    ⟨rankOneExtensionStableIntegrand F t χ σ ψ ℓ f.val g,
      rankOneExtensionStableDomain_le_at g f.property⟩

/-- Uniqueness characterization of the stable value. -/
theorem rankOneExtensionStableValueAt_eq_iff
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionStableDomain F t χ σ ψ ℓ ν) (z : ℂ) :
    rankOneExtensionStableValueAt F t χ σ ψ ℓ ν g f = z ↔
      HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f.val g z := by
  constructor
  · rintro rfl
    exact hasRankOneExtensionStableJacquetAt_stableValueAt g f
  · exact (hasRankOneExtensionStableJacquetAt_stableValueAt g f).unique

theorem hasRankOneExtensionStableJacquetAt_stableFunctional
    (f : rankOneExtensionStableDomain F t χ σ ψ ℓ ν) :
    HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f.val 1
      (rankOneExtensionStableFunctional F t χ σ ψ ℓ ν f) :=
  hasRankOneExtensionStableJacquetAt_stableValueAt 1 f

theorem rankOneExtensionStableFunctional_eq_iff
    (f : rankOneExtensionStableDomain F t χ σ ψ ℓ ν) (z : ℂ) :
    rankOneExtensionStableFunctional F t χ σ ψ ℓ ν f = z ↔
      HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f.val 1 z :=
  rankOneExtensionStableValueAt_eq_iff 1 f z

/-- Right translation by `h` moves the stable value from `g` to `g * h`. -/
theorem rankOneExtensionStableValueAt_translate
    (h g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionStableDomain F t χ σ ψ ℓ ν) :
    rankOneExtensionStableValueAt F t χ σ ψ ℓ ν g
        (rankOneExtensionStableDomainTranslate F t χ σ ψ ℓ ν h f) =
      rankOneExtensionStableValueAt F t χ σ ψ ℓ ν (g * h) f := by
  rw [rankOneExtensionStableValueAt_eq_iff, rankOneExtensionStableDomainTranslate_val,
    hasRankOneExtensionStableJacquetAt_translate_iff]
  exact hasRankOneExtensionStableJacquetAt_stableValueAt (g * h) f

/-- Evaluation identity: the stable functional of the translate by `g` is the stable
value at `g`. -/
theorem rankOneExtensionStableFunctional_translate
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionStableDomain F t χ σ ψ ℓ ν) :
    rankOneExtensionStableFunctional F t χ σ ψ ℓ ν
        (rankOneExtensionStableDomainTranslate F t χ σ ψ ℓ ν g f) =
      rankOneExtensionStableValueAt F t χ σ ψ ℓ ν g f :=
  (rankOneExtensionStableValueAt_translate g 1 f).trans
    (congrArg (fun x => rankOneExtensionStableValueAt F t χ σ ψ ℓ ν x f) (one_mul g))

variable (F t χ σ ψ ℓ ν)

/-- Given a proof that every section stabilizes at every ambient element, the stable
functional on the whole actual section space. -/
def rankOneExtensionStableExtension
    (hall : rankOneExtensionStableDomain F t χ σ ψ ℓ ν = ⊤) :
    rankOneExtensionLowerSection F t χ σ →ₗ[ℂ] ℂ :=
  (rankOneExtensionStableFunctional F t χ σ ψ ℓ ν).comp
    (LinearMap.codRestrict _ LinearMap.id fun f => Submodule.eq_top_iff'.mp hall f)

variable {F t χ σ ψ ℓ ν}

theorem rankOneExtensionStableExtension_apply
    (hall : rankOneExtensionStableDomain F t χ σ ψ ℓ ν = ⊤)
    (f : rankOneExtensionLowerSection F t χ σ) :
    rankOneExtensionStableExtension F t χ σ ψ ℓ ν hall f =
      rankOneExtensionStableFunctional F t χ σ ψ ℓ ν ⟨f, Submodule.eq_top_iff'.mp hall f⟩ :=
  rfl

/-- The extension satisfies the stable graph at the identity. -/
theorem hasRankOneExtensionStableJacquetAt_stableExtension
    (hall : rankOneExtensionStableDomain F t χ σ ψ ℓ ν = ⊤)
    (f : rankOneExtensionLowerSection F t χ σ) :
    HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f 1
      (rankOneExtensionStableExtension F t χ σ ψ ℓ ν hall f) := by
  rw [rankOneExtensionStableExtension_apply]
  exact hasRankOneExtensionStableJacquetAt_stableFunctional ⟨f, Submodule.eq_top_iff'.mp hall f⟩

theorem rankOneExtensionStableExtension_eq_iff
    (hall : rankOneExtensionStableDomain F t χ σ ψ ℓ ν = ⊤)
    (f : rankOneExtensionLowerSection F t χ σ) (z : ℂ) :
    rankOneExtensionStableExtension F t χ σ ψ ℓ ν hall f = z ↔
      HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f 1 z :=
  rankOneExtensionStableFunctional_eq_iff _ z

/-- Right translation: the extension at the translate of `f` by `g` is the stable
value of `f` at `g`. -/
theorem hasRankOneExtensionStableJacquetAt_stableExtension_translate
    (hall : rankOneExtensionStableDomain F t χ σ ψ ℓ ν = ⊤)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
    (f : rankOneExtensionLowerSection F t χ σ) :
    HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f g
      (rankOneExtensionStableExtension F t χ σ ψ ℓ ν hall
        (rankOneExtensionLowerTranslate F t χ σ g f)) := by
  have h := hasRankOneExtensionStableJacquetAt_stableExtension hall
    (rankOneExtensionLowerTranslate F t χ σ g f)
  rwa [hasRankOneExtensionStableJacquetAt_translate_iff, one_mul] at h

end Padic

end Langlands.RankinSelberg
