import Langlands.HarmonicAnalysis.RenardHomogeneousStatements
import Langlands.HarmonicAnalysis.Distribution.RenardModularProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Sheaf.Renard.HomogeneousSections
import Langlands.Representation.Induction.OpenAdjunction

/-! # Renard II.3.9: quotient, compact-induction and module comparisons -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

open Langlands.Algebra Langlands.Sheaf.Renard
open Langlands.Induction (LeftQuotient quotientMap quotientMap_eq_iff)
open scoped Pointwise NNReal

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard

universe uG

section Coset

variable {G : Type uG} [Group G] (H : Subgroup G)

theorem quotientMap_mul_left (h : H) (x : G) :
    quotientMap H (h.val * x) = quotientMap H x := by
  rw [quotientMap_eq_iff]
  simpa only [mul_inv_rev, mul_inv_cancel_left] using H.inv_mem h.property

theorem mem_mul_iff_quotientMap (S : Set G) (x : G) :
    x ∈ (H : Set G) * S ↔ ∃ s ∈ S, quotientMap H s = quotientMap H x := by
  constructor
  · rintro ⟨h, hh, s, hs, rfl⟩
    exact ⟨s, hs, (quotientMap_mul_left H ⟨h, hh⟩ s).symm⟩
  · rintro ⟨s, hs, he⟩
    rw [quotientMap_eq_iff] at he
    exact ⟨x * s⁻¹, he, s, hs, by group⟩

theorem preimage_image_quotientMap (S : Set G) :
    quotientMap H ⁻¹' (quotientMap H '' S) = (H : Set G) * S := by
  ext x
  rw [mem_mul_iff_quotientMap]
  rfl

end Coset

section Space

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (χ : H →* ℝ≥0)

theorem character_ne_zero (h : H) : ((χ h : ℝ) : ℂ) ≠ 0 := by
  have hm : χ h * χ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hne : χ h ≠ 0 := left_ne_zero_of_mul_eq_one hm
  exact_mod_cast hne

theorem apply_mul_ne_zero_iff (f : space H χ) (h : H) (x : G) :
    f.val (h.val * x) ≠ 0 ↔ f.val x ≠ 0 := by
  rw [f.property.1 h x]
  exact ⟨fun hx => right_ne_zero_of_mul hx,
    fun hx => mul_ne_zero (character_ne_zero H χ h) hx⟩

theorem support_subset_mul (f : space H χ) {S : Set G}
    (hS : Function.support f.val ⊆ (H : Set G) * S) (x : G) (hx : f.val x ≠ 0) :
    ∃ s ∈ S, quotientMap H s = quotientMap H x :=
  (mem_mul_iff_quotientMap H S x).mp (hS hx)

theorem preimage_image_support (f : space H χ) :
    quotientMap H ⁻¹' (quotientMap H '' Function.support f.val) =
      Function.support f.val := by
  ext x
  constructor
  · rintro ⟨s, hs, he⟩
    rw [quotientMap_eq_iff] at he
    have hx := (apply_mul_ne_zero_iff H χ f ⟨x * s⁻¹, he⟩ s).mpr hs
    show f.val x ≠ 0
    simpa only [inv_mul_cancel_right] using hx
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isClopen_support (f : space H χ) : IsClopen (Function.support f.val) :=
  (f.val.isLocallyConstant.isClopen_fiber 0).compl

theorem isClosed_image_support (f : space H χ) :
    IsClosed (quotientMap H '' Function.support f.val) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isClosed_preimage.mp
  change IsClosed (quotientMap H ⁻¹' (quotientMap H '' Function.support f.val))
  rw [preimage_image_support]
  exact (isClopen_support H χ f).isClosed

theorem image_support_subset (f : space H χ) {K : Set G}
    (hK : Function.support f.val ⊆ (H : Set G) * K) :
    quotientMap H '' Function.support f.val ⊆ quotientMap H '' K := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, he⟩ := support_subset_mul H χ f hK x hx
  exact ⟨s, hs, he⟩

theorem isCompact_image_support (f : space H χ) :
    IsCompact (quotientMap H '' Function.support f.val) := by
  obtain ⟨K, hK, hs⟩ := f.property.2
  exact (hK.image continuous_quotient_mk').of_isClosed_subset
    (isClosed_image_support H χ f) (image_support_subset H χ f hs)

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_compactOpenSubgroup :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) := by
  obtain ⟨K, -, hK, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ ⊤
  exact ⟨K, hK⟩

/-- A compact set of the quotient lifts to a compact set of the group. -/
theorem exists_compact_lift {C : Set (LeftQuotient H)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ C ⊆ quotientMap H '' K := by
  obtain ⟨K₀, hK₀⟩ := exists_compactOpenSubgroup (G := G)
  let U : G → Set (LeftQuotient H) := fun g =>
    quotientMap H '' ((fun x => g * x) '' (K₀ : Set G))
  have hU : ∀ g, IsOpen (U g) := fun g =>
    (QuotientIntegration.leftQuotient_isOpenQuotientMap H).isOpenMap _
      (isOpenMap_mul_left g _ K₀.isOpen)
  have hcover : C ⊆ ⋃ g, U g := by
    intro c _
    induction c using Quotient.inductionOn with
    | h g =>
      exact Set.mem_iUnion.mpr ⟨g, g, ⟨1, K₀.one_mem, mul_one g⟩, rfl⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU hcover
  refine ⟨⋃ g ∈ t, (fun x => g * x) '' (K₀ : Set G),
    t.isCompact_biUnion fun g _ => hK₀.image (continuous_const.mul continuous_id), ?_⟩
  intro c hc
  obtain ⟨g, hg, hcg⟩ := Set.mem_iUnion₂.mp (ht hc)
  obtain ⟨y, hy, rfl⟩ := hcg
  exact ⟨y, Set.mem_iUnion₂.mpr ⟨g, hg, hy⟩, rfl⟩

/-- Every vector of the twisted space has one compact open right stabilizer. -/
theorem exists_uniform_stabilizer (f : space H χ) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ (k : K) (x : G), f.val (x * k) = f.val x := by
  classical
  obtain ⟨Kf, hKf, hs⟩ := f.property.2
  obtain ⟨K₀, hK₀⟩ := exists_compactOpenSubgroup (G := G)
  let U : Set G := Kf * (K₀ : Set G)
  have hUc : IsCompact U := hKf.mul hK₀
  have hUo : IsOpen U := K₀.isOpen.mul_left
  let φ : SchwartzBruhat G :=
    Distribution.multiplyTest f.val
      (Hecke.TestFunction.characteristic ⟨hUc.isClosed, hUo⟩ hUc)
  obtain ⟨K, hKK₀, hK, hφ⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G {φ} K₀
  have hφK := (hφ φ (Finset.mem_singleton_self φ)).2
  refine ⟨K, hK, ?_⟩
  have hbase : ∀ (k : K) (y : G), y ∈ Kf → f.val (y * k) = f.val y := by
    intro k y hy
    have hyU : y ∈ U := ⟨y, hy, 1, K₀.one_mem, mul_one y⟩
    have hykU : y * k ∈ U := ⟨y, hy, k, hKK₀ k.property, rfl⟩
    have he := hφK k y
    simp only [φ, Distribution.multiplyTest_apply,
      Hecke.TestFunction.characteristic_apply, Set.indicator_of_mem hyU,
      Set.indicator_of_mem hykU, mul_one] at he
    exact he
  have hsupp : ∀ (k : K) (y : G), f.val y ≠ 0 → f.val (y * k) = f.val y := by
    intro k y hy
    obtain ⟨h, hh, z, hz, rfl⟩ := hs hy
    rw [mul_assoc, f.property.1 ⟨h, hh⟩, f.property.1 ⟨h, hh⟩, hbase k z hz]
  intro k x
  by_cases hx : f.val x = 0
  · by_cases hxk : f.val (x * k) = 0
    · rw [hx, hxk]
    · have h1 := hsupp k⁻¹ (x * k) hxk
      have h2 : x * (k : G) * ((k⁻¹ : K) : G) = x := by simp
      rw [h2] at h1
      exact absurd (h1.symm.trans hx) hxk
  · exact hsupp k x hx

theorem isLocallyConstant_of_stabilizer {F : G → ℂ} (K : OpenSubgroup G)
    (hF : ∀ (k : K) (x : G), F (x * k) = F x) : IsLocallyConstant F := by
  apply (IsLocallyConstant.iff_exists_open F).mpr
  intro x
  refine ⟨(fun k => x * k) '' (K : Set G), isOpenMap_mul_left x _ K.isOpen,
    ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact hF ⟨k, hk⟩ x

theorem compactModulo_of_image {F : LocallyConstant G ℂ}
    (hc : IsCompact (quotientMap H '' Function.support F)) : CompactModulo H F := by
  obtain ⟨K, hK, hCK⟩ := exists_compact_lift H hc
  refine ⟨K, hK, ?_⟩
  intro x hx
  rw [mem_mul_iff_quotientMap]
  obtain ⟨s, hs, he⟩ := hCK ⟨x, hx, rfl⟩
  exact ⟨s, hs, he⟩

end Space

/-! ## Conjunct 3: pullback of quotient tests -/

section QuotientTests

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable (H : Subgroup G) (χ : H →* ℝ≥0)

theorem continuous_quotientMap : Continuous (quotientMap H) :=
  continuous_quotient_mk'

/-- Pull back a quotient test along the projection `G → H\G`. -/
def pullbackTest (hχ : ∀ h, χ h = 1) (f : SchwartzBruhat (LeftQuotient H)) : space H χ :=
  ⟨⟨fun x => f (quotientMap H x),
      f.locallyConstant.comp_continuous (continuous_quotientMap H)⟩, by
    refine ⟨?_, ?_⟩
    · intro h x
      change f (quotientMap H (h.val * x)) = ((χ h : ℝ) : ℂ) * f (quotientMap H x)
      rw [quotientMap_mul_left, hχ h]
      simp
    · obtain ⟨K, hK, hCK⟩ := exists_compact_lift H f.hasCompactSupport
      refine ⟨K, hK, ?_⟩
      intro x hx
      rw [mem_mul_iff_quotientMap]
      obtain ⟨s, hs, he⟩ := hCK (subset_tsupport _ hx)
      exact ⟨s, hs, he⟩⟩

@[simp]
theorem pullbackTest_apply (hχ : ∀ h, χ h = 1) (f : SchwartzBruhat (LeftQuotient H)) (x : G) :
    (pullbackTest H χ hχ f).val x = f (quotientMap H x) := rfl

/-- Descend an `H`-invariant compactly supported-modulo-`H` function to `H\G`. -/
def descendTest (hχ : ∀ h, χ h = 1) (F : space H χ) : SchwartzBruhat (LeftQuotient H) :=
  ⟨QuotientIntegration.descend H F.val (fun h g => by
      rw [F.property.1 h g, hχ h]
      simp), by
    refine ⟨?_, ?_⟩
    · intro s
      apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isOpen_preimage.mp
      exact F.val.isLocallyConstant s
    · have hsub : Function.support (QuotientIntegration.descend H F.val (fun h g => by
          rw [F.property.1 h g, hχ h]
          simp)) ⊆ quotientMap H '' Function.support F.val := by
        intro c hc
        induction c using Quotient.inductionOn with
        | h x => exact ⟨x, hc, rfl⟩
      exact (isCompact_image_support H χ F).of_isClosed_subset isClosed_closure
        (closure_minimal hsub (isClosed_image_support H χ F))⟩

theorem descendTest_apply (hχ : ∀ h, χ h = 1) (F : space H χ) (x : G) :
    descendTest H χ hχ F (quotientMap H x) = F.val x := rfl

/-- The comparison of quotient tests with the twisted space for a trivial character. -/
def quotientTestEquiv (hχ : ∀ h, χ h = 1) :
    SchwartzBruhat (LeftQuotient H) ≃ₗ[ℂ] space H χ where
  toFun := pullbackTest H χ hχ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := descendTest H χ hχ
  left_inv f := by
    apply Subtype.ext
    funext c
    induction c using Quotient.inductionOn with
    | h x => rfl
  right_inv F := rfl

theorem quotientTest : QuotientTestStatement.{uG} := by
  intro G _ _ _ _ _ _ H hH hχ
  exact ⟨quotientTestEquiv H (relativeModular H hH) hχ, fun _ _ => rfl⟩

end QuotientTests

/-! ## Conjunct 4: comparison with compact induction -/

section CompactInduction

open Langlands.Induction (CompactFunctions compactFunctionOf eval compactInduced
  EquivariantFunctions SmoothCharacter)

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable (H : Subgroup G) (χ : H →* ℝ≥0) (ψ : H →* ℂˣ)

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] in
theorem characterRepresentation_apply (h : H) (v : ℂ) :
    Langlands.characterRepresentation ψ h v = (ψ h : ℂ) * v := rfl

variable {χ ψ}

/-- The twisted function, viewed as a compactly induced function. -/
def toCompact (hψ : ∀ h, (ψ h : ℂ) = ((χ h : ℝ) : ℂ)) (f : space H χ) :
    CompactFunctions H (Langlands.characterRepresentation ψ) :=
  compactFunctionOf H _ f.val
    (fun p x => by rw [characterRepresentation_apply, hψ]; exact f.property.1 p x)
    (Classical.choose (exists_uniform_stabilizer H χ f))
    (Classical.choose_spec (exists_uniform_stabilizer H χ f)).2
    (isCompact_image_support H χ f)

theorem eval_isLocallyConstant (F : CompactFunctions H (Langlands.characterRepresentation ψ)) :
    IsLocallyConstant (eval H (Langlands.characterRepresentation ψ) F.1) := by
  obtain ⟨K, hK⟩ := F.1.property
  apply isLocallyConstant_of_stabilizer K
  intro k x
  exact congrArg (fun F' : EquivariantFunctions H (Langlands.characterRepresentation ψ) =>
    F'.1 x) (hK k)

/-- A compactly induced function, viewed as a twisted function. -/
def ofCompact (hψ : ∀ h, (ψ h : ℂ) = ((χ h : ℝ) : ℂ))
    (F : CompactFunctions H (Langlands.characterRepresentation ψ)) : space H χ :=
  ⟨⟨eval H _ F.1, eval_isLocallyConstant H F⟩, by
    refine ⟨?_, ?_⟩
    · intro h x
      have := F.1.1.property h x
      rw [characterRepresentation_apply, hψ] at this
      exact this
    · exact compactModulo_of_image H F.2⟩

/-- The identity-on-values comparison with compact induction. -/
def compactEquiv (hψ : ∀ h, (ψ h : ℂ) = ((χ h : ℝ) : ℂ)) :
    space H χ ≃ₗ[ℂ] CompactFunctions H (Langlands.characterRepresentation ψ) where
  toFun := toCompact H hψ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := ofCompact H hψ
  left_inv _ := rfl
  right_inv _ := rfl

theorem compactEquiv_rightAction (hψ : ∀ h, (ψ h : ℂ) = ((χ h : ℝ) : ℂ)) (g : G)
    (f : space H χ) :
    compactEquiv H hψ (rightAction H χ g f) =
      compactInduced H (Langlands.characterRepresentation ψ) g (compactEquiv H hψ f) := rfl

/-- The relative character as a unit-valued character of `H`. -/
def relativeUnits (hH : IsClosed (H : Set G)) : H →* ℂˣ :=
  ((Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom.comp
    (relativeModular H hH)).toHomUnits

theorem relativeUnits_apply (hH : IsClosed (H : Set G)) (h : H) :
    (relativeUnits H hH h : ℂ) = ((relativeModular H hH h : ℝ) : ℂ) := rfl

theorem relativeModular_isLocallyConstant (hH : IsClosed (H : Set G)) :
    IsLocallyConstant (relativeModular H hH) := by
  let _ : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hG := (Distribution.RenardModular.regularity G).2.1
  have hH' := (Distribution.RenardModular.regularity H).2.1
  have h1 : IsLocallyConstant (fun h : H => Distribution.renardModular h.val) :=
    hG.comp_continuous continuous_subtype_val
  exact h1.comp₂ hH' (· / ·)

/-- The relative character as a smooth character in the compact-induction interface. -/
def relativeCharacter (hH : IsClosed (H : Set G)) : SmoothCharacter ℂ H where
  toMonoidHom := relativeUnits H hH
  isOpen_ker := by
    have h := ((relativeModular_isLocallyConstant H hH).comp
      (fun r : ℝ≥0 => (((Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom.comp
        (MonoidHom.id ℝ≥0)) r))).isOpen_fiber 1
    convert h using 1
    ext h
    simp only [MonoidHom.coe_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Units.val_eq_one]
    rfl

theorem compactInduction : CompactInductionStatement.{uG} := by
  intro G _ _ _ _ _ _ H hH
  refine ⟨relativeCharacter H hH, fun h => rfl, compactEquiv H (relativeUnits_apply H hH),
    fun _ _ => rfl, compactEquiv_rightAction H (relativeUnits_apply H hH)⟩

end CompactInduction

/-! ## Conjunct 5: the pointwise test-algebra action and its projector sheaf -/

section Pointwise

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable (H : Subgroup G) (χ : H →* ℝ≥0)

/-- Pull back a pointwise quotient test to a locally constant function on `G`. -/
def pullbackFunction (a : PointwiseTestAlgebra.Carrier (LeftQuotient H)) :
    LocallyConstant G ℂ :=
  ⟨fun x => a (quotientMap H x), a.1.isLocallyConstant.comp_continuous (continuous_quotientMap H)⟩

/-- Multiplication by a pulled-back quotient test preserves the twisted space. -/
def pointwiseSMul (a : PointwiseTestAlgebra.Carrier (LeftQuotient H)) (f : space H χ) :
    space H χ :=
  ⟨pullbackFunction H a * f.val, by
    refine ⟨?_, ?_⟩
    · intro h x
      change a (quotientMap H (h.val * x)) * f.val (h.val * x) =
        ((χ h : ℝ) : ℂ) * (a (quotientMap H x) * f.val x)
      rw [quotientMap_mul_left, f.property.1 h x, mul_left_comm]
    · obtain ⟨K, hK, hs⟩ := f.property.2
      refine ⟨K, hK, ?_⟩
      intro x hx
      apply hs
      intro hz
      exact hx (by change a (quotientMap H x) * f.val x = 0; rw [hz, mul_zero])⟩

theorem pointwiseSMul_apply (a : PointwiseTestAlgebra.Carrier (LeftQuotient H))
    (f : space H χ) (x : G) :
    (pointwiseSMul H χ a f).val x = a (quotientMap H x) * f.val x := rfl

/-- The pointwise action of quotient tests on the twisted space. -/
@[reducible]
def pointwiseModule :
    NonUnitalModule (PointwiseTestAlgebra.Carrier (LeftQuotient H)) (space H χ) where
  smul := pointwiseSMul H χ
  smul_zero a := Subtype.ext <| LocallyConstant.ext fun x => by
    show a (quotientMap H x) * 0 = 0
    exact mul_zero _
  smul_add a f g := Subtype.ext <| LocallyConstant.ext fun x => by
    show a (quotientMap H x) * (f.val x + g.val x) =
      a (quotientMap H x) * f.val x + a (quotientMap H x) * g.val x
    exact mul_add _ _ _
  mul_smul a b f := Subtype.ext <| LocallyConstant.ext fun x => by
    show a (quotientMap H x) * b (quotientMap H x) * f.val x =
      a (quotientMap H x) * (b (quotientMap H x) * f.val x)
    exact mul_assoc _ _ _
  add_smul a b f := Subtype.ext <| LocallyConstant.ext fun x => by
    show (a (quotientMap H x) + b (quotientMap H x)) * f.val x =
      a (quotientMap H x) * f.val x + b (quotientMap H x) * f.val x
    exact add_mul _ _ _
  zero_smul f := Subtype.ext <| LocallyConstant.ext fun x => by
    show 0 * f.val x = 0
    exact zero_mul _

theorem isOpen_image_support (f : space H χ) :
    IsOpen (quotientMap H '' Function.support f.val) :=
  (QuotientIntegration.leftQuotient_isOpenQuotientMap H).isOpenMap _
    (isClopen_support H χ f).isOpen

theorem pointwise_nondegenerate :
    letI := pointwiseModule H χ
    IsNondegenerate (PointwiseTestAlgebra.Carrier (LeftQuotient H)) (space H χ) := by
  let _ := pointwiseModule H χ
  intro f
  refine ⟨PointwiseTestAlgebra.characteristicIdempotent
    (U := quotientMap H '' Function.support f.val)
    ⟨isClosed_image_support H χ f, isOpen_image_support H χ f⟩
    (isCompact_image_support H χ f), ?_⟩
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  show (quotientMap H '' Function.support f.val).indicator (fun _ => (1 : ℂ))
    (quotientMap H x) * f.val x = f.val x
  by_cases hx : f.val x = 0
  · rw [hx, mul_zero]
  · rw [Set.indicator_of_mem
      (show quotientMap H x ∈ quotientMap H '' Function.support f.val from ⟨x, hx, rfl⟩),
      one_mul]

theorem action_eq_self_iff (hQ : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))
    (U : ProjectorBasisSheaf.CompactOpen hQ) (f : space H χ) :
    letI := pointwiseModule H χ
    ProjectorBasisSheaf.action hQ (space H χ) U f = f ↔
      Function.support f.val ⊆ quotientMap H ⁻¹' (U.obj : Set _) := by
  let _ := pointwiseModule H χ
  have hval : ∀ x, (ProjectorBasisSheaf.action hQ (space H χ) U f).val x =
      (U.obj : Set _).indicator (fun _ => (1 : ℂ)) (quotientMap H x) * f.val x :=
    fun x => rfl
  constructor
  · intro he x hx
    by_contra hU
    have hU' : quotientMap H x ∉ (U.obj : Set _) := hU
    have hx' := congrArg (fun F : space H χ => F.val x) he
    simp only [hval, Set.indicator_of_notMem hU', zero_mul] at hx'
    exact hx hx'.symm
  · intro hs
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    rw [hval]
    by_cases hx : f.val x = 0
    · rw [hx, mul_zero]
    · rw [Set.indicator_of_mem (show quotientMap H x ∈ (U.obj : Set _) from hs hx), one_mul]

theorem pointwiseModuleSheaf : PointwiseModuleSheafStatement.{uG} := by
  intro G _ _ _ _ _ _ H hH
  refine ⟨Langlands.Sheaf.Renard.HomogeneousSections.quotient_isLocallyProfinite H
    Langlands.Topology.isLocallyProfinite_of_mathlib hH,
    pointwiseModule H (relativeModular H hH), ?_⟩
  intro V F
  refine ⟨pointwise_nondegenerate H _, fun a f g => rfl,
    fun U f => action_eq_self_iff H _ _ U f, ?_⟩
  intro U W h s g
  rfl

end Pointwise

end Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard
