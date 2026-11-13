import Langlands.Sheaf.Renard.FibreCoinvariantStalk
import Langlands.Sheaf.Renard.FibreCoinvariantRestriction

/-!
# Renard III.3.1: the stalk of the coinvariant sheaf is the fibre coinvariants
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.FibreCoinvariantProof

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.ProjectorBasisSheaf

attribute [local instance] CompatibleTestAction.complexModule

/-- Two equal module structures give the same scalar multiplication. -/
theorem smul_of_module_eq {V : Type} [AddCommGroup V] {I J : Module ℂ V} (h : I = J)
    (c : ℂ) (v : V) : (letI := I; c • v) = (letI := J; c • v) := by
  subst h
  rfl

variable {G : Type} [Group G] [TopologicalSpace G]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [ContinuousSMul G X]
variable (hX : Langlands.Topology.IsLocallyProfinite X)
variable (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
variable (hY : Langlands.Topology.IsLocallyProfinite Y) (y : Y)

/-- The compactly supported global sections, with their natural complex structure. -/
abbrev Sections (F : ActionSheaf G X) : Type :=
  CompactSupport.submodule (CompactSections.ordinary F.obj)

/-- The compact-section test action of `F`. -/
abbrev testAction (F : ActionSheaf G X) : CompatibleTestAction G X :=
  CompactSectionActions.compatibleObject hX F

/-- The natural and the recovered complex structures agree on compact sections. -/
def sectionsEquiv (F : ActionSheaf G X) :
    Sections F ≃ₗ[ℂ] (testAction hX F).module.obj where
  toFun a := a
  invFun a := a
  map_add' _ _ := rfl
  map_smul' c a := (CompactSectionActions.canonicalScalar_eq hX F c a).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coinvariant module of `F` on `Y`. -/
abbrev coinvariantModule (F : ActionSheaf G X) :=
  (CoinvariantSheaf.modules hX q hq hY).obj F

/-- The library quotient structure and Renard's recovered structure agree on coinvariants. -/
def coinvariantEquiv (F : ActionSheaf G X) :
    letI := ProjectorVectorSheaf.originalModule (coinvariantModule hX q hq hY F).property
    Representation.Coinvariants (testAction hX F).action ≃ₗ[ℂ]
      (coinvariantModule hX q hq hY F).obj :=
  letI := ProjectorVectorSheaf.originalModule (coinvariantModule hX q hq hY F).property
  { toFun := fun a => a
    invFun := fun a => a
    map_add' := fun _ _ => rfl
    map_smul' := fun c a =>
      (smul_of_module_eq (CoinvariantTestModule.canonicalComplex_eq q hq hY
        (testAction hX F)) c a).symm
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The stalk at `y` of Renard's sheaf, as the ordinary stalk of its presheaf. -/
abbrev stalkY (F : ActionSheaf G X) :=
  (ProjectorVectorSheaf.presheaf.{0,0} hY (coinvariantModule hX q hq hY F).property).stalk y

/-- `α`: compact section ↦ germ at `y` of its coinvariant class. -/
def alpha (F : ActionSheaf G X) : Sections F →ₗ[ℂ] stalkY hX q hq hY y F :=
  letI := ProjectorVectorSheaf.originalModule (coinvariantModule hX q hq hY F).property
  (FibreCoinvariantStalk.stalkGerm hY (coinvariantModule hX q hq hY F).property y).comp
    ((coinvariantEquiv hX q hq hY F).toLinearMap.comp
      ((Representation.Coinvariants.mk (testAction hX F).action).comp
        (sectionsEquiv hX F).toLinearMap))

theorem alpha_apply (F : ActionSheaf G X) (a : Sections F) :
    alpha hX q hq hY y F a =
      FibreCoinvariantStalk.stalkGerm hY (coinvariantModule hX q hq hY F).property y
        (Representation.Coinvariants.mk (testAction hX F).action a) := rfl

/-- The germ of a pulled-back test multiple is the pointwise multiple of the germ. -/
theorem germ_multiplier (F : ActionSheaf G X) (f : PointwiseTestAlgebra.Carrier Y)
    (a : Sections F) (x : X) :
    (CompactSections.ordinary F.obj).Γgerm x ((sectionsEquiv hX F).symm
        (CoinvariantTestModule.multiplier q (testAction hX F) f (sectionsEquiv hX F a))).val =
      f (q x) • (CompactSections.ordinary F.obj).Γgerm x a.val := by
  obtain ⟨U, hU, hc, hm⟩ := PointwiseTestModule.exists_characteristic_fixer
    (testAction hX F).module.property (sectionsEquiv hX F a)
  have h := PointwiseTestModule.smul_eq (testAction hX F).module.property
    (CoinvariantTestModule.pullback q f) (sectionsEquiv hX F a) hU hc hm
  have h2 := CompactSectionTestModule.Γgerm_testSmul (underlying F)
    (CoinvariantTestModule.pullback q f • PointwiseTestAlgebra.characteristic hU hc)
    (sectionsEquiv hX F a) x
  have h3 := CompactSectionTestModule.Γgerm_testSmul (underlying F)
    (PointwiseTestAlgebra.characteristic hU hc) (sectionsEquiv hX F a) x
  rw [hm] at h3
  have h1 := congrArg (fun s : (testAction hX F).module.obj =>
    (CompactSections.ordinary F.obj).Γgerm x ((sectionsEquiv hX F).symm s).val) h
  refine h1.trans (h2.trans ?_)
  by_cases hx : x ∈ U
  · change (CoinvariantTestModule.pullback q f x *
      PointwiseTestAlgebra.characteristic hU hc x) • _ = _
    rw [PointwiseTestAlgebra.characteristic_apply, Set.indicator_of_mem hx, mul_one]
    rfl
  · rw [PointwiseTestAlgebra.characteristic_apply, Set.indicator_of_notMem hx, zero_smul] at h3
    erw [h3, smul_zero, smul_zero]

/-- The kernel of `α`: a compact-open neighbourhood test of `y` kills the coinvariant class. -/
theorem alpha_eq_zero_iff (F : ActionSheaf G X) (a : Sections F) :
    alpha hX q hq hY y F a = 0 ↔ ∃ K : CompactOpen hY, y ∈ K.obj ∧
      CoinvariantTestModule.multiplier q (testAction hX F) (test hY K) (sectionsEquiv hX F a) ∈
        Representation.Coinvariants.ker (testAction hX F).action := by
  rw [alpha_apply, FibreCoinvariantStalk.stalkGerm_eq_zero_iff]
  refine exists_congr fun K => and_congr_right fun _ => ?_
  change Representation.Coinvariants.mk (testAction hX F).action
    (CoinvariantTestModule.multiplier q (testAction hX F) (test hY K) a) = 0 ↔ _
  exact Representation.Coinvariants.mk_eq_zero _

/-- A compact section with zero germs along the fibre is killed by a neighbourhood test. -/
theorem exists_multiplier_eq_zero (F : ActionSheaf G X) (a : Sections F)
    (ha : ∀ x : X, q x = y → (CompactSections.ordinary F.obj).Γgerm x a.val = 0) :
    ∃ K : CompactOpen hY, y ∈ K.obj ∧
      CoinvariantTestModule.multiplier q (testAction hX F) (test hY K) (sectionsEquiv hX F a) =
        0 := by
  let := hY.t2Space
  have hSc : IsCompact (CompactSupport.support (CompactSections.ordinary F.obj) a.val) :=
    a.property
  have hyS : y ∉ q '' CompactSupport.support (CompactSections.ordinary F.obj) a.val := by
    rintro ⟨x, hx, hxy⟩
    exact hx (ha x hxy)
  obtain ⟨K, hyK, hKS⟩ := FibreCoinvariantStalk.exists_compactOpen_le hY y
    (U := ⟨_, (hSc.image q.continuous).isClosed.isOpen_compl⟩) hyS
  refine ⟨K, hyK, ?_⟩
  apply (sectionsEquiv hX F).symm.injective
  rw [map_zero]
  apply Subtype.ext
  apply TopCat.Presheaf.section_ext (underlying F) ⊤
  intro x _
  change (CompactSections.ordinary F.obj).Γgerm x ((sectionsEquiv hX F).symm
      (CoinvariantTestModule.multiplier q (testAction hX F) (test hY K)
        (sectionsEquiv hX F a))).val =
    (CompactSections.ordinary F.obj).Γgerm x (0 : Sections F).val
  rw [germ_multiplier, ZeroMemClass.coe_zero, map_zero]
  by_cases hx : x ∈ CompactSupport.support (CompactSections.ordinary F.obj) a.val
  · have hqx : q x ∉ (K.obj : Set Y) := fun h => hKS h ⟨x, hx, rfl⟩
    change (K.obj : Set Y).indicator (fun _ => (1 : ℂ)) (q x) • _ = _
    rw [Set.indicator_of_notMem hqx, zero_smul]
  · change ¬ ((CompactSections.ordinary F.obj).Γgerm x a.val ≠ 0) at hx
    rw [not_not.mp hx, smul_zero]

/-! ### The fibre side -/

include hY in
/-- The literal fibre inclusion is a closed embedding, since the target is Hausdorff. -/
theorem inclusion_isClosedEmbedding :
    _root_.Topology.IsClosedEmbedding (InvariantFibres.inclusion q y) := by
  let := hY.t2Space
  exact (InvariantFibres.fibre_closed q y).isClosedEmbedding_subtypeVal

/-- The compact-section representation of the actual fibre restriction of `F`. -/
abbrev fibreRep (F : ActionSheaf G X) :=
  letI := InvariantFibres.fibreAction q hq y
  letI := InvariantFibres.fibreContinuousSMul q hq y
  CompactSections.representation ((InvariantFibres.restriction q hq y).obj F).obj

/-- Restriction of compact sections of `F` to the fibre over `y`. -/
abbrev rFib (F : ActionSheaf G X) :
    letI := InvariantFibres.fibreAction q hq y
    Sections F →ₗ[ℂ]
      CompactSupport.submodule (CompactSections.ordinary ((InvariantFibres.restriction q hq y).obj F).obj) :=
  letI := InvariantFibres.fibreAction q hq y
  letI := InvariantFibres.fibreContinuousSMul q hq y
  FibreCoinvariantRestriction.compactRestrict (InvariantFibres.inclusion q y) (fun _ _ => rfl)
    (inclusion_isClosedEmbedding q hY y) F

/-- `β`: compact section ↦ coinvariant class of its fibre restriction. -/
def beta (F : ActionSheaf G X) : Sections F →ₗ[ℂ] (InvariantFibres.coinvariants q hq y).obj F :=
  letI := InvariantFibres.fibreAction q hq y
  (Representation.Coinvariants.mk (fibreRep q hq y F)).comp (rFib q hq hY y F)

theorem beta_apply (F : ActionSheaf G X) (a : Sections F) :
    beta q hq hY y F a = Representation.Coinvariants.mk (fibreRep q hq y F) (rFib q hq hY y F a) :=
  rfl

theorem rFib_action (F : ActionSheaf G X) (g : G) (m : (testAction hX F).module.obj) :
    rFib q hq hY y F ((sectionsEquiv hX F).symm ((testAction hX F).action g m)) =
      fibreRep q hq y F g (rFib q hq hY y F ((sectionsEquiv hX F).symm m)) := by
  let := InvariantFibres.fibreAction q hq y
  let := InvariantFibres.fibreContinuousSMul q hq y
  exact FibreCoinvariantRestriction.compactRestrict_action (InvariantFibres.inclusion q y)
    (fun _ _ => rfl) (inclusion_isClosedEmbedding q hY y) F g ((sectionsEquiv hX F).symm m)

/-- Restriction sends the coinvariant kernel into the fibre coinvariant kernel. -/
theorem rFib_mem_ker (F : ActionSheaf G X) {m : (testAction hX F).module.obj}
    (hm : m ∈ Representation.Coinvariants.ker (testAction hX F).action) :
    rFib q hq hY y F ((sectionsEquiv hX F).symm m) ∈
      Representation.Coinvariants.ker (fibreRep q hq y F) := by
  let := InvariantFibres.fibreAction q hq y
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, m⟩, rfl⟩ := hx
    rw [map_sub, map_sub, rFib_action]
    exact Representation.Coinvariants.sub_mem_ker (ρ := fibreRep q hq y F) g _
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [map_add, map_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hx

/-- Every element of the fibre coinvariant kernel is the restriction of a kernel element. -/
theorem exists_ker_preimage (F : ActionSheaf G X) {b}
    (hb : b ∈ Representation.Coinvariants.ker (fibreRep q hq y F)) :
    ∃ k : Sections F, sectionsEquiv hX F k ∈ Representation.Coinvariants.ker
      (testAction hX F).action ∧ rFib q hq hY y F k = b := by
  let := InvariantFibres.fibreAction q hq y
  let := InvariantFibres.fibreContinuousSMul q hq y
  have hsurj := FibreCoinvariantRestriction.compactRestrict_surjective
    (InvariantFibres.inclusion q y) (fun _ _ => rfl) F (inclusion_isClosedEmbedding q hY y) hX
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, b'⟩, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := hsurj b'
    refine ⟨(sectionsEquiv hX F).symm ((testAction hX F).action g (sectionsEquiv hX F m) -
      sectionsEquiv hX F m), ?_, ?_⟩
    · rw [LinearEquiv.apply_symm_apply]
      exact Representation.Coinvariants.sub_mem_ker (ρ := (testAction hX F).action) g _
    · rw [map_sub, map_sub, rFib_action, LinearEquiv.symm_apply_apply]
      rfl
  | zero => exact ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, map_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨k', hk', rfl⟩ := hz
    exact ⟨k + k', by rw [map_add]; exact Submodule.add_mem _ hk hk', map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨c • k, by rw [map_smul]; exact Submodule.smul_mem _ c hk, map_smul _ _ _⟩

/-- Over the fibre, a neighbourhood test of `y` acts trivially. -/
theorem rFib_multiplier (F : ActionSheaf G X) (K : CompactOpen hY) (hyK : y ∈ K.obj)
    (a : Sections F) :
    rFib q hq hY y F ((sectionsEquiv hX F).symm
        (CoinvariantTestModule.multiplier q (testAction hX F) (test hY K) (sectionsEquiv hX F a))) =
      rFib q hq hY y F a := by
  let := InvariantFibres.fibreAction q hq y
  let := InvariantFibres.fibreContinuousSMul q hq y
  apply Subtype.ext
  apply TopCat.Presheaf.section_ext (underlying ((InvariantFibres.restriction q hq y).obj F)) ⊤
  intro z _
  change (CompactSections.ordinary (FibreCoinvariantRestriction.res
        (InvariantFibres.inclusion q y) (fun _ _ => rfl) F).obj).Γgerm z
      ((FibreCoinvariantRestriction.globalRestrict (InvariantFibres.inclusion q y)
        (fun _ _ => rfl) F).hom ((sectionsEquiv hX F).symm
          (CoinvariantTestModule.multiplier q (testAction hX F) (test hY K)
            (sectionsEquiv hX F a))).val) =
    (CompactSections.ordinary (FibreCoinvariantRestriction.res
        (InvariantFibres.inclusion q y) (fun _ _ => rfl) F).obj).Γgerm z
      ((FibreCoinvariantRestriction.globalRestrict (InvariantFibres.inclusion q y)
        (fun _ _ => rfl) F).hom a.val)
  rw [FibreCoinvariantRestriction.germ_globalRestrict,
    FibreCoinvariantRestriction.germ_globalRestrict, germ_multiplier]
  have hz : q ((InvariantFibres.inclusion q y) z) ∈ (K.obj : Set Y) := by
    change q z.val ∈ (K.obj : Set Y)
    rw [z.property]
    exact hyK
  change (InverseImageStalks.stalkIso _ _ F z).hom
      ((K.obj : Set Y).indicator (fun _ => (1 : ℂ)) (q ((InvariantFibres.inclusion q y) z)) • _) = _
  rw [Set.indicator_of_mem hz, one_smul]

/-! ### Comparison of kernels and the natural isomorphism -/

/-- `α` and `β` have the same kernel. -/
theorem ker_alpha_eq_ker_beta (F : ActionSheaf G X) :
    LinearMap.ker (alpha hX q hq hY y F) = LinearMap.ker (beta q hq hY y F) := by
  let := InvariantFibres.fibreAction q hq y
  let := InvariantFibres.fibreContinuousSMul q hq y
  ext a
  rw [LinearMap.mem_ker, LinearMap.mem_ker, alpha_eq_zero_iff]
  change _ ↔ Representation.Coinvariants.mk (fibreRep q hq y F) (rFib q hq hY y F a) = 0
  rw [Representation.Coinvariants.mk_eq_zero]
  constructor
  · rintro ⟨K, hyK, hK⟩
    rw [← rFib_multiplier hX q hq hY y F K hyK a]
    exact rFib_mem_ker hX q hq hY y F hK
  · intro hb
    obtain ⟨k, hk, hkb⟩ := exists_ker_preimage hX q hq hY y F hb
    have hd : ∀ x : X, q x = y →
        (CompactSections.ordinary F.obj).Γgerm x (a - k).val = 0 := by
      intro x hx
      have h0 : rFib q hq hY y F (a - k) = 0 := by rw [map_sub, hkb, sub_self]
      have h1 : (CompactSections.ordinary (FibreCoinvariantRestriction.res
          (InvariantFibres.inclusion q y) (fun _ _ => rfl) F).obj).Γgerm ⟨x, hx⟩
          ((FibreCoinvariantRestriction.globalRestrict (InvariantFibres.inclusion q y)
            (fun _ _ => rfl) F).hom (a - k).val) = 0 := by
        change (CompactSections.ordinary (FibreCoinvariantRestriction.res
          (InvariantFibres.inclusion q y) (fun _ _ => rfl) F).obj).Γgerm ⟨x, hx⟩
          (rFib q hq hY y F (a - k)).val = 0
        rw [h0, ZeroMemClass.coe_zero, map_zero]
      rw [FibreCoinvariantRestriction.germ_globalRestrict] at h1
      have h2 := congrArg (InverseImageStalks.stalkIso (InvariantFibres.inclusion q y)
        (fun _ _ => rfl) F ⟨x, hx⟩).inv.hom h1
      rw [Iso.hom_inv_id_apply, map_zero] at h2
      exact h2
    obtain ⟨K, hyK, hK⟩ := exists_multiplier_eq_zero hX q hY y F (a - k) hd
    refine ⟨K, hyK, ?_⟩
    rw [map_sub, map_sub, sub_eq_zero] at hK
    rw [hK]
    exact CoinvariantTestModule.multiplier_preserves_ker q hq (testAction hX F) (test hY K) hk

theorem alpha_surjective (F : ActionSheaf G X) :
    Function.Surjective (alpha hX q hq hY y F) := by
  intro t
  obtain ⟨m, rfl⟩ :=
    FibreCoinvariantStalk.stalkGerm_surjective hY (coinvariantModule hX q hq hY F).property y t
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective (testAction hX F).action m
  exact ⟨(sectionsEquiv hX F).symm a, rfl⟩

include hX in
theorem beta_surjective (F : ActionSheaf G X) :
    Function.Surjective (beta q hq hY y F) := by
  let := InvariantFibres.fibreAction q hq y
  let := InvariantFibres.fibreContinuousSMul q hq y
  intro t
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective (fibreRep q hq y F) t
  obtain ⟨a, rfl⟩ := FibreCoinvariantRestriction.compactRestrict_surjective
    (InvariantFibres.inclusion q y) (fun _ _ => rfl) F (inclusion_isClosedEmbedding q hY y) hX b
  exact ⟨a, rfl⟩

/-- The comparison at `F`: the unique linear map sending `α a` to `β a`. -/
def component (F : ActionSheaf G X) :
    stalkY hX q hq hY y F ≃ₗ[ℂ] (InvariantFibres.coinvariants q hq y).obj F :=
  ((alpha hX q hq hY y F).quotKerEquivOfSurjective (alpha_surjective hX q hq hY y F)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_alpha_eq_ker_beta hX q hq hY y F)).trans
      ((beta q hq hY y F).quotKerEquivOfSurjective (beta_surjective hX q hq hY y F)))

theorem component_alpha (F : ActionSheaf G X) (a : Sections F) :
    component hX q hq hY y F (alpha hX q hq hY y F a) = beta q hq hY y F a := by
  rw [component, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The fibre side is natural on images of `β`. -/
theorem beta_map {F F' : ActionSheaf G X} (φ : F ⟶ F') (a : Sections F) :
    ((InvariantFibres.coinvariants q hq y).map φ).hom (beta q hq hY y F a) =
      beta q hq hY y F' (CompactSections.map φ a) := by
  let := InvariantFibres.fibreAction q hq y
  let := InvariantFibres.fibreContinuousSMul q hq y
  change Representation.Coinvariants.mk (fibreRep q hq y F')
      (CompactSections.map ((InvariantFibres.restriction q hq y).map φ) (rFib q hq hY y F a)) =
    Representation.Coinvariants.mk (fibreRep q hq y F') (rFib q hq hY y F' (CompactSections.map φ a))
  exact congrArg (Representation.Coinvariants.mk (fibreRep q hq y F'))
    (FibreCoinvariantRestriction.compactRestrict_naturality (InvariantFibres.inclusion q y)
      (fun _ _ => rfl) (inclusion_isClosedEmbedding q hY y) φ a).symm

/-- The stalk side is natural on images of `α`. -/
theorem alpha_map {F F' : ActionSheaf G X} (φ : F ⟶ F') (a : Sections F) :
    ((CoinvariantSheaf.functor hX q hq hY ⋙ TopCat.Sheaf.forget (ModuleCat.{0} ℂ) (TopCat.of Y) ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) y).map φ).hom (alpha hX q hq hY y F a) =
      alpha hX q hq hY y F' (CompactSections.map φ a) := by
  rw [alpha_apply, alpha_apply, FibreCoinvariantStalk.stalkGerm_apply,
    FibreCoinvariantStalk.stalkGerm_apply]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [ProjectorVectorSheaf.sheafMap_originalSection]
  rfl

/-- The natural isomorphism of Renard III.3.1. -/
def natIso :
    (CoinvariantSheaf.functor hX q hq hY ⋙
        TopCat.Sheaf.forget (ModuleCat.{0} ℂ) (TopCat.of Y) ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) y) ≅
      InvariantFibres.coinvariants q hq y :=
  NatIso.ofComponents (fun F => (component hX q hq hY y F).toModuleIso) (fun {F F'} φ => by
    ext t
    obtain ⟨a, rfl⟩ := alpha_surjective hX q hq hY y F t
    change component hX q hq hY y F' (((CoinvariantSheaf.functor hX q hq hY ⋙
        TopCat.Sheaf.forget (ModuleCat.{0} ℂ) (TopCat.of Y) ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) y).map φ).hom (alpha hX q hq hY y F a)) =
      ((InvariantFibres.coinvariants q hq y).map φ).hom
        (component hX q hq hY y F (alpha hX q hq hY y F a))
    rw [alpha_map, component_alpha, component_alpha, beta_map])

end Langlands.Sheaf.Renard.FibreCoinvariantProof

namespace Langlands.Sheaf.Renard.CoinvariantStatements

/-- Renard III.3.1 Proposition: the stalk of the coinvariant sheaf at `y` is naturally the
coinvariants of the compactly supported sections of the fibre restriction. -/
theorem fibreCoinvariantStatement : FibreCoinvariantStatement := by
  intro G _ _ _ _ X Y _ _ _ _ hX q hq hY y
  exact ⟨FibreCoinvariantProof.natIso hX q hq hY y⟩

end Langlands.Sheaf.Renard.CoinvariantStatements
