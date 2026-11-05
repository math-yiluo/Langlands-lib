import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.FiniteVectors
import Langlands.Representation.ScalarSubReduction

/-! # Square-integrable representations are unitary and semisimple (Waldspurger, Lemma III.1.3)

Waldspurger, Lemma III.1.3 (printed p. 264): every admissible square-integrable representation
`(π, V)` is unitary and semisimple. For a finitely generated subrepresentation `V'`, the form
`(v̌₁, v̌₂) ↦ Σᵢ ∫_{A_G\G} conj⟨π(g) vᵢ, v̌₁⟩ ⟨π(g) vᵢ, v̌₂⟩ dg` on `V̌'` is positive definite and
invariant, so `V̌'` and then `V'` are unitary; admissible unitary representations are semisimple;
`V` is the union of such `V'`, hence semisimple; its irreducible subrepresentations are unitary,
hence so is `V`.

This module proves the lemma for a representation square integrable modulo a normal central
subgroup `A`, with a Haar measure on `G ⧸ A` invariant under inversion and cofinal compact open
subgroups. It uses cyclic subrepresentations (one generator) in place of finitely generated
ones; square integrability passes to subrepresentations and to smooth contragredients; the
invariant form on the contragredient of a cyclic subrepresentation is the published
`invariantForm` with the evaluation at the generator.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe u v w

section Transfer

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {W : Type w} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- A unitary central character transfers along an injective intertwiner. -/
def unitaryCentralCharacterComap (c : UnitaryCentralCharacter ρ)
    (f : σ.IntertwiningMap ρ) (hf : Function.Injective f) : UnitaryCentralCharacter σ where
  character := c.character
  isOpen_ker := c.isOpen_ker
  norm_eq_one := c.norm_eq_one
  acts z x := by
    apply hf
    rw [f.isIntertwining, c.acts, map_smul]

omit [BorelSpace (G ⧸ A)] in
/-- **Square integrability passes to subrepresentations**: along an injective intertwiner
`σ → ρ`, square integrability of `ρ` modulo `A` gives that of `σ`. -/
theorem IsSquareIntegrableModCentralSubgroup.of_injective
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (f : σ.IntertwiningMap ρ) (hf : Function.Injective f)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) :
    IsSquareIntegrableModCentralSubgroup A hA σ μ := by
  obtain ⟨hadm, c, hc⟩ := hρ
  have hσ : IsAdmissible σ := isAdmissible_of_injective f hf hadm
  refine ⟨hσ, unitaryCentralCharacterComap c f hf, fun ℓ x => ?_⟩
  obtain ⟨ℓ', hℓ'⟩ :=
    contragredientMap_surjective_of_injective_of_compact_cofinal hcof hσ.1 hadm.1 f hf ℓ
  have heq : centralSubgroupCoefficientNorm A hA (unitaryCentralCharacterComap c f hf) ℓ.val x =
      centralSubgroupCoefficientNorm A hA c ℓ'.val (f x) := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [centralSubgroupCoefficientNorm_mk, centralSubgroupCoefficientNorm_mk, ← hℓ']
    change ‖ℓ'.val (f (σ g x))‖ = ‖ℓ'.val (ρ g (f x))‖
    rw [f.isIntertwining]
  rw [heq]
  exact hc ℓ' (f x)

/-- The unitary central character `c⁻¹` of the smooth contragredient. -/
def unitaryCentralCharacterDual (c : UnitaryCentralCharacter ρ) :
    UnitaryCentralCharacter (smoothContragredient ρ) where
  character := c.character⁻¹
  isOpen_ker := by
    have hker : (c.character⁻¹).ker = c.character.ker := by
      ext z
      simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
    rw [hker]
    exact c.isOpen_ker
  norm_eq_one z := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, c.norm_eq_one, inv_one]
  acts z ℓ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change ℓ.val (ρ ((z : G)⁻¹) x) = ((c.character⁻¹ z : ℂˣ) : ℂ) * ℓ.val x
    have hz : ((z : G)⁻¹) = ((z⁻¹ : Subgroup.center G) : G) := rfl
    rw [hz, c.acts, map_smul, smul_eq_mul, MonoidHom.inv_apply, map_inv]

/-- **The smooth contragredient of a square-integrable representation is square integrable**,
for a Haar measure on `G ⧸ A` invariant under inversion: its coefficients are those of `ρ`
composed with `g ↦ g⁻¹` (by reflexivity of admissible representations). -/
theorem IsSquareIntegrableModCentralSubgroup.smoothContragredient [μ.IsInvInvariant]
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) :
    IsSquareIntegrableModCentralSubgroup A hA (smoothContragredient ρ) μ := by
  obtain ⟨hadm, c, hc⟩ := hρ
  refine ⟨isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hadm,
    unitaryCentralCharacterDual c, fun ℓ' ℓ => ?_⟩
  obtain ⟨x, hx⟩ := smoothBidual_surjective_of_compact_cofinal hcof ρ hadm ℓ'
  have heq : centralSubgroupCoefficientNorm A hA (unitaryCentralCharacterDual c) ℓ'.val ℓ =
      centralSubgroupCoefficientNorm A hA c ℓ.val x ∘ fun q => q⁻¹ := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Function.comp_apply, centralSubgroupCoefficientNorm_mk, ← QuotientGroup.mk_inv,
      centralSubgroupCoefficientNorm_mk, ← hx]
    rfl
  rw [heq]
  exact (hc ℓ x).comp_measurePreserving (Measure.measurePreserving_inv μ)

end Transfer

section DualForm

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- **The contragredient of a unitarizable admissible representation is unitarizable**: the
form `⟪ℓ₁, ℓ₂⟫ = b(E⁻¹ ℓ₂, E⁻¹ ℓ₁)`, where `E : v ↦ b(v, -)` is the Hermitian identification
`InvariantPositiveForm.smoothDualEquiv`. -/
def dualInvariantForm (b : InvariantPositiveForm ρ)
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) : InvariantPositiveForm (smoothContragredient ρ) where
  inner ℓ₁ ℓ₂ := b.inner ((b.smoothDualEquiv hcof hρ).symm ℓ₂)
    ((b.smoothDualEquiv hcof hρ).symm ℓ₁)
  conj_inner_symm ℓ₁ ℓ₂ := b.conj_inner_symm _ _
  re_inner_nonneg ℓ := b.re_inner_nonneg _
  add_left ℓ₁ ℓ₂ ℓ₃ := by
    change b.rightFunctional _ _ = b.rightFunctional _ _ + b.rightFunctional _ _
    rw [map_add, map_add]
  smul_left ℓ₁ ℓ₂ r := by
    change b.rightFunctional _ _ = conj r * b.rightFunctional _ _
    rw [LinearEquiv.map_smulₛₗ, map_smul, smul_eq_mul]
  definite ℓ hℓ := by
    have h0 := b.definite _ hℓ
    exact (b.smoothDualEquiv hcof hρ).symm.map_eq_zero_iff.mp h0
  invariant g ℓ₁ ℓ₂ := by
    have hE : ∀ ℓ : SmoothDual ρ, (b.smoothDualEquiv hcof hρ).symm (smoothContragredient ρ g ℓ) =
        ρ g ((b.smoothDualEquiv hcof hρ).symm ℓ) := by
      intro ℓ
      apply (b.smoothDualEquiv hcof hρ).injective
      rw [LinearEquiv.apply_symm_apply, InvariantPositiveForm.smoothDualEquiv_apply,
        b.toSmoothDual_apply_action, ← InvariantPositiveForm.smoothDualEquiv_apply b hcof hρ,
        LinearEquiv.apply_symm_apply]
    change b.inner _ _ = b.inner _ _
    rw [hE, hE, b.invariant]

theorem isUnitarizable_smoothContragredient_of_admissible
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (hu : IsUnitarizable ρ) :
    IsUnitarizable (smoothContragredient ρ) :=
  let ⟨b⟩ := hu
  ⟨dualInvariantForm b hcof hρ⟩

end DualForm

section Orbit

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- A linear functional on the orbit subrepresentation that vanishes on the orbit of the
generator vanishes. -/
theorem eq_zero_of_forall_orbit (ρ : Representation ℂ G V) (x : V)
    (ℓ : Module.Dual ℂ (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule)
    (hℓ : ∀ g : G, ℓ ((FiniteVectors.orbitSubrepresentation ρ x).toRepresentation g
      ⟨x, FiniteVectors.self_mem_orbitSpan ρ x⟩) = 0) : ℓ = 0 := by
  apply LinearMap.ext
  rintro ⟨y, hy⟩
  rw [LinearMap.zero_apply]
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨g, rfl⟩ := hz
      exact hℓ g
  | zero => exact map_zero ℓ
  | add a b ha hb iha ihb =>
      have : (⟨a + b, Submodule.add_mem _ ha hb⟩ :
          (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this, map_add, iha, ihb, add_zero]
  | smul c a ha iha =>
      have : (⟨c • a, Submodule.smul_mem _ c ha⟩ :
          (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule) = c • ⟨a, ha⟩ := rfl
      rw [this, map_smul, iha, smul_zero]

/-- The algebra action on a subrepresentation is the restriction of the ambient one. -/
theorem subrepresentation_asAlgebraHom_apply {ρ : Representation ℂ G V} (S : Subrepresentation ρ)
    (r : MonoidAlgebra ℂ G) (y : S.toSubmodule) :
    (S.toRepresentation.asAlgebraHom r y : V) = ρ.asAlgebraHom r (y : V) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r₁ r₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single g a => simp [Representation.asAlgebraHom_single]; rfl

/-- The `ℂ[G]`-module of a subrepresentation is the corresponding submodule of
`ρ.asModule`. -/
def subrepresentationAsModuleEquiv {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ G] Subrepresentation.asSubmodule S where
  toFun y := ⟨ρ.asModuleEquiv.symm (S.toRepresentation.asModuleEquiv y : V),
    (S.toRepresentation.asModuleEquiv y).2⟩
  invFun y := S.toRepresentation.asModuleEquiv.symm ⟨ρ.asModuleEquiv y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r y := by
    apply Subtype.ext
    exact subrepresentation_asAlgebraHom_apply S r y

end Orbit

section Semisimple

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- **Unitarity of cyclic subrepresentations** (proof of Lemma III.1.3): for `ρ` square
integrable modulo `A`, the subrepresentation `V'` spanned by the orbit of one vector `x` is
unitarizable. The form `⟪ℓ₁, ℓ₂⟫ = ∫_{G/A} conj(ℓ₁(π(g⁻¹) x)) ℓ₂(π(g⁻¹) x) dg` (Waldspurger's form
for the single generator `x`, after `g ↦ g⁻¹`) is positive definite on the smooth dual of `V'`, so
that dual is unitarizable; hence so is its smooth dual, which contains `V'`. -/
theorem isUnitarizable_orbitSubrepresentation
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (x : V) :
    IsUnitarizable (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation := by
  set S := FiniteVectors.orbitSubrepresentation ρ x
  set σ := S.toRepresentation
  have hσ : IsSquareIntegrableModCentralSubgroup A hA σ μ :=
    IsSquareIntegrableModCentralSubgroup.of_injective A hA μ hcof (ScalarSubReduction.inclusion ρ S)
      (ScalarSubReduction.inclusion_injective ρ S) hρ
  have hX := IsSquareIntegrableModCentralSubgroup.smoothContragredient A hA μ hcof hσ
  obtain ⟨hXadm, c, -⟩ := id hX
  let χ : A →* ℂˣ := c.character.comp (Subgroup.inclusion hA)
  have h : ∀ (a : A) (l : SmoothDual σ), smoothContragredient σ a l = (χ a : ℂ) • l :=
    fun a l => c.acts ⟨a, hA a.2⟩ l
  have hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1 := fun a => c.norm_eq_one _
  let x₀ : S.toSubmodule := ⟨x, FiniteVectors.self_mem_orbitSpan ρ x⟩
  let ℓ : SmoothDual (smoothContragredient σ) := smoothBidual hσ.1.1 x₀
  have hdef : ∀ l : SmoothDual σ, invariantForm A μ h hu ℓ l l = 0 → l = 0 := by
    intro l hl
    by_contra hne
    obtain ⟨g, hg⟩ : ∃ g : G, l.val (σ g x₀) ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hne (Subtype.ext (eq_zero_of_forall_orbit ρ x l.val hall))
    have hv : ℓ.val (smoothContragredient σ g⁻¹ l) ≠ 0 := by
      change l.val (σ (g⁻¹)⁻¹ x₀) ≠ 0
      rwa [inv_inv]
    have hpos : 0 < (invariantForm A μ h hu ℓ l l).re := by
      rw [← invariantForm_rho A μ h hu ℓ g⁻¹ l l, invariantForm_self, Complex.ofReal_re]
      exact invariantForm_self_re_pos A hA μ h hu hX ℓ hv
    rw [hl, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  have hXu : IsUnitarizable (smoothContragredient σ) :=
    ⟨{ inner := fun l₁ l₂ => invariantForm A μ h hu ℓ l₂ l₁
       conj_inner_symm := fun l₁ l₂ => (invariantForm_swap A μ h hu ℓ l₁ l₂).symm
       re_inner_nonneg := fun l => by
         show 0 ≤ (invariantForm A μ h hu ℓ l l).re
         rw [invariantForm_self, Complex.ofReal_re]
         exact integral_nonneg fun q => (formIntegrand_self A h hu ℓ.val l q).2
       add_left := fun l₁ l₂ l₃ => by
         show invariantForm A μ h hu ℓ l₃ (l₁ + l₂) =
           invariantForm A μ h hu ℓ l₃ l₁ + invariantForm A μ h hu ℓ l₃ l₂
         rw [invariantForm_swap A μ h hu ℓ (l₁ + l₂) l₃,
           invariantForm_add_left A hA μ h hu hX ℓ l₁ l₂ l₃, map_add, ← invariantForm_swap,
           ← invariantForm_swap]
       smul_left := fun l₁ l₂ r => by
         show invariantForm A μ h hu ℓ l₂ (r • l₁) = conj r * invariantForm A μ h hu ℓ l₂ l₁
         rw [invariantForm_swap A μ h hu ℓ (r • l₁) l₂, invariantForm_smul_left, map_mul,
           ← invariantForm_swap]
       definite := fun l hl => hdef l hl
       invariant := fun g l₁ l₂ => invariantForm_rho A μ h hu ℓ g l₂ l₁ }⟩
  exact (isUnitarizable_smoothContragredient_of_admissible hcof hXadm hXu).of_injective (smoothBidual hσ.1.1)
    (smoothBidual_injective_of_compact_cofinal hcof σ hσ.1.1)

/-- **Semisimplicity** (Waldspurger, Lemma III.1.3): a representation that is square integrable
modulo `A` is semisimple. Every cyclic subrepresentation is admissible and unitarizable, hence
semisimple (`admissibleUnitarySemisimplicity`), and the cyclic subrepresentations span. -/
theorem isSemisimpleRepresentation_of_isSquareIntegrable
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) : ρ.IsSemisimpleRepresentation := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun x : V => Subrepresentation.asSubmodule (FiniteVectors.orbitSubrepresentation ρ x))
    (fun x => ?_) ?_
  · have hadm : IsAdmissible (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation :=
      isAdmissible_of_injective (ScalarSubReduction.inclusion ρ _)
        (ScalarSubReduction.inclusion_injective ρ _) hρ.1
    have hS := admissibleUnitarySemisimplicity G hcof _
      (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation hadm
      (isUnitarizable_orbitSubrepresentation A hA μ hcof hρ x)
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hS
    exact (subrepresentationAsModuleEquiv (FiniteVectors.orbitSubrepresentation ρ x)).isSemisimpleModule_iff.mp
      hS
  · rw [eq_top_iff]
    intro y _
    exact Submodule.mem_iSup_of_mem y (FiniteVectors.self_mem_orbitSpan ρ y)

end Semisimple

section DirectSumForm

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {ι : Type*}

/-- **Gluing invariant forms along an internal direct sum of subrepresentations**: if `ρ` is the
internal direct sum of `ℂ[G]`-submodules `p i` of `ρ.asModule` and each piece carries an
invariant positive form, the sum of these forms over the components is an invariant positive
form on `ρ`. -/
theorem isUnitarizable_of_isInternal [DecidableEq ι]
    (p : ι → Submodule (MonoidAlgebra ℂ G) ρ.asModule) (hint : DirectSum.IsInternal p)
    (b : ∀ i, InvariantPositiveForm (Subrepresentation.ofSubmodule' (p i)).toRepresentation) :
    IsUnitarizable ρ := by
  classical
  let dec : ρ.asModule ≃ₗ[MonoidAlgebra ℂ G] DirectSum ι fun i => p i :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap p) hint).symm
  let comp : ∀ i, V → (Subrepresentation.ofSubmodule' (p i)).toSubmodule := fun i x =>
    ⟨((dec (ρ.asModuleEquiv.symm x)) i : ρ.asModule), ((dec (ρ.asModuleEquiv.symm x)) i).2⟩
  have comp_add : ∀ i x y, comp i (x + y) = comp i x + comp i y := by
    intro i x y
    apply Subtype.ext
    change (((dec (ρ.asModuleEquiv.symm (x + y))) i : ρ.asModule) : V) =
      ((dec (ρ.asModuleEquiv.symm x)) i : ρ.asModule) + ((dec (ρ.asModuleEquiv.symm y)) i : ρ.asModule)
    rw [map_add, map_add, DirectSum.add_apply, Submodule.coe_add]
  have hsm : ∀ (c : ℂ) (w : V), ρ.asModuleEquiv.symm (c • w) =
      algebraMap ℂ (MonoidAlgebra ℂ G) c • ρ.asModuleEquiv.symm w :=
    fun c w => ρ.asModuleEquiv_symm_map_smul c w
  have comp_smul : ∀ i (c : ℂ) x, comp i (c • x) = c • comp i x := by
    intro i c x
    apply Subtype.ext
    change (((dec (ρ.asModuleEquiv.symm (c • x))) i : ρ.asModule) : V) =
      c • (((dec (ρ.asModuleEquiv.symm x)) i : ρ.asModule) : V)
    rw [hsm, map_smul, DirectSum.smul_apply, Submodule.coe_smul]
    exact (hsm c _).symm
  have comp_rho : ∀ i (g : G) x,
      comp i (ρ g x) = (Subrepresentation.ofSubmodule' (p i)).toRepresentation g (comp i x) := by
    intro i g x
    apply Subtype.ext
    change (((dec (ρ.asModuleEquiv.symm (ρ g x))) i : ρ.asModule) : V) =
      ρ g (((dec (ρ.asModuleEquiv.symm x)) i : ρ.asModule) : V)
    rw [ρ.asModuleEquiv_symm_map_rho, map_smul, DirectSum.smul_apply, Submodule.coe_smul]
    exact ρ.asModuleEquiv_map_smul (MonoidAlgebra.of ℂ G g) _ |>.trans
      (by rw [Representation.asAlgebraHom_of]; rfl)
  have mem_support : ∀ i x, comp i x ≠ 0 → i ∈ (dec (ρ.asModuleEquiv.symm x)).support := by
    intro i x hx
    rw [DFinsupp.mem_support_iff]
    intro h0
    apply hx
    apply Subtype.ext
    change (((dec (ρ.asModuleEquiv.symm x)) i : ρ.asModule) : V) = 0
    rw [h0]
    rfl
  have eq_zero_of_comp : ∀ x, (∀ i, comp i x = 0) → x = 0 := by
    intro x hx
    have hd : dec (ρ.asModuleEquiv.symm x) = 0 := by
      ext i
      have := congrArg Subtype.val (hx i)
      exact this
    have := congrArg dec.symm hd
    rw [LinearEquiv.symm_apply_apply, map_zero] at this
    exact this
  have inner_zero_left : ∀ i (z : (Subrepresentation.ofSubmodule' (p i)).toSubmodule),
      (b i).inner 0 z = 0 := by
    intro i z
    rw [← (b i).conj_inner_symm]
    change conj ((b i).rightFunctional z 0) = 0
    rw [map_zero, map_zero]
  let F : V → V → ι → ℂ := fun x y i => (b i).inner (comp i x) (comp i y)
  have hsum : ∀ (x y : V) (T : Finset ι), (dec (ρ.asModuleEquiv.symm x)).support ⊆ T →
      ∑ᶠ i, F x y i = ∑ i ∈ T, F x y i := by
    intro x y T hT
    refine finsum_eq_sum_of_support_subset _ fun i hi => hT (mem_support i x ?_)
    intro h0
    apply hi
    change (b i).inner (comp i x) (comp i y) = 0
    rw [h0, inner_zero_left]
  let supp : V → Finset ι := fun x => (dec (ρ.asModuleEquiv.symm x)).support
  refine ⟨{ inner := (fun x y => ∑ᶠ i, F x y i)
            conj_inner_symm := ?_
            re_inner_nonneg := ?_
            add_left := ?_
            smul_left := ?_
            definite := ?_
            invariant := ?_ }⟩
  · intro x y
    change conj (∑ᶠ i, F y x i) = ∑ᶠ i, F x y i
    rw [hsum y x (supp x ∪ supp y) Finset.subset_union_right,
      hsum x y (supp x ∪ supp y) Finset.subset_union_left, map_sum]
    refine Finset.sum_congr rfl fun i _ => (b i).conj_inner_symm _ _
  · intro x
    change 0 ≤ (∑ᶠ i, F x x i).re
    rw [hsum x x (supp x) subset_rfl, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => (b i).re_inner_nonneg _
  · intro x x' y
    change ∑ᶠ i, F (x + x') y i = ∑ᶠ i, F x y i + ∑ᶠ i, F x' y i
    rw [hsum (x + x') y (supp (x + x') ∪ (supp x ∪ supp x')) Finset.subset_union_left,
      hsum x y (supp (x + x') ∪ (supp x ∪ supp x'))
        (Finset.subset_union_left.trans Finset.subset_union_right),
      hsum x' y (supp (x + x') ∪ (supp x ∪ supp x'))
        (Finset.subset_union_right.trans Finset.subset_union_right),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (b i).inner (comp i (x + x')) (comp i y) = _
    rw [comp_add]
    exact (b i).add_left _ _ _
  · intro x y c
    change ∑ᶠ i, F (c • x) y i = conj c * ∑ᶠ i, F x y i
    rw [hsum (c • x) y (supp (c • x) ∪ supp x) Finset.subset_union_left,
      hsum x y (supp (c • x) ∪ supp x) Finset.subset_union_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (b i).inner (comp i (c • x)) (comp i y) = _
    rw [comp_smul]
    exact (b i).smul_left _ _ _
  · intro x hx
    change ∑ᶠ i, F x x i = 0 at hx
    rw [hsum x x (supp x) subset_rfl] at hx
    have hre : ∑ i ∈ supp x, (F x x i).re = 0 := by
      rw [← Complex.re_sum, hx, Complex.zero_re]
    have hnn : ∀ i ∈ supp x, 0 ≤ (F x x i).re := fun i _ => (b i).re_inner_nonneg _
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hre
    apply eq_zero_of_comp
    intro i
    by_cases hi : i ∈ supp x
    · have h1 : (F x x i).re = 0 := hre i hi
      have h2 : (F x x i).im = 0 := by
        have := (b i).conj_inner_symm (comp i x) (comp i x)
        exact Complex.conj_eq_iff_im.mp this
      exact (b i).definite _ (Complex.ext h1 h2)
    · by_contra hne
      exact hi (mem_support i x hne)
  · intro g x y
    refine finsum_congr fun i => ?_
    change (b i).inner (comp i (ρ g x)) (comp i (ρ g y)) = (b i).inner (comp i x) (comp i y)
    rw [comp_rho, comp_rho, (b i).invariant]

end DirectSumForm

section Unitary

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- **Unitarity** (Waldspurger, Lemma III.1.3): a representation that is square integrable
modulo `A` is unitarizable. It is a direct sum of irreducible subrepresentations
(`isSemisimpleRepresentation_of_isSquareIntegrable`), each square integrable and hence
unitarizable (`isUnitarizable_of_isSquareIntegrable`), and the invariant forms of the pieces add
up (`isUnitarizable_of_isInternal`). -/
theorem isUnitarizable_of_isSquareIntegrableModCentralSubgroup
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) : IsUnitarizable ρ := by
  classical
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      (isSemisimpleRepresentation_of_isSquareIntegrable A hA μ hcof hρ)
  obtain ⟨s, hind, htop, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (R := MonoidAlgebra ℂ G)
      (M := ρ.asModule)
  let p : s → Submodule (MonoidAlgebra ℂ G) ρ.asModule := fun m => m.1
  have hint : DirectSum.IsInternal p :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ((sSupIndep_iff s).mp hind)
      (by rw [← sSup_eq_iSup']; exact htop)
  obtain ⟨-, c, -⟩ := id hρ
  let χ : A →* ℂˣ := c.character.comp (Subgroup.inclusion hA)
  have hb : ∀ m : s, IsUnitarizable (Subrepresentation.ofSubmodule' (p m)).toRepresentation := by
    intro m
    have hinj := ScalarSubReduction.inclusion_injective ρ (Subrepresentation.ofSubmodule' (p m))
    have hsqS := IsSquareIntegrableModCentralSubgroup.of_injective A hA μ hcof
      (ScalarSubReduction.inclusion ρ (Subrepresentation.ofSubmodule' (p m))) hinj hρ
    have hi : (Subrepresentation.ofSubmodule' (p m)).toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      exact (subrepresentationAsModuleEquiv
        (Subrepresentation.ofSubmodule' (p m))).isSimpleModule_iff.mpr (hsimple m.1 m.2)
    have h : ∀ (a : A) (y : (Subrepresentation.ofSubmodule' (p m)).toSubmodule),
        (Subrepresentation.ofSubmodule' (p m)).toRepresentation a y = (χ a : ℂ) • y :=
      fun a y => (unitaryCentralCharacterComap c
        (ScalarSubReduction.inclusion ρ (Subrepresentation.ofSubmodule' (p m))) hinj).acts
          ⟨a, hA a.2⟩ y
    exact isUnitarizable_of_isSquareIntegrable A hA μ h hcof hsqS hi
  exact isUnitarizable_of_isInternal p hint fun m => (hb m).some

end Unitary

end Langlands.HarishChandraSchwartz
