import Langlands.Representation.RankinSelberg.UnramifiedKirillovInjectivity
import Langlands.Representation.Whittaker.MirabolicKirillovAdapters
import Langlands.Representation.Whittaker.MirabolicMinimalityProof
import Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof
import Langlands.Representation.Induction.CompactFunctionalPairing
import Langlands.Representation.Whittaker.ConjugateCoefficient
import Langlands.Representation.Whittaker.MultiplicityOneProof
import Langlands.Representation.Category.Contragredient

/-!
# Square-summability of Whittaker functions of unitary generic representations on cells
-/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedUnitary

open MeasureTheory GeneralLinear HarmonicAnalysis Induction QuotientIntegration Whittaker

universe uF uV

/-! ### The inverse of the Kirillov map on compactly supported functions -/

section KirillovSection

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (hρ : IsSmooth ρ) (ℓ : glFunctionals ψ n ρ)
  (hinj : Function.Injective (mirabolicCoefficientMap ψ ρ hρ ℓ))
  (hmin : mirabolicCompactSubrepresentation ψ n ≤ mirabolicCoefficientImage ψ ρ hρ ℓ)

include hinj hmin

omit hinj in
theorem exists_kirillov_preimage (f : MirabolicCompactFunctions ψ n) :
    ∃ v : V, mirabolicCoefficientMap ψ ρ hρ ℓ v = f.val :=
  hmin f.property

/-- The vector whose Kirillov function is a given compactly supported function. -/
def kirillovSection : MirabolicCompactFunctions ψ n →ₗ[ℂ] V where
  toFun f := (exists_kirillov_preimage ψ ρ hρ ℓ hmin f).choose
  map_add' f f' := by
    apply hinj
    rw [map_add, (exists_kirillov_preimage ψ ρ hρ ℓ hmin f).choose_spec,
      (exists_kirillov_preimage ψ ρ hρ ℓ hmin f').choose_spec,
      (exists_kirillov_preimage ψ ρ hρ ℓ hmin (f + f')).choose_spec]
    rfl
  map_smul' c f := by
    apply hinj
    rw [map_smul, (exists_kirillov_preimage ψ ρ hρ ℓ hmin f).choose_spec,
      (exists_kirillov_preimage ψ ρ hρ ℓ hmin (c • f)).choose_spec]
    rfl

theorem kirillovSection_spec (f : MirabolicCompactFunctions ψ n) :
    mirabolicCoefficientMap ψ ρ hρ ℓ (kirillovSection ψ ρ hρ ℓ hinj hmin f) = f.val :=
  (exists_kirillov_preimage ψ ρ hρ ℓ hmin f).choose_spec

theorem kirillovSection_eval (f : MirabolicCompactFunctions ψ n) (q : mirabolic n F) :
    ℓ.val (ρ q.val (kirillovSection ψ ρ hρ ℓ hinj hmin f)) = f.val.val.val q := by
  have h := congrArg (fun x => mirabolicEval ψ n x q) (kirillovSection_spec ψ ρ hρ ℓ hinj hmin f)
  rw [mirabolicCoefficientMap_eval] at h
  exact h

theorem kirillovSection_equivariant (g : mirabolic n F) (f : MirabolicCompactFunctions ψ n) :
    kirillovSection ψ ρ hρ ℓ hinj hmin (mirabolicCompactInduced ψ n g f) =
      ρ g.val (kirillovSection ψ ρ hρ ℓ hinj hmin f) := by
  apply hinj
  rw [kirillovSection_spec]
  have h := Representation.IntertwiningMap.isIntertwining _ _
    (mirabolicCoefficientMap ψ ρ hρ ℓ) g (kirillovSection ψ ρ hρ ℓ hinj hmin f)
  change _ = mirabolicCoefficientMap ψ ρ hρ ℓ ((ρ.comp (mirabolic n F).subtype) g _)
  rw [h, kirillovSection_spec]
  rfl

end KirillovSection

/-! ### The two invariant forms -/

section Forms

set_option linter.unusedSectionVars false

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The smooth contragredient, restricted to the mirabolic group. -/
abbrev dualRestriction : Representation ℂ (mirabolic n F) (SmoothDual ρ) :=
  (smoothContragredient ρ).comp (mirabolic n F).subtype

theorem dualRestriction_pairing (g : mirabolic n F) (lam : SmoothDual ρ) (v : V) :
    smoothDualPairing ρ (dualRestriction ρ g lam) v = smoothDualPairing ρ lam (ρ g⁻¹.val v) :=
  rfl

/-- The form `(f, λ) ↦ λ(ι f)` attached to a section `ι` of the Kirillov map. -/
def kirillovForm (ι : MirabolicCompactFunctions ψ n →ₗ[ℂ] V) :
    MirabolicCompactFunctions ψ n →ₗ[ℂ] SmoothDual ρ →ₗ[ℂ] ℂ :=
  (smoothDualPairing ρ).flip ∘ₗ ι

theorem kirillovForm_apply (ι : MirabolicCompactFunctions ψ n →ₗ[ℂ] V)
    (f : MirabolicCompactFunctions ψ n) (lam : SmoothDual ρ) :
    kirillovForm ψ ρ ι f lam = smoothDualPairing ρ lam (ι f) := rfl

theorem kirillovForm_mem (ι : MirabolicCompactFunctions ψ n →ₗ[ℂ] V)
    (hι : ∀ (g : mirabolic n F) f, ι (mirabolicCompactInduced ψ n g f) = ρ g.val (ι f)) :
    kirillovForm ψ ρ ι ∈ InvariantBilinear.forms (mirabolicCompactInduced ψ n)
      (dualRestriction ρ) (fun _ => (1 : ℂ)) := by
  intro g f lam
  rw [kirillovForm_apply, kirillovForm_apply, hι, dualRestriction_pairing, one_mul,
    ← Module.End.mul_apply, ← map_mul]
  change smoothDualPairing ρ lam (ρ (g⁻¹ * g).val (ι f)) = _
  rw [inv_mul_cancel, OneMemClass.coe_one, map_one, Module.End.one_apply]

/-- A standard Whittaker functional, as a functional for the mirabolic unipotent group. -/
def mirabolicFunctional (ℓ : glFunctionals ψ n ρ) :
    Whittaker.functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n)
      (ρ.comp (mirabolic n F).subtype) :=
  ⟨ℓ.val, fun u w => ℓ.property (Mirabolic.upperUnipotentEquiv u) w⟩

theorem mem_glFunctionals_of_mirabolic (lam' : Module.Dual ℂ V)
    (h : lam' ∈ Whittaker.functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n)
      (ρ.comp (mirabolic n F).subtype)) : lam' ∈ glFunctionals ψ n ρ := by
  intro u w
  have := h (Mirabolic.upperUnipotentEquiv.symm u) w
  simp only [mirabolicCharacter_apply, MulEquiv.apply_symm_apply] at this
  exact this

theorem norm_mirabolicCharacter (u : Mirabolic.upperUnipotent n F) :
    ‖(mirabolicCharacter ψ n u : ℂ)‖ = 1 := by
  rw [mirabolicCharacter_apply]
  exact norm_standardCharacter ψ n _

theorem norm_mirabolicCharacter_inv (u : Mirabolic.upperUnipotent n F) :
    ‖((mirabolicCharacter ψ n)⁻¹ u : ℂ)‖ = 1 := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, norm_mirabolicCharacter, inv_one]

theorem mirabolicCharacter_inv_mul (u : Mirabolic.upperUnipotent n F) :
    ((mirabolicCharacter ψ n)⁻¹ u : ℂ) * mirabolicCharacter ψ n u = 1 := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact inv_mul_cancel₀ (Units.ne_zero _)

/-- The contragredient functional attached to `ℓ` by an equivariant conjugate-linear
identification `E` of `ρ` with its smooth dual. -/
def dualFunctional (E : V ≃ₗ⋆[ℂ] SmoothDual ρ)
    (hE : ∀ (g : Langlands.GeneralLinear (n + 1) F) v,
      E (ρ g v) = smoothContragredient ρ g (E v))
    (ℓ : glFunctionals ψ n ρ) :
    Whittaker.functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n)⁻¹
      (dualRestriction ρ) :=
  conjugateFunctional (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) E
    (fun g v => hE g.val v) (norm_mirabolicCharacter ψ) (mirabolicFunctional ψ ρ ℓ)

theorem dualFunctional_apply (E : V ≃ₗ⋆[ℂ] SmoothDual ρ)
    (hE : ∀ (g : Langlands.GeneralLinear (n + 1) F) v,
      E (ρ g v) = smoothContragredient ρ g (E v))
    (ℓ : glFunctionals ψ n ρ) (v : V) :
    (dualFunctional ψ ρ E hE ℓ).val (E v) = starRingEnd ℂ (ℓ.val v) :=
  conjugateFunctional_apply_equiv _ _ _ _ _ _ v

/-- Multiplicity one for the standard Whittaker functionals of `ρ` makes the
inverse-character functionals on the restricted smooth dual a line. -/
theorem eq_smul_dualFunctional (E : V ≃ₗ⋆[ℂ] SmoothDual ρ)
    (hE : ∀ (g : Langlands.GeneralLinear (n + 1) F) v,
      E (ρ g v) = smoothContragredient ρ g (E v))
    (ℓ : glFunctionals ψ n ρ) (hmult : ∀ ℓ' : glFunctionals ψ n ρ, ∃ c : ℂ, ℓ' = c • ℓ)
    (μ : Whittaker.functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n)⁻¹
      (dualRestriction ρ)) :
    ∃ c : ℂ, μ = c • dualFunctional ψ ρ E hE ℓ := by
  have hEs : ∀ (g : mirabolic n F) (lam : SmoothDual ρ),
      E.symm (dualRestriction ρ g lam) = (ρ.comp (mirabolic n F).subtype) g (E.symm lam) := by
    intro g lam
    apply E.injective
    rw [E.apply_symm_apply]
    change _ = E (ρ g.val (E.symm lam))
    rw [hE, E.apply_symm_apply]
    rfl
  let ν := conjugateFunctional (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n)⁻¹ E.symm
    hEs (norm_mirabolicCharacter_inv ψ) μ
  have hν : ν.val ∈ glFunctionals ψ n ρ := by
    apply mem_glFunctionals_of_mirabolic
    intro u w
    have h := ν.property u w
    have e : (mirabolicCharacter ψ n)⁻¹⁻¹ u = mirabolicCharacter ψ n u := by
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv]
    rw [e] at h
    exact h
  obtain ⟨c, hc⟩ := hmult ⟨ν.val, hν⟩
  refine ⟨starRingEnd ℂ c, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro lam
  have h1 : ν.val (E.symm lam) = c * ℓ.val (E.symm lam) := by
    have := congrArg (fun x : glFunctionals ψ n ρ => x.val (E.symm lam)) hc
    simpa using this
  have h2 : ν.val (E.symm lam) = starRingEnd ℂ (μ.val lam) := by
    change starRingEnd ℂ (μ.val (E.symm.symm (E.symm lam))) = _
    rw [LinearEquiv.symm_symm, E.apply_symm_apply]
  have h3 : (dualFunctional ψ ρ E hE ℓ).val lam = starRingEnd ℂ (ℓ.val (E.symm lam)) := by
    conv_lhs => rw [← E.apply_symm_apply lam]
    exact dualFunctional_apply ψ ρ E hE ℓ _
  change μ.val lam = starRingEnd ℂ c * (dualFunctional ψ ρ E hE ℓ).val lam
  rw [h3, ← map_mul, ← h1, h2, Complex.conj_conj]

end Forms

/-! ### Proportionality of forms through an injective map to a line -/

theorem exists_eq_smul_of_injective_line {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] (L : Y →ₗ[ℂ] Z) (hL : Function.Injective L) (z₀ : Z)
    (hspan : ∀ z : Z, ∃ c : ℂ, z = c • z₀) (B₁ B₂ : Y) :
    (∃ κ : ℂ, B₁ = κ • B₂) ∨ B₂ = 0 := by
  obtain ⟨c₁, h₁⟩ := hspan (L B₁)
  obtain ⟨c₂, h₂⟩ := hspan (L B₂)
  by_cases hc : c₂ = 0
  · right
    apply hL
    rw [h₂, hc, zero_smul, map_zero]
  · left
    refine ⟨c₁ / c₂, hL ?_⟩
    rw [map_smul, h₁, h₂, smul_smul, div_mul_cancel₀ _ hc]

/-! ### Cells and their sections -/

section Cells

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (θ : H →* ℂˣ)

/-- The conjugate `g K g⁻¹` of an open subgroup. -/
def conjSub (g : G) (K : OpenSubgroup G) : OpenSubgroup G :=
  K.comap (MulAut.conj g⁻¹).toMonoidHom (IsTopologicalGroup.continuous_conj g⁻¹)

theorem mem_conjSub (g : G) (K : OpenSubgroup G) (x : G) :
    x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  change g⁻¹ * x * g⁻¹⁻¹ ∈ K ↔ _
  rw [inv_inv]

theorem conj_mem_conjSub (g : G) (K : OpenSubgroup G) {k : G} (hk : k ∈ K) :
    g * k * g⁻¹ ∈ conjSub g K := by
  rw [mem_conjSub]
  simpa [mul_assoc] using hk

theorem isCompact_conjSub (g : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    IsCompact (conjSub g K : Set G) := by
  have he : (conjSub g K : Set G) =
      ((Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)) ⁻¹' (K : Set G) := by
    ext x
    simp [mem_conjSub]
  rw [he]
  exact (Homeomorph.isCompact_preimage _).2 hK

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A nonzero value of a `θ`-functional at `π(g) v`, with `v` fixed by `K`, makes the unit
section on `H (g K g⁻¹)` well defined. -/
theorem cell_admissible (π : Representation ℂ G W) (lam : Whittaker.functionals H θ π)
    (K : OpenSubgroup G) (v : W) (hv : ∀ k ∈ K, π k v = v) (g : G)
    (hW : lam.val (π g v) ≠ 0) :
    (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (Induction.conjOpenSubgroup H (conjSub g K) 1).toSubgroup := by
  rw [fixedVectors, Representation.mem_invariants]
  intro p
  have hp : ((p : H) : G) ∈ conjSub g K := by
    have := Induction.mem_conjOpenSubgroup.mp p.property
    simpa using this
  rw [mem_conjSub] at hp
  have h1 : lam.val (π ((p : H) : G) (π g v)) = (θ (p : H) : ℂ) * lam.val (π g v) :=
    lam.property (p : H) (π g v)
  have h2 : π ((p : H) : G) (π g v) = π g v := by
    rw [← Module.End.mul_apply, ← map_mul]
    have he : ((p : H) : G) * g = g * (g⁻¹ * ((p : H) : G) * g) := by group
    rw [he, map_mul, Module.End.mul_apply, hv _ hp]
  rw [h2] at h1
  have h3 : (θ (p : H) : ℂ) = 1 := by
    have := h1.symm
    rw [← sub_eq_zero, ← sub_one_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hW
  change (θ (p : H) : ℂ) * 1 = 1
  rw [h3, mul_one]

/-- The function supported on `H g K` with value `θ(h)` at `h g k`. -/
def cellFunction (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (Induction.conjOpenSubgroup H (conjSub g K) 1).toSubgroup) :
    CompactFunctions H (characterRepresentation θ) :=
  compactInduced H (characterRepresentation θ) g⁻¹
    (compactDoubleCosetSection H (characterRepresentation θ) (conjSub g K)
      (isCompact_conjSub g K hK) 1 1 hv)

variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
  (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (Induction.conjOpenSubgroup H (conjSub g K) 1).toSubgroup)

theorem cellFunction_eval (y : G) :
    eval H _ (cellFunction H θ K hK g hv).1 y =
      eval H _ (compactDoubleCosetSection H (characterRepresentation θ) (conjSub g K)
        (isCompact_conjSub g K hK) 1 1 hv).1 (y * g⁻¹) := rfl

theorem cellFunction_self : eval H _ (cellFunction H θ K hK g hv).1 g = 1 := by
  rw [cellFunction_eval, mul_inv_cancel]
  have h := compactDoubleCosetSection_apply H (characterRepresentation θ) (conjSub g K)
    (isCompact_conjSub g K hK) 1 1 hv 1 1
  simp only [OneMemClass.coe_one, mul_one, map_one, Module.End.one_apply] at h
  exact h

theorem cellFunction_other (y : G) (hy : ∀ (h : H) (k : G), k ∈ K → y ≠ (h : G) * g * k) :
    eval H _ (cellFunction H θ K hK g hv).1 y = 0 := by
  rw [cellFunction_eval]
  by_contra hne
  obtain ⟨k, hk, he⟩ := compactDoubleCosetSection_support_subset H (characterRepresentation θ)
    (conjSub g K) (isCompact_conjSub g K hK) 1 1 hv ⟨y * g⁻¹, hne, rfl⟩
  have hk' : g⁻¹ * k * g ∈ K := (mem_conjSub g K k).mp hk
  have hH : y * g⁻¹ * (1 * k)⁻¹ ∈ H := by
    have := Quotient.exact he
    exact QuotientGroup.rightRel_apply.mp this
  apply hy ⟨_, hH⟩ (g⁻¹ * k * g) hk'
  simp [mul_assoc]

theorem cellFunction_fixed (k : G) (hk : k ∈ K) :
    compactInduced H (characterRepresentation θ) k (cellFunction H θ K hK g hv) =
      cellFunction H θ K hK g hv := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext y
  change eval H _ (cellFunction H θ K hK g hv).1 (y * k) = eval H _ (cellFunction H θ K hK g hv).1 y
  rw [cellFunction_eval, cellFunction_eval]
  have he : y * k * g⁻¹ = y * g⁻¹ * (g * k * g⁻¹) := by group
  rw [he]
  exact compactDoubleCosetSection_mul H (characterRepresentation θ) (conjSub g K)
    (isCompact_conjSub g K hK) 1 1 hv ⟨_, conj_mem_conjSub g K hk⟩ (y * g⁻¹)

end Cells

/-! ### The integral pairing on cells -/

section CellPairing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (θ θ' : H →* ℂˣ) {X : Type*} [AddCommGroup X] [Module ℂ X]
  (σ : Representation ℂ G X) (hσ : IsSmooth σ) (μ : Whittaker.functionals H θ' σ)
  (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)
  [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)]
  (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]

/-- The integral pairing of the section of the cell `H g K` with a `K`-fixed vector. -/
theorem pairing_cellFunction
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (Induction.conjOpenSubgroup H (conjSub g K) 1).toSubgroup)
    (x : X) (hx : ∀ k ∈ K, σ k x = x) :
    CompactFunctionalPairing.pairing H θ θ' σ hσ μ hθ' ν (cellFunction H θ K hK g hv) x =
      ((ν (compactOpenQuotientOrbit H (conjSub g K))).toReal : ℂ) * μ.val (σ g x) := by
  have hmem := CompactFunctionalPairing.pairing_mem H θ θ' σ hσ μ hθ' ν hinv
  have h1 := hmem g⁻¹ (compactDoubleCosetSection H (characterRepresentation θ) (conjSub g K)
      (isCompact_conjSub g K hK) 1 1 hv) (σ g x)
  rw [one_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] at h1
  change CompactFunctionalPairing.pairing H θ θ' σ hσ μ hθ' ν
    (compactInduced H (characterRepresentation θ) g⁻¹ _) x = _
  rw [h1]
  apply CompactFunctionalPairing.pairing_section
  intro k hk
  rw [← Module.End.mul_apply, ← map_mul]
  have he : k * g = g * (g⁻¹ * k * g) := by group
  rw [he, map_mul, Module.End.mul_apply, hx _ ((mem_conjSub g K k).mp hk)]

end CellPairing

/-! ### The uniform bound -/

section Bound

set_option linter.unusedSectionVars false

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (hρ : IsSmooth ρ) (ℓ : glFunctionals ψ n ρ)

/-- Cauchy–Schwarz for an invariant positive form. -/
theorem norm_inner_sq_le (b : InvariantPositiveForm ρ) (x y : V) :
    ‖b.inner x y‖ ^ 2 ≤ (b.inner x x).re * (b.inner y y).re := by
  have h : ‖b.inner x y‖ * ‖b.inner y x‖ ≤ (b.inner x x).re * (b.inner y y).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := b.toInnerProductCore.toCore) x y
  have hs : ‖b.inner y x‖ = ‖b.inner x y‖ := by
    rw [← b.conj_inner_symm x y, Complex.norm_conj]
  rw [hs, ← sq] at h
  exact h

/-- The scalar inequality behind the bound: `‖κ S‖² ≤ R re(κ S)` and `κ ≠ 0` give
`S ≤ ‖κ‖⁻¹ R`. -/
theorem le_of_norm_sq_le_re {κ : ℂ} (hκ : κ ≠ 0) {S R : ℝ} (hS : 0 ≤ S) (hR : 0 ≤ R)
    (h : ‖κ * S‖ ^ 2 ≤ R * (κ * S).re) : S ≤ ‖κ‖⁻¹ * R := by
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hnorm : ‖κ * (S : ℂ)‖ = ‖κ‖ * S := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hS]
  have hre : (κ * (S : ℂ)).re ≤ ‖κ‖ * S := by
    rw [← hnorm]
    exact Complex.re_le_norm _
  rw [hnorm] at h
  have h2 : (‖κ‖ * S) ^ 2 ≤ R * (‖κ‖ * S) := h.trans (mul_le_mul_of_nonneg_left hre hR)
  have h3 : ‖κ‖ * S ≤ R := by
    rcases hS.lt_or_eq with hSpos | hS0
    · have hpos : 0 < ‖κ‖ * S := mul_pos hκn hSpos
      nlinarith
    · rw [← hS0, mul_zero]
      exact hR
  rw [inv_mul_eq_div, le_div_iff₀ hκn]
  linarith

/-- Evaluation of compactly supported mirabolic functions at a point. -/
def evalAt (y : mirabolic n F) : MirabolicCompactFunctions ψ n →ₗ[ℂ] ℂ where
  toFun f := f.val.val.val y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The admissibility of the cell section, phrased with the standard functional. -/
theorem cell_admissible_mirabolic (K : OpenSubgroup (mirabolic n F)) (v : V)
    (hv : ∀ k ∈ K, ρ k.val v = v) (g : mirabolic n F) (hW : ℓ.val (ρ g.val v) ≠ 0) :
    (1 : ℂ) ∈ fixedVectors (characterRepresentation (mirabolicCharacter ψ n))
      (Induction.conjOpenSubgroup (Mirabolic.upperUnipotent n F) (conjSub g K) 1).toSubgroup :=
  cell_admissible _ _ (ρ.comp (mirabolic n F).subtype) (mirabolicFunctional ψ ρ ℓ) K v hv g hW

/-- The cell section `cellFunction`, as a compactly supported mirabolic function. -/
def mirabolicCell (K : OpenSubgroup (mirabolic n F)) (hK : IsCompact (K : Set (mirabolic n F)))
    (g : mirabolic n F)
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation (mirabolicCharacter ψ n))
      (Induction.conjOpenSubgroup (Mirabolic.upperUnipotent n F) (conjSub g K) 1).toSubgroup) :
    MirabolicCompactFunctions ψ n :=
  cellFunction (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) K hK g hv

/-- The family of cell sections attached to the points `g i` with nonzero Whittaker value. -/
def cellFamily (K : OpenSubgroup (mirabolic n F)) (hK : IsCompact (K : Set (mirabolic n F)))
    (v : V) (hv : ∀ k ∈ K, ρ k.val v = v) (g : ℕ → mirabolic n F) (i : ℕ) :
    MirabolicCompactFunctions ψ n :=
  if h : ℓ.val (ρ (g i).val v) = 0 then 0 else
    mirabolicCell ψ K hK (g i) (cell_admissible_mirabolic ψ ρ ℓ K v hv (g i) h)

theorem cellFamily_of_eq_zero (K : OpenSubgroup (mirabolic n F))
    (hK : IsCompact (K : Set (mirabolic n F))) (v : V) (hv : ∀ k ∈ K, ρ k.val v = v)
    (g : ℕ → mirabolic n F) (i : ℕ) (h : ℓ.val (ρ (g i).val v) = 0) :
    cellFamily ψ ρ ℓ K hK v hv g i = 0 := by
  unfold cellFamily
  exact dite_eq_left h

theorem cellFamily_of_ne_zero (K : OpenSubgroup (mirabolic n F))
    (hK : IsCompact (K : Set (mirabolic n F))) (v : V) (hv : ∀ k ∈ K, ρ k.val v = v)
    (g : ℕ → mirabolic n F) (i : ℕ) (h : ℓ.val (ρ (g i).val v) ≠ 0) :
    cellFamily ψ ρ ℓ K hK v hv g i =
      mirabolicCell ψ K hK (g i) (cell_admissible_mirabolic ψ ρ ℓ K v hv (g i) h) := by
  unfold cellFamily
  exact dite_eq_right h

theorem evalAt_mirabolicCell_self (K : OpenSubgroup (mirabolic n F))
    (hK : IsCompact (K : Set (mirabolic n F))) (g : mirabolic n F)
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation (mirabolicCharacter ψ n))
      (Induction.conjOpenSubgroup (Mirabolic.upperUnipotent n F) (conjSub g K) 1).toSubgroup) :
    evalAt ψ g (mirabolicCell ψ K hK g hv) = 1 :=
  cellFunction_self (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) K hK g hv

theorem evalAt_mirabolicCell_other (K : OpenSubgroup (mirabolic n F))
    (hK : IsCompact (K : Set (mirabolic n F))) (g : mirabolic n F)
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation (mirabolicCharacter ψ n))
      (Induction.conjOpenSubgroup (Mirabolic.upperUnipotent n F) (conjSub g K) 1).toSubgroup)
    (y : mirabolic n F)
    (hy : ∀ (h : Mirabolic.upperUnipotent n F) (k : mirabolic n F), k ∈ K →
      y ≠ (h : mirabolic n F) * g * k) :
    evalAt ψ y (mirabolicCell ψ K hK g hv) = 0 :=
  cellFunction_other (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) K hK g hv y hy

theorem mirabolicCell_fixed (K : OpenSubgroup (mirabolic n F))
    (hK : IsCompact (K : Set (mirabolic n F))) (g : mirabolic n F)
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation (mirabolicCharacter ψ n))
      (Induction.conjOpenSubgroup (Mirabolic.upperUnipotent n F) (conjSub g K) 1).toSubgroup)
    (k : mirabolic n F) (hk : k ∈ K) :
    mirabolicCompactInduced ψ n k (mirabolicCell ψ K hK g hv) = mirabolicCell ψ K hK g hv :=
  cellFunction_fixed (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) K hK g hv k hk

/-- The bound, given the value of `b(u, ι f)` on cell sections. -/
theorem bound_of_cell_formula (b : InvariantPositiveForm ρ)
    (ι : MirabolicCompactFunctions ψ n →ₗ[ℂ] V)
    (hιeq : ∀ (g : mirabolic n F) f, ι (mirabolicCompactInduced ψ n g f) = ρ g.val (ι f))
    (hιeval : ∀ f (q : mirabolic n F), ℓ.val (ρ q.val (ι f)) = f.val.val.val q)
    (M : OpenSubgroup (mirabolic n F) → ℝ) (hM : ∀ J, 0 ≤ M J) (κ : ℂ)
    (hcell : ∀ (K : OpenSubgroup (mirabolic n F)) (hK : IsCompact (K : Set (mirabolic n F)))
      (g : mirabolic n F)
      (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation (mirabolicCharacter ψ n))
        (Induction.conjOpenSubgroup (Mirabolic.upperUnipotent n F) (conjSub g K) 1).toSubgroup)
      (u : V), (∀ k ∈ K, ρ k.val u = u) →
      b.inner u (ι (mirabolicCell ψ K hK g hv)) =
        κ * ((M (conjSub g K) : ℂ) * starRingEnd ℂ (ℓ.val (ρ g.val u))))
    (v : V) (K : OpenSubgroup (mirabolic n F)) (hK : IsCompact (K : Set (mirabolic n F)))
    (hvK : ∀ k ∈ K, ρ k.val v = v) (s : Finset ℕ) (g : ℕ → mirabolic n F)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (h : Mirabolic.upperUnipotent n F) (k : mirabolic n F),
      k ∈ K → g i ≠ (h : mirabolic n F) * g j * k) :
    ∑ i ∈ s, M (conjSub (g i) K) * ‖ℓ.val (ρ (g i).val v)‖ ^ 2 ≤
      (if κ = 0 then 0 else ‖κ‖⁻¹) * (b.inner v v).re := by
  classical
  let W : ℕ → ℂ := fun i => ℓ.val (ρ (g i).val v)
  let cf := cellFamily ψ ρ ℓ K hK v hvK g
  let φ : MirabolicCompactFunctions ψ n := ∑ i ∈ s, W i • cf i
  let m : ℕ → ℝ := fun i => M (conjSub (g i) K)
  have hterm : ∀ i, ∀ u : V, (∀ k ∈ K, ρ k.val u = u) →
      W i * b.inner u (ι (cf i)) =
        W i * (κ * ((m i : ℂ) * starRingEnd ℂ (ℓ.val (ρ (g i).val u)))) := by
    intro i u hu
    by_cases hW : W i = 0
    · rw [hW, zero_mul, zero_mul]
    · congr 1
      rw [show cf i = _ from cellFamily_of_ne_zero ψ ρ ℓ K hK v hvK g i hW]
      exact hcell K hK (g i) _ u hu
  have hinner : ∀ u : V,
      b.inner u (ι φ) = ∑ i ∈ s, W i * b.inner u (ι (cf i)) := by
    intro u
    have he : ι φ = ∑ i ∈ s, W i • ι (cf i) := by
      simp only [φ, map_sum, map_smul]
    rw [he]
    change b.rightFunctional u _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, InvariantPositiveForm.rightFunctional_apply]
  have hφfix : ∀ k ∈ K, ρ k.val (ι φ) = ι φ := by
    intro k hk
    rw [← hιeq]
    congr 1
    simp only [φ, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    by_cases hW : W i = 0
    · rw [show cf i = 0 from cellFamily_of_eq_zero ψ ρ ℓ K hK v hvK g i hW, map_zero]
    · rw [show cf i = _ from cellFamily_of_ne_zero ψ ρ ℓ K hK v hvK g i hW]
      exact mirabolicCell_fixed ψ K hK (g i) _ k hk
  have hcfself : ∀ i, W i * evalAt ψ (g i) (cf i) = W i := by
    intro i
    by_cases hW : W i = 0
    · rw [hW, zero_mul]
    · rw [show cf i = _ from cellFamily_of_ne_zero ψ ρ ℓ K hK v hvK g i hW,
        evalAt_mirabolicCell_self, mul_one]
  have hcfother : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → evalAt ψ (g i) (cf j) = 0 := by
    intro i hi j hj hji
    by_cases hW : W j = 0
    · rw [show cf j = 0 from cellFamily_of_eq_zero ψ ρ ℓ K hK v hvK g j hW, map_zero]
    · rw [show cf j = _ from cellFamily_of_ne_zero ψ ρ ℓ K hK v hvK g j hW]
      exact evalAt_mirabolicCell_other ψ K hK (g j) _ (g i)
        (fun h k hk => hdist i hi j hj (Ne.symm hji) h k hk)
  have hval : ∀ i ∈ s, ℓ.val (ρ (g i).val (ι φ)) = W i := by
    intro i hi
    rw [hιeval]
    change evalAt ψ (g i) φ = W i
    simp only [φ, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j hj hji => by rw [hcfother i hi j hj hji, mul_zero])
      (fun h => absurd hi h)]
    exact hcfself i
  have hsq : ∀ i, W i * (κ * ((m i : ℂ) * starRingEnd ℂ (W i))) =
      κ * ((m i * ‖W i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj' (W i)]
    ring
  let S : ℝ := ∑ i ∈ s, m i * ‖W i‖ ^ 2
  have hvφ : b.inner v (ι φ) = κ * S := by
    rw [hinner v, Finset.sum_congr rfl (fun i _ => hterm i v hvK)]
    change _ = κ * ((∑ i ∈ s, m i * ‖W i‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact hsq i
  have hφφ : b.inner (ι φ) (ι φ) = κ * S := by
    rw [hinner (ι φ), Finset.sum_congr rfl (fun i _ => hterm i (ι φ) hφfix)]
    change _ = κ * ((∑ i ∈ s, m i * ‖W i‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hval i hi]
    exact hsq i
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hM _) (sq_nonneg _))
  have hR : 0 ≤ (b.inner v v).re := b.re_inner_nonneg v
  have hcs := norm_inner_sq_le ρ b v (ι φ)
  rw [hvφ, hφφ] at hcs
  change S ≤ (if κ = 0 then 0 else ‖κ‖⁻¹) * (b.inner v v).re
  by_cases hκ0 : κ = 0
  · rw [ite_eq_left hκ0, zero_mul]
    have hz : ι φ = 0 := by
      apply b.definite
      rw [hφφ, hκ0, zero_mul]
    have hW0 : ∀ i ∈ s, W i = 0 := by
      intro i hi
      rw [← hval i hi, hz, map_zero, map_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    rw [hW0 i hi, norm_zero]
    ring
  · rw [ite_eq_right hκ0]
    exact le_of_norm_sq_le_re hκ0 hS0 hR hcs

/-- **The cell bound.** For a smooth representation `ρ` of `GL_(n+1)` with an invariant
positive form `b`, a standard Whittaker functional `ℓ` spanning the functionals, an
injective Kirillov map whose image contains the compact functions, and a right-invariant
measure `ν` on `N \ P` with positive finite orbit masses, there is a constant `C` such that
for every vector `v` fixed by a compact open subgroup `K` of `P` and every finite family of
pairwise distinct cells `N g_i K`,
`∑ ν(N \ N g_i K g_i⁻¹) |ℓ(ρ(g_i) v)|² ≤ C b(v, v)`. -/
theorem cellBound_core
    (hinj : Function.Injective (mirabolicCoefficientMap ψ ρ hρ ℓ))
    (hmin : mirabolicCompactSubrepresentation ψ n ≤ mirabolicCoefficientImage ψ ρ hρ ℓ)
    (hmult : ∀ ℓ' : glFunctionals ψ n ρ, ∃ c : ℂ, ℓ' = c • ℓ)
    (b : InvariantPositiveForm ρ) (E : V ≃ₗ⋆[ℂ] SmoothDual ρ)
    (hEb : ∀ v, E v = b.toSmoothDual hρ v)
    [T2Space F] [T2Space (mirabolic n F)]
    (hG : ∀ O : Set (mirabolic n F), IsOpen O → (1 : mirabolic n F) ∈ O →
      ∃ K : OpenSubgroup (mirabolic n F), IsCompact (K : Set (mirabolic n F)) ∧
        (K : Set (mirabolic n F)) ⊆ O)
    (hσ : IsSmooth (characterRepresentation (mirabolicCharacter ψ n)))
    [MeasurableSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F))]
    [BorelSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F))]
    (ν : Measure (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F)))
    [IsFiniteMeasureOnCompacts ν]
    (hinv : ∀ g : mirabolic n F,
      MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν)
    (hmass : ∀ J : OpenSubgroup (mirabolic n F), IsCompact (J : Set (mirabolic n F)) →
      0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V) (K : OpenSubgroup (mirabolic n F)),
      IsCompact (K : Set (mirabolic n F)) → (∀ k ∈ K, ρ k.val v = v) →
      ∀ (s : Finset ℕ) (g : ℕ → mirabolic n F),
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (h : Mirabolic.upperUnipotent n F) (k : mirabolic n F),
          k ∈ K → g i ≠ (h : mirabolic n F) * g j * k) →
        ∑ i ∈ s, (ν (compactOpenQuotientOrbit _ (conjSub (g i) K))).toReal *
            ‖ℓ.val (ρ (g i).val v)‖ ^ 2 ≤ C * (b.inner v v).re := by
  classical
  let H := Mirabolic.upperUnipotent n F
  let θ := mirabolicCharacter ψ n
  let X := dualRestriction ρ
  have hX : IsSmooth X :=
    isSmooth_comp (mirabolic n F).subtype continuous_subtype_val (isSmooth_smoothPart ρ.dual)
  have hE : ∀ (g : Langlands.GeneralLinear (n + 1) F) v,
      E (ρ g v) = smoothContragredient ρ g (E v) := by
    intro g v
    rw [hEb, hEb]
    exact b.toSmoothDual_apply_action hρ g v
  let μ0 := dualFunctional ψ ρ E hE ℓ
  have hθ' := mirabolicCharacter_inv_mul ψ (n := n)
  obtain ⟨L, hL⟩ := FormsFunctional.exists_injective_formsFunctional hG H
    Mirabolic.upperUnipotent_isClosed θ hσ X hX ν hinv hmass θ⁻¹ hθ'
  let ι := kirillovSection ψ ρ hρ ℓ hinj hmin
  let B1 : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) X
      (fun _ => (1 : ℂ)) :=
    ⟨kirillovForm ψ ρ ι, kirillovForm_mem ψ ρ ι (kirillovSection_equivariant ψ ρ hρ ℓ hinj hmin)⟩
  let B2 : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) X
      (fun _ => (1 : ℂ)) :=
    ⟨CompactFunctionalPairing.pairing H θ θ⁻¹ X hX μ0 hθ' ν,
      CompactFunctionalPairing.pairing_mem H θ θ⁻¹ X hX μ0 hθ' ν hinv⟩
  -- evaluation of the two forms
  have hB1 : ∀ f u, B1.val f (E u) = b.inner u (ι f) := by
    intro f u
    change smoothDualPairing ρ (E u) (ι f) = _
    rw [hEb]
    rfl
  have hB2 : ∀ (K : OpenSubgroup (mirabolic n F)) (hK : IsCompact (K : Set (mirabolic n F)))
      (g : mirabolic n F) (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
        (Induction.conjOpenSubgroup H (conjSub g K) 1).toSubgroup)
      (u : V), (∀ k ∈ K, ρ k.val u = u) →
      B2.val (cellFunction H θ K hK g hv) (E u) =
        ((ν (compactOpenQuotientOrbit H (conjSub g K))).toReal : ℂ) *
          starRingEnd ℂ (ℓ.val (ρ g.val u)) := by
    intro K hK g hv u hu
    have hx : ∀ k ∈ K, X k (E u) = E u := by
      intro k hk
      change smoothContragredient ρ k.val (E u) = E u
      rw [← hE, hu k hk]
    change CompactFunctionalPairing.pairing H θ θ⁻¹ X hX μ0 hθ' ν _ _ = _
    rw [pairing_cellFunction H θ θ⁻¹ X hX μ0 hθ' ν hinv K hK g hv (E u) hx]
    congr 1
    change μ0.val (smoothContragredient ρ g.val (E u)) = _
    rw [← hE]
    exact dualFunctional_apply ψ ρ E hE ℓ _
  have hvP : ∀ (K : OpenSubgroup (mirabolic n F)) (u : V), (∀ k ∈ K, ρ k.val u = u) →
      ∀ k ∈ K, (ρ.comp (mirabolic n F).subtype) k u = u := fun K u hu k hk => hu k hk
  have hmassne : ∀ (K : OpenSubgroup (mirabolic n F)), IsCompact (K : Set (mirabolic n F)) →
      ∀ g : mirabolic n F, ((ν (compactOpenQuotientOrbit H (conjSub g K))).toReal : ℂ) ≠ 0 := by
    intro K hK g
    obtain ⟨hpos, hfin⟩ := hmass _ (isCompact_conjSub g K hK)
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  rcases exists_eq_smul_of_injective_line L hL μ0 (eq_smul_dualFunctional ψ ρ E hE ℓ hmult)
      B1 B2 with ⟨κ, hκ⟩ | h0
  · refine ⟨if κ = 0 then 0 else ‖κ‖⁻¹, by split_ifs <;> positivity, ?_⟩
    intro v K hK hvK s g hdist
    refine bound_of_cell_formula ψ ρ ℓ b ι (kirillovSection_equivariant ψ ρ hρ ℓ hinj hmin)
      (kirillovSection_eval ψ ρ hρ ℓ hinj hmin)
      (fun J => (ν (compactOpenQuotientOrbit H J)).toReal) (fun J => ENNReal.toReal_nonneg) κ
      ?_ v K hK hvK s g hdist
    intro K' hK' g' hv' u hu
    have h1 := hB1 (mirabolicCell ψ K' hK' g' hv') u
    have h2 : B1.val (mirabolicCell ψ K' hK' g' hv') (E u) =
        κ * B2.val (mirabolicCell ψ K' hK' g' hv') (E u) := by
      rw [hκ]
      rfl
    rw [← h1, h2]
    exact congrArg (κ * ·) (hB2 K' hK' g' hv' u hu)
  · refine ⟨0, le_rfl, ?_⟩
    intro v K hK hvK s g _
    rw [zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i _
    by_cases hW : ℓ.val (ρ (g i).val v) = 0
    · rw [hW, norm_zero]
      ring
    · exfalso
      have hv := cell_admissible H θ (ρ.comp (mirabolic n F).subtype)
        (mirabolicFunctional ψ ρ ℓ) K v (hvP K v hvK) (g i) hW
      have h1 := hB2 K hK (g i) hv v hvK
      rw [h0] at h1
      change (0 : _ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) _ _ = _ at h1
      rw [LinearMap.zero_apply, LinearMap.zero_apply] at h1
      exact mul_ne_zero (hmassne K hK (g i)) ((map_ne_zero (starRingEnd ℂ)).mpr hW) h1.symm

end Bound

/-! ### The p-adic specialization -/

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The cell bound for an irreducible admissible generic unitarizable representation of
`GL_(n+1)(F)`, `F` a p-adic field with its canonical topology. -/
theorem padicCellBound (F : PadicField.{uF} p) (n : ℕ) {V : Type uV} [AddCommGroup V]
    [Module ℂ V]
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    letI : IsTopologicalRing F.Carrier := by
      let := F.canonicalTopologicalData.valuativeRel
      let := F.canonicalTopologicalData.localField
      infer_instance
    IsAdmissible ρ → Representation.IsIrreducible ρ → IsUnitarizable ρ →
    ∀ ℓ : glFunctionals ψ n ρ, ℓ.val ≠ 0 →
    ∀ [MeasurableSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F.Carrier))]
      [BorelSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F.Carrier))]
      (ν : Measure (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F.Carrier))),
      IsFiniteMeasureOnCompacts ν →
      (∀ g : mirabolic n F.Carrier,
        MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν) →
      (∀ J : OpenSubgroup (mirabolic n F.Carrier), IsCompact (J : Set (mirabolic n F.Carrier)) →
        0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤) →
      ∀ (v : V) (K : OpenSubgroup (mirabolic n F.Carrier)),
        IsCompact (K : Set (mirabolic n F.Carrier)) → (∀ k ∈ K, ρ k.val v = v) →
        ∃ C : ℝ, ∀ (s : Finset ℕ) (g : ℕ → mirabolic n F.Carrier),
          (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (h : Mirabolic.upperUnipotent n F.Carrier)
            (k : mirabolic n F.Carrier), k ∈ K → g i ≠ (h : mirabolic n F.Carrier) * g j * k) →
          ∑ i ∈ s, (ν (compactOpenQuotientOrbit _ (conjSub (g i) K))).toReal *
              ‖ℓ.val (ρ (g i).val v)‖ ^ 2 ≤ C := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := MirabolicCompactTwistedPairing.valuative_nonarchimedean (K := F.Carrier)
  have : ∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F.Carrier) :=
    T.generalLinearNonarchimedean
  have : ∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F.Carrier) :=
    T.generalLinearLocallyCompactSpace
  have : NonarchimedeanGroup (mirabolic n F.Carrier) :=
    MirabolicWhittaker.mirabolic_nonarchimedean
  have : LocallyCompactSpace (mirabolic n F.Carrier) := Mirabolic.locallyCompactSpace
  intro hadm hirr hunit ℓ hℓ _ _ ν hfin hinv hmass v K hK hvK
  obtain ⟨b⟩ := hunit
  have hρ : IsSmooth ρ := hadm.1
  have hG : ∀ O : Set (mirabolic n F.Carrier), IsOpen O → (1 : mirabolic n F.Carrier) ∈ O →
      ∃ K : OpenSubgroup (mirabolic n F.Carrier), IsCompact (K : Set (mirabolic n F.Carrier)) ∧
        (K : Set (mirabolic n F.Carrier)) ⊆ O :=
    fun O hO h1 => compactOpenSubgroupBasis _ O (hO.mem_nhds h1)
  have hstd : IsOpen ((standardCharacter ψ n).ker :
      Set (GeneralLinear.upperUnipotent (n + 1) F.Carrier)) := by
    have := T.upperUnipotentNonarchimedean (n + 1)
    exact isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous
  have hker : IsOpen ((mirabolicCharacter ψ n).ker :
      Set (Mirabolic.upperUnipotent n F.Carrier)) :=
    hstd.preimage Mirabolic.upperUnipotentContinuousEquiv.continuous
  have hσ := MirabolicCompactTwistedPairing.isSmooth_characterRepresentation _ hker
  have hmult : ∀ ℓ' : glFunctionals ψ n ρ, ∃ c : ℂ, ℓ' = c • ℓ := by
    intro ℓ'
    obtain ⟨c, hc, -⟩ := Whittaker.multiplicityOne p inferInstance F n V ψ ρ hadm hirr ℓ ℓ' hℓ
    exact ⟨c, hc⟩
  have hinj : Function.Injective (mirabolicCoefficientMap ψ ρ hρ ℓ) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply kirillov_injective T ψ n ρ hρ hirr ℓ hℓ hmult w
    intro q
    have := congrArg (fun x => mirabolicEval ψ n x q) hw
    rw [mirabolicCoefficientMap_eval] at this
    exact this
  have hmin : mirabolicCompactSubrepresentation ψ n ≤ mirabolicCoefficientImage ψ ρ hρ ℓ :=
    Whittaker.mirabolicCompactMinimality p inferInstance F n ψ _
      (mirabolicCoefficientImage_ne_bot ψ ρ hρ ℓ hℓ)
  obtain ⟨C, -, hC⟩ := cellBound_core ψ ρ hρ ℓ hinj hmin hmult b
    (b.smoothDualEquiv (GeneralLinear.compactOpen_cofinal F T (n + 1)) hadm)
    (fun w => rfl) hG hσ ν hinv hmass
  exact ⟨C * (b.inner v v).re, fun s g hdist => hC v K hK hvK s g hdist⟩

end Padic

end Langlands.RankinSelberg.UnramifiedUnitary
