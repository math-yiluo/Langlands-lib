import Langlands.Group.HaarModulus
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Category.Twist
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# BZ77 1.8 functors for closed semidirect triples

For closed subgroups `M`, `U`, `P` of a locally compact group `G` with `M`
normalizing `U`, `M ∩ U = 1` and `P = MU`, and a locally constant character `θ`
of `U` fixed by `M`, this file constructs the normalized smooth induction
`I_{U,θ}`, the normalized compact induction `i_{U,θ}` and (for nonarchimedean `G`)
the normalized `θ`-localization `r_{U,θ}` of Bernstein–Zelevinsky (1977), 1.8.

The unique algebraic decomposition `p = u*m` of `P`, its projection to `M` and the
inflation of `θ` are derived from the subgroup equalities. Induced functions are
built from the published covariant-function constructors for an arbitrary scalar
character `ν` of `M`; the normalized functors take `ν = mod_U^{1/2}`. Localization
twists the published `θ`-coinvariant functor by `mod_U^{-1/2}`.
-/

noncomputable section

open CategoryTheory MeasureTheory
open scoped Pointwise NNReal

namespace Langlands.ClosedSemidirect

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual subgroup hypotheses of BZ77 1.8, before choosing a character. -/
structure Triple (G : Type uG) [Group G] [TopologicalSpace G] where
  /-- The acting subgroup. -/
  M : Subgroup G
  /-- The normalized subgroup carrying the character. -/
  U : Subgroup G
  /-- The subgroup `MU`. -/
  P : Subgroup G
  /-- `M` is closed. -/
  closed_M : IsClosed (M : Set G)
  /-- `U` is closed. -/
  closed_U : IsClosed (U : Set G)
  /-- `P = MU` is closed. -/
  closed_P : IsClosed (P : Set G)
  /-- `M` normalizes `U`. -/
  normalizes : M ≤ Subgroup.normalizer (U : Set G)
  /-- `M ∩ U = {1}`. -/
  intersection : M ⊓ U = ⊥
  /-- The carrier of `P` is the pointwise product `MU`. -/
  product_eq : (P : Set G) = (M : Set G) * (U : Set G)

namespace Triple

variable (T : Triple G)

theorem product_eq_reverse : (T.P : Set G) = (T.U : Set G) * (T.M : Set G) :=
  T.product_eq.trans (Subgroup.set_mul_normalizer_comm _ _ T.normalizes)

theorem M_le_P : T.M ≤ T.P := by
  intro m hm
  change m ∈ (T.P : Set G)
  rw [T.product_eq]
  exact ⟨m, hm, 1, T.U.one_mem, mul_one m⟩

theorem U_le_P : T.U ≤ T.P := by
  intro u hu
  change u ∈ (T.P : Set G)
  rw [T.product_eq]
  exact ⟨1, T.M.one_mem, u, hu, one_mul u⟩

/-- Conjugation `u ↦ m u m⁻¹` on the actual subgroup `U`, as in `Jacquet.Localization`. -/
abbrev conjugate (m : T.M) (u : T.U) : T.U :=
  Jacquet.Localization.conjugate T.U T.M T.normalizes m u

@[simp] theorem conjugate_val (m : T.M) (u : T.U) :
    (T.conjugate m u : G) = (m : G) * u * (m : G)⁻¹ := rfl

/-- The actual product `u*m`, regarded as an element of `P`. -/
def combine (u : T.U) (m : T.M) : T.P :=
  ⟨(u : G) * m, T.P.mul_mem (T.U_le_P u.property) (T.M_le_P m.property)⟩

@[simp] theorem combine_val (u : T.U) (m : T.M) :
    (T.combine u m : G) = (u : G) * m := rfl

theorem combine_one_one : T.combine 1 1 = 1 := by
  apply Subtype.ext
  simp

theorem combine_bijective : Function.Bijective (fun x : T.U × T.M => T.combine x.1 x.2) := by
  constructor
  · intro x y h
    apply Subgroup.mul_injective_of_disjoint (H₁ := T.U) (H₂ := T.M)
      (disjoint_iff.mpr (by rw [inf_comm, T.intersection]))
    exact congrArg Subtype.val h
  · intro p
    have hp : (p : G) ∈ (T.U : Set G) * (T.M : Set G) := by
      rw [← T.product_eq_reverse]
      exact p.property
    obtain ⟨u, hu, m, hm, hum⟩ := hp
    exact ⟨(⟨u, hu⟩, ⟨m, hm⟩), Subtype.ext hum⟩

/-- The unique algebraic decomposition `p = u*m`. It carries no asserted continuity. -/
def decomposition : T.P ≃ T.U × T.M :=
  (Equiv.ofBijective (fun x : T.U × T.M => T.combine x.1 x.2) T.combine_bijective).symm

@[simp] theorem decomposition_combine (u : T.U) (m : T.M) :
    T.decomposition (T.combine u m) = (u, m) :=
  T.decomposition.apply_symm_apply (u, m)

@[simp] theorem combine_decomposition (p : T.P) :
    T.combine (T.decomposition p).1 (T.decomposition p).2 = p :=
  T.decomposition.symm_apply_apply p

theorem decomposition_val (p : T.P) :
    ((T.decomposition p).1 : G) * ((T.decomposition p).2 : G) = p :=
  congrArg Subtype.val (T.combine_decomposition p)

theorem decomposition_unique (p : T.P) (u : T.U) (m : T.M)
    (h : (u : G) * m = p) : T.decomposition p = (u, m) := by
  have hp : T.combine u m = p := Subtype.ext h
  rw [← hp, T.decomposition_combine]

theorem combine_mul (u v : T.U) (m n : T.M) :
    T.combine u m * T.combine v n = T.combine (u * T.conjugate m v) (m * n) := by
  apply Subtype.ext
  simp [combine, Jacquet.Localization.conjugate, mul_assoc]

theorem decomposition_mul (p q : T.P) :
    T.decomposition (p * q) =
      ((T.decomposition p).1 * T.conjugate (T.decomposition p).2 (T.decomposition q).1,
       (T.decomposition p).2 * (T.decomposition q).2) := by
  obtain ⟨⟨u, m⟩, rfl⟩ := T.combine_bijective.surjective p
  obtain ⟨⟨v, n⟩, rfl⟩ := T.combine_bijective.surjective q
  simp only [T.combine_mul, T.decomposition_combine]

/-- The projection `P → M`, `u*m ↦ m`. -/
def projection : T.P →* T.M where
  toFun p := (T.decomposition p).2
  map_one' := by
    simpa [T.combine_one_one] using congrArg Prod.snd (T.decomposition_combine 1 1)
  map_mul' p q := congrArg Prod.snd (T.decomposition_mul p q)

theorem projection_apply (p : T.P) : T.projection p = (T.decomposition p).2 := rfl

/-- The actual inclusion of `M` in `P`. -/
def sectionM : T.M →* T.P := Subgroup.inclusion T.M_le_P

/-- The actual inclusion of `U` in `P`. -/
def sectionU : T.U →* T.P := Subgroup.inclusion T.U_le_P

@[simp] theorem sectionM_val (m : T.M) : (T.sectionM m : G) = m := rfl

@[simp] theorem sectionU_val (u : T.U) : (T.sectionU u : G) = u := rfl

@[simp] theorem projection_combine (u : T.U) (m : T.M) :
    T.projection (T.combine u m) = m :=
  congrArg Prod.snd (T.decomposition_combine u m)

@[simp] theorem projection_sectionM (m : T.M) : T.projection (T.sectionM m) = m := by
  have h : T.sectionM m = T.combine 1 m := by apply Subtype.ext; simp [sectionM]
  rw [h, T.projection_combine]

@[simp] theorem projection_sectionU (u : T.U) : T.projection (T.sectionU u) = 1 := by
  have h : T.sectionU u = T.combine u 1 := by apply Subtype.ext; simp [sectionU]
  rw [h, T.projection_combine]

/-- The kernel of the projection is exactly `U`. -/
theorem projection_eq_one_iff (p : T.P) : T.projection p = 1 ↔ (p : G) ∈ T.U := by
  obtain ⟨⟨u, m⟩, rfl⟩ := T.combine_bijective.surjective p
  simp only [projection_combine, combine_val]
  constructor
  · rintro rfl
    simp
  · intro h
    have hm : (m : G) ∈ T.U := by
      simpa using T.U.mul_mem (T.U.inv_mem u.property) h
    have hmM : (m : G) ∈ T.M ⊓ T.U := ⟨m.property, hm⟩
    rw [T.intersection] at hmM
    exact Subtype.ext ((Subgroup.mem_bot).mp hmM)

end Triple

/-- A locally constant complex character of `U`, fixed by actual conjugation by `M`. -/
structure Character (T : Triple G) where
  /-- The character, with values in the nonzero complex numbers. -/
  theta : T.U →* ℂˣ
  /-- BZ77 1.5: a character is locally constant. -/
  locallyConstant : IsLocallyConstant (fun u : T.U => (theta u : ℂ))
  /-- `θ(m u m⁻¹) = θ(u)` for all `m ∈ M`, `u ∈ U`. -/
  invariant : Jacquet.Localization.IsInvariant T.U T.M T.normalizes theta

namespace Character

variable {T : Triple G} (χ : Character T)

@[simp] theorem theta_conjugate (m : T.M) (u : T.U) :
    χ.theta (T.conjugate m u) = χ.theta u :=
  χ.invariant m u

/-- Inflation `u*m ↦ θ(u)` to `P`, evaluated on the unique `U` component. -/
def inflation : T.P →* ℂˣ where
  toFun p := χ.theta (T.decomposition p).1
  map_one' := by
    have hd := T.decomposition_combine 1 1
    rw [T.combine_one_one] at hd
    simp [hd]
  map_mul' p q := by
    rw [T.decomposition_mul]
    simp

@[simp] theorem inflation_combine (u : T.U) (m : T.M) :
    χ.inflation (T.combine u m) = χ.theta u := by
  change χ.theta (T.decomposition (T.combine u m)).1 = _
  rw [T.decomposition_combine]

@[simp] theorem inflation_sectionM (m : T.M) : χ.inflation (T.sectionM m) = 1 := by
  have h : T.sectionM m = T.combine 1 m := by apply Subtype.ext; simp
  rw [h, χ.inflation_combine, map_one]

@[simp] theorem inflation_sectionU (u : T.U) : χ.inflation (T.sectionU u) = χ.theta u := by
  have h : T.sectionU u = T.combine u 1 := by apply Subtype.ext; simp
  rw [h, χ.inflation_combine]

/-- The covariance scalar `u*m ↦ θ(u) ν(m)` for a scalar character `ν` of `M`. -/
def covarianceCharacter (ν : T.M →* ℂˣ) : T.P →* ℂˣ :=
  χ.inflation * ν.comp T.projection

@[simp] theorem covarianceCharacter_combine (ν : T.M →* ℂˣ) (u : T.U) (m : T.M) :
    χ.covarianceCharacter ν (T.combine u m) = χ.theta u * ν m := by
  simp [covarianceCharacter]

variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The covariance representation `u*m ↦ θ(u) ν(m) ρ(m)` of `P`; no smoothness is assumed. -/
def covariance (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V) : Representation ℂ T.P V :=
  Langlands.twist (χ.covarianceCharacter ν) (ρ.comp T.projection)

@[simp] theorem covariance_apply (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (p : T.P) (v : V) :
    χ.covariance ν ρ p v =
      ((χ.inflation p : ℂ) * (ν (T.projection p) : ℂ)) • ρ (T.projection p) v := rfl

@[simp] theorem covariance_combine (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (u : T.U) (m : T.M) (v : V) :
    χ.covariance ν ρ (T.combine u m) v = ((χ.theta u : ℂ) * (ν m : ℂ)) • ρ m v := by
  simp

/-- An actual `M`-intertwiner is a `P`-intertwiner of covariance representations. -/
def covarianceMap (ν : T.M →* ℂˣ) {ρ : Representation ℂ T.M V}
    {σ : Representation ℂ T.M W} (f : ρ.IntertwiningMap σ) :
    (χ.covariance ν ρ).IntertwiningMap (χ.covariance ν σ) :=
  Langlands.twistIntertwining (χ.covarianceCharacter ν)
    { toLinearMap := f.toLinearMap
      isIntertwining' p := f.isIntertwining' (T.projection p) }

@[simp] theorem covarianceMap_apply (ν : T.M →* ℂˣ) {ρ : Representation ℂ T.M V}
    {σ : Representation ℂ T.M W} (f : ρ.IntertwiningMap σ) (v : V) :
    χ.covarianceMap ν f v = f v := rfl

/-- Covariance as a functor between Mathlib representation categories. -/
def covarianceFunctor (ν : T.M →* ℂˣ) : Rep.{uV} ℂ T.M ⥤ Rep.{uV} ℂ T.P where
  obj A := Rep.of (χ.covariance ν A.ρ)
  map f := Rep.ofHom (χ.covarianceMap ν f.hom)
  map_id _ := by ext v; rfl
  map_comp _ _ := by ext v; rfl

section Induction

variable [IsTopologicalGroup G]

/-- Covariant smooth functions `G → V`; the carrier universe is `max uG uV`. -/
abbrev SmoothFunctions (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V) : Type (max uG uV) :=
  Induction.SmoothFunctions T.P (χ.covariance ν ρ)

/-- Covariant smooth functions with compact support modulo the actual `P`. -/
abbrev CompactFunctions (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V) : Type (max uG uV) :=
  Induction.CompactFunctions T.P (χ.covariance ν ρ)

/-- Right translation on covariant smooth functions. -/
abbrev smoothAction (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V) :
    Representation ℂ G (χ.SmoothFunctions ν ρ) :=
  Induction.smoothInduced T.P (χ.covariance ν ρ)

/-- Right translation on covariant smooth functions with compact support modulo `P`. -/
abbrev compactAction (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V) :
    Representation ℂ G (χ.CompactFunctions ν ρ) :=
  Induction.compactInduced T.P (χ.covariance ν ρ)

/-- Evaluation of the underlying function of a covariant smooth function. -/
abbrev eval (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (f : χ.SmoothFunctions ν ρ) (g : G) : V :=
  Induction.eval T.P (χ.covariance ν ρ) f g

omit [IsTopologicalGroup G] in
/-- Covariance of an induced function at `u*m*g`, for the scalar character `ν`. -/
theorem eval_covariance (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (f : χ.SmoothFunctions ν ρ) (u : T.U) (m : T.M) (g : G) :
    χ.eval ν ρ f ((u : G) * m * g) =
      ((χ.theta u : ℂ) * (ν m : ℂ)) • ρ m (χ.eval ν ρ f g) := by
  have h := f.1.property (T.combine u m) g
  simpa [eval, Induction.eval] using h

@[simp] theorem eval_smoothAction (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (g x : G) (f : χ.SmoothFunctions ν ρ) :
    χ.eval ν ρ (χ.smoothAction ν ρ g f) x = χ.eval ν ρ f (x * g) := rfl

@[simp] theorem eval_compactAction (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (g x : G) (f : χ.CompactFunctions ν ρ) :
    χ.eval ν ρ (χ.compactAction ν ρ g f).1 x = χ.eval ν ρ f.1 (x * g) := rfl

/-- The compact-support condition is compactness of the nonzero support in `P\G`. -/
theorem compact_support (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (f : χ.CompactFunctions ν ρ) :
    IsCompact (Induction.quotientSupport T.P (χ.eval ν ρ f.1)) :=
  f.property

/-- An induced function from the source's `u*m*g` covariance and one open right stabilizer. -/
def smoothFunctionOf (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V) (f : G → V)
    (hcov : ∀ (u : T.U) (m : T.M) (g : G),
      f ((u : G) * m * g) = ((χ.theta u : ℂ) * (ν m : ℂ)) • ρ m (f g))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (g : G), f (g * (k : G)) = f g) :
    χ.SmoothFunctions ν ρ :=
  Induction.smoothFunctionOf T.P (χ.covariance ν ρ) f (by
    intro p g
    obtain ⟨⟨u, m⟩, rfl⟩ := T.combine_bijective.surjective p
    simpa using hcov u m g) K hK

omit [IsTopologicalGroup G] in
@[simp] theorem eval_smoothFunctionOf (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V)
    (f : G → V)
    (hcov : ∀ (u : T.U) (m : T.M) (g : G),
      f ((u : G) * m * g) = ((χ.theta u : ℂ) * (ν m : ℂ)) • ρ m (f g))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (g : G), f (g * (k : G)) = f g) (g : G) :
    χ.eval ν ρ (χ.smoothFunctionOf ν ρ f hcov K hK) g = f g := rfl

/-- The compact constructor adds exactly compactness of the support modulo `P`. -/
def compactFunctionOf (ν : T.M →* ℂˣ) (ρ : Representation ℂ T.M V) (f : G → V)
    (hcov : ∀ (u : T.U) (m : T.M) (g : G),
      f ((u : G) * m * g) = ((χ.theta u : ℂ) * (ν m : ℂ)) • ρ m (f g))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (g : G), f (g * (k : G)) = f g)
    (hc : IsCompact (Induction.quotientSupport T.P f)) :
    χ.CompactFunctions ν ρ :=
  ⟨χ.smoothFunctionOf ν ρ f hcov K hK, hc⟩

/-- The map of smooth induced functions given by postcomposition with an `M`-intertwiner. -/
abbrev smoothMap (ν : T.M →* ℂˣ) {ρ : Representation ℂ T.M V}
    {σ : Representation ℂ T.M W} (f : ρ.IntertwiningMap σ) :
    (χ.smoothAction ν ρ).IntertwiningMap (χ.smoothAction ν σ) :=
  Induction.smoothInducedMap T.P (χ.covarianceMap ν f)

/-- The map of compactly induced functions given by postcomposition with an `M`-intertwiner. -/
abbrev compactMap (ν : T.M →* ℂˣ) {ρ : Representation ℂ T.M V}
    {σ : Representation ℂ T.M W} (f : ρ.IntertwiningMap σ) :
    (χ.compactAction ν ρ).IntertwiningMap (χ.compactAction ν σ) :=
  Induction.compactInducedMap T.P (χ.covarianceMap ν f)

@[simp] theorem eval_smoothMap (ν : T.M →* ℂˣ) {ρ : Representation ℂ T.M V}
    {σ : Representation ℂ T.M W} (f : ρ.IntertwiningMap σ)
    (s : χ.SmoothFunctions ν ρ) (g : G) :
    χ.eval ν σ (χ.smoothMap ν f s) g = f (χ.eval ν ρ s g) := rfl

@[simp] theorem eval_compactMap (ν : T.M →* ℂˣ) {ρ : Representation ℂ T.M V}
    {σ : Representation ℂ T.M W} (f : ρ.IntertwiningMap σ)
    (s : χ.CompactFunctions ν ρ) (g : G) :
    χ.eval ν σ (χ.compactMap ν f s).1 g = f (χ.eval ν ρ s.1 g) := rfl

end Induction

end Character

/-! ### The actual Haar modulus of conjugation on `U` -/

namespace Triple

section Modulus

variable [LocallyCompactSpace G] [IsTopologicalGroup G] (T : Triple G)

/-- `mod_U` on `M`: the published positive Haar modulus of `u ↦ m u m⁻¹` on the closed `U`. -/
def modulus : T.M →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter T.U T.closed_U T.M T.normalizes

/-- `mod_U^{1/2}` on `M`, the positive square root embedded in `ℂˣ`. -/
def halfModulus : T.M →* ℂˣ :=
  HaarModulus.closedHalfCharacter T.U T.closed_U T.M T.normalizes

/-- `mod_U^{-1/2}` on `M`. -/
def inverseHalfModulus : T.M →* ℂˣ :=
  HaarModulus.closedInverseHalfCharacter T.U T.closed_U T.M T.normalizes

theorem halfModulus_apply (m : T.M) :
    (T.halfModulus m : ℂ) = ((NNReal.sqrt (T.modulus m : ℝ≥0) : ℝ) : ℂ) := rfl

theorem inverseHalfModulus_apply (m : T.M) :
    (T.inverseHalfModulus m : ℂ) = (((NNReal.sqrt (T.modulus m : ℝ≥0) : ℝ) : ℂ))⁻¹ :=
  Jacquet.inverseHalfCharacter_apply _ _

theorem inverseHalfModulus_eq_inv : T.inverseHalfModulus = T.halfModulus⁻¹ := rfl

theorem halfModulus_sq (m : T.M) :
    T.halfModulus m ^ 2 = Jacquet.complexCharacter T.modulus m := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, halfModulus_apply, Jacquet.complexCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

/-- BZ77 1.7 orientation: `∫ f(m⁻¹ u m) dμ(u) = mod_U(m) ∫ f dμ` for a Haar measure on `U`. -/
theorem integral_conjugate_inv [MeasurableSpace T.U] [BorelSpace T.U] (m : T.M)
    (μ : Measure T.U) [μ.IsHaarMeasure] [μ.Regular]
    {E : Type uV} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : T.U → E) :
    (∫ u, f (T.conjugate m⁻¹ u) ∂μ) = (T.modulus m : ℝ≥0) • ∫ u, f u ∂μ := by
  let := T.closed_U.locallyCompactSpace
  obtain ⟨h⟩ := ‹BorelSpace T.U›
  subst h
  have hconj : ∀ u : T.U, T.conjugate m⁻¹ u =
      (HaarModulus.normalizerConj T.U ⟨m, T.normalizes m.property⟩).symm u := by
    intro u
    apply Subtype.ext
    simp [Jacquet.Localization.conjugate]
  simp only [hconj]
  exact HaarModulus.integral_normalizerConj_symm T.U _ μ f

end Modulus

section Openness

variable [LocallyCompactSpace G] [NonarchimedeanGroup G] (T : Triple G)

theorem isOpen_ker_halfModulus : IsOpen (T.halfModulus.ker : Set T.M) :=
  HaarModulus.isOpen_ker_closedHalfCharacter T.U T.closed_U T.M T.normalizes

theorem isOpen_ker_inverseHalfModulus : IsOpen (T.inverseHalfModulus.ker : Set T.M) :=
  HaarModulus.isOpen_ker_closedInverseHalfCharacter T.U T.closed_U T.M T.normalizes

end Openness

end Triple

/-! ### Normalized induction `I_{U,θ}` and compact induction `i_{U,θ}` -/

namespace Character

variable {T : Triple G} (χ : Character T)
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section NormalizedInduction

variable [LocallyCompactSpace G] [IsTopologicalGroup G]

/-- The BZ77 1.8(a)(1) representation `u*m ↦ θ(u) mod_U^{1/2}(m) ρ(m)` of `P`. -/
abbrev inducingRepresentation (ρ : Representation ℂ T.M V) : Representation ℂ T.P V :=
  χ.covariance T.halfModulus ρ

theorem inducingRepresentation_combine (ρ : Representation ℂ T.M V) (u : T.U) (m : T.M)
    (v : V) :
    χ.inducingRepresentation ρ (T.combine u m) v =
      ((χ.theta u : ℂ) * (T.halfModulus m : ℂ)) • ρ m v :=
  χ.covariance_combine _ ρ u m v

/-- Normalized smooth induction `I_{U,θ}`: right translation on smooth functions
`f(umg) = θ(u) mod_U^{1/2}(m) ρ(m) f(g)`. -/
def normalizedInductionFunctor :
    SmoothRep.{0, uG, uV} ℂ T.M ⥤ SmoothRep.{0, uG, max uG uV} ℂ G :=
  SmoothRep.toRep ⋙ χ.covarianceFunctor T.halfModulus ⋙ Induction.smoothInductionFunctor T.P

/-- Normalized compact induction `i_{U,θ}`: the functions of `I_{U,θ}` with compact
support modulo `P`. -/
def normalizedCompactInductionFunctor :
    SmoothRep.{0, uG, uV} ℂ T.M ⥤ SmoothRep.{0, uG, max uG uV} ℂ G :=
  SmoothRep.toRep ⋙ χ.covarianceFunctor T.halfModulus ⋙ Induction.compactInductionFunctor T.P

theorem normalizedInductionFunctor_obj_representation (A : SmoothRep.{0, uG, uV} ℂ T.M) :
    (χ.normalizedInductionFunctor.obj A).representation =
      χ.smoothAction T.halfModulus A.representation := rfl

theorem normalizedCompactInductionFunctor_obj_representation (A : SmoothRep.{0, uG, uV} ℂ T.M) :
    (χ.normalizedCompactInductionFunctor.obj A).representation =
      χ.compactAction T.halfModulus A.representation := rfl

/-- The BZ77 1.8(a)(1) covariance of a normalized induced function. -/
theorem normalizedInductionFunctor_covariant (A : SmoothRep.{0, uG, uV} ℂ T.M)
    (f : χ.normalizedInductionFunctor.obj A) (u : T.U) (m : T.M) (g : G) :
    χ.eval T.halfModulus A.representation f ((u : G) * m * g) =
      ((χ.theta u : ℂ) * (T.halfModulus m : ℂ)) •
        A.representation m (χ.eval T.halfModulus A.representation f g) :=
  χ.eval_covariance _ A.representation f u m g

/-- Covariance under an arbitrary `p ∈ P`, through its unique decomposition. -/
theorem normalizedInductionFunctor_covariant_P (A : SmoothRep.{0, uG, uV} ℂ T.M)
    (f : χ.normalizedInductionFunctor.obj A) (p : T.P) (g : G) :
    χ.eval T.halfModulus A.representation f ((p : G) * g) =
      ((χ.inflation p : ℂ) * (T.halfModulus (T.projection p) : ℂ)) •
        A.representation (T.projection p) (χ.eval T.halfModulus A.representation f g) :=
  f.1.property p g

/-- The BZ77 1.8(a)(2) condition: one open subgroup fixes the function under right translation. -/
theorem normalizedInductionFunctor_exists_openSubgroup (A : SmoothRep.{0, uG, uV} ℂ T.M)
    (f : χ.normalizedInductionFunctor.obj A) :
    ∃ K : OpenSubgroup G, ∀ (k : K) (g : G),
      χ.eval T.halfModulus A.representation f (g * (k : G)) =
        χ.eval T.halfModulus A.representation f g := by
  obtain ⟨K, hK⟩ := f.property
  exact ⟨K, fun k g => congrArg (fun F => F.1 g) (hK k)⟩

/-- `G` acts on `I_{U,θ}` by right translation. -/
theorem normalizedInductionFunctor_obj_apply (A : SmoothRep.{0, uG, uV} ℂ T.M) (g : G)
    (f : χ.normalizedInductionFunctor.obj A) (x : G) :
    χ.eval T.halfModulus A.representation
        ((χ.normalizedInductionFunctor.obj A).representation g f) x =
      χ.eval T.halfModulus A.representation f (x * g) := rfl

/-- `I_{U,θ}` sends an intertwiner to postcomposition. -/
theorem normalizedInductionFunctor_map_eval {A B : SmoothRep.{0, uG, uV} ℂ T.M} (φ : A ⟶ B)
    (f : χ.normalizedInductionFunctor.obj A) (x : G) :
    χ.eval T.halfModulus B.representation
        (SmoothRep.hom (χ.normalizedInductionFunctor.map φ) f) x =
      SmoothRep.hom φ (χ.eval T.halfModulus A.representation f x) := rfl

theorem normalizedInductionFunctor_hom_map {A B : SmoothRep.{0, uG, uV} ℂ T.M} (φ : A ⟶ B) :
    SmoothRep.hom (χ.normalizedInductionFunctor.map φ) =
      χ.smoothMap T.halfModulus (SmoothRep.hom φ) := rfl

/-- An element of `I_{U,θ}(ρ)` from its BZ77 1.8(a) conditions (1) and (2). -/
def normalizedFunctionOf (A : SmoothRep.{0, uG, uV} ℂ T.M) (f : G → A)
    (hcov : ∀ (u : T.U) (m : T.M) (g : G),
      f ((u : G) * m * g) = ((χ.theta u : ℂ) * (T.halfModulus m : ℂ)) • A.representation m (f g))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (g : G), f (g * (k : G)) = f g) :
    χ.normalizedInductionFunctor.obj A :=
  χ.smoothFunctionOf T.halfModulus A.representation f hcov K hK

@[simp] theorem eval_normalizedFunctionOf (A : SmoothRep.{0, uG, uV} ℂ T.M) (f : G → A)
    (hcov : ∀ (u : T.U) (m : T.M) (g : G),
      f ((u : G) * m * g) = ((χ.theta u : ℂ) * (T.halfModulus m : ℂ)) • A.representation m (f g))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (g : G), f (g * (k : G)) = f g) (g : G) :
    χ.eval T.halfModulus A.representation (χ.normalizedFunctionOf A f hcov K hK) g = f g := rfl

/-- Elements of `i_{U,θ}(ρ)` are elements of `I_{U,θ}(ρ)`. -/
abbrev compactToInduced (A : SmoothRep.{0, uG, uV} ℂ T.M)
    (f : χ.normalizedCompactInductionFunctor.obj A) : χ.normalizedInductionFunctor.obj A := f.1

/-- The support of an element of `i_{U,θ}` is compact modulo `P`. -/
theorem normalizedCompactInductionFunctor_isCompact (A : SmoothRep.{0, uG, uV} ℂ T.M)
    (f : χ.normalizedCompactInductionFunctor.obj A) :
    IsCompact (Induction.quotientSupport T.P
      (χ.eval T.halfModulus A.representation (χ.compactToInduced A f))) :=
  f.property

/-- `G` acts on `i_{U,θ}` by right translation. -/
theorem normalizedCompactInductionFunctor_obj_apply (A : SmoothRep.{0, uG, uV} ℂ T.M) (g : G)
    (f : χ.normalizedCompactInductionFunctor.obj A) (x : G) :
    χ.eval T.halfModulus A.representation
        (χ.compactToInduced A ((χ.normalizedCompactInductionFunctor.obj A).representation g f)) x =
      χ.eval T.halfModulus A.representation (χ.compactToInduced A f) (x * g) := rfl

/-- `i_{U,θ}` sends an intertwiner to postcomposition. -/
theorem normalizedCompactInductionFunctor_map_eval {A B : SmoothRep.{0, uG, uV} ℂ T.M}
    (φ : A ⟶ B) (f : χ.normalizedCompactInductionFunctor.obj A) (x : G) :
    χ.eval T.halfModulus B.representation
        (χ.compactToInduced B (SmoothRep.hom (χ.normalizedCompactInductionFunctor.map φ) f)) x =
      SmoothRep.hom φ (χ.eval T.halfModulus A.representation (χ.compactToInduced A f) x) := rfl

theorem normalizedCompactInductionFunctor_hom_map {A B : SmoothRep.{0, uG, uV} ℂ T.M}
    (φ : A ⟶ B) :
    SmoothRep.hom (χ.normalizedCompactInductionFunctor.map φ) =
      χ.compactMap T.halfModulus (SmoothRep.hom φ) := rfl

/-- An element of `i_{U,θ}(ρ)` from (1), (2) and compact support modulo `P`. -/
def normalizedCompactFunctionOf (A : SmoothRep.{0, uG, uV} ℂ T.M) (f : G → A)
    (hcov : ∀ (u : T.U) (m : T.M) (g : G),
      f ((u : G) * m * g) = ((χ.theta u : ℂ) * (T.halfModulus m : ℂ)) • A.representation m (f g))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (g : G), f (g * (k : G)) = f g)
    (hc : IsCompact (Induction.quotientSupport T.P f)) :
    χ.normalizedCompactInductionFunctor.obj A :=
  χ.compactFunctionOf T.halfModulus A.representation f hcov K hK hc

/-- The inclusion `i_{U,θ}(ρ) ⊂ I_{U,θ}(ρ)` as a morphism of smooth representations. -/
def compactInclusion (A : SmoothRep.{0, uG, uV} ℂ T.M) :
    χ.normalizedCompactInductionFunctor.obj A ⟶ χ.normalizedInductionFunctor.obj A :=
  SmoothRep.ofHom (Induction.compactInclusion T.P (χ.inducingRepresentation A.representation))

@[simp] theorem compactInclusion_apply (A : SmoothRep.{0, uG, uV} ℂ T.M)
    (f : χ.normalizedCompactInductionFunctor.obj A) :
    SmoothRep.hom (χ.compactInclusion A) f = χ.compactToInduced A f := rfl

end NormalizedInduction

/-! ### Normalized localization `r_{U,θ}` -/

section NormalizedLocalization

variable [LocallyCompactSpace G] [IsTopologicalGroup G]

/-- The normalized `θ`-localization of any representation of `G`:
`m · (ξ + E(U,θ)) = mod_U^{-1/2}(m) (π(m) ξ + E(U,θ))`. -/
def localizedAction (π : Representation ℂ G V) :
    Representation ℂ T.M (Jacquet.Localization.Coinvariants π T.U χ.theta) :=
  Langlands.twist T.inverseHalfModulus
    (Jacquet.Localization.action π T.U χ.theta T.M T.normalizes χ.invariant)

theorem localizedAction_mk (π : Representation ℂ G V) (m : T.M) (v : V) :
    χ.localizedAction π m (Jacquet.Localization.mk π T.U χ.theta v) =
      (T.inverseHalfModulus m : ℂ) • Jacquet.Localization.mk π T.U χ.theta (π m v) := rfl

omit [LocallyCompactSpace G] [IsTopologicalGroup G] in
/-- The generating relation of the quotient: `π(u) ξ ≡ θ(u) ξ`. -/
theorem localization_mk_apply (π : Representation ℂ G V) (u : T.U) (v : V) :
    Jacquet.Localization.mk π T.U χ.theta (π u v) =
      (χ.theta u : ℂ) • Jacquet.Localization.mk π T.U χ.theta v :=
  Jacquet.Localization.mk_apply_subgroup π T.U χ.theta u v

omit [LocallyCompactSpace G] [IsTopologicalGroup G] in
/-- The kernel of the quotient map is the span `E(U,θ)` of all `π(u) ξ - θ(u) ξ`. -/
theorem localization_ker_mk (π : Representation ℂ G V) :
    LinearMap.ker (Jacquet.Localization.mk π T.U χ.theta) =
      Submodule.span ℂ (Set.range fun uv : T.U × V => π uv.1 uv.2 - (χ.theta uv.1 : ℂ) • uv.2) :=
  Jacquet.Localization.ker_mk π T.U χ.theta

/-- The map of normalized localizations induced by a `G`-intertwiner, `[ξ] ↦ [f ξ]`. -/
def localizedMap {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : π.IntertwiningMap σ) :
    (χ.localizedAction π).IntertwiningMap (χ.localizedAction σ) :=
  Langlands.twistIntertwining T.inverseHalfModulus
    (Jacquet.Localization.map T.U χ.theta T.M T.normalizes χ.invariant f)

theorem localizedMap_mk {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : π.IntertwiningMap σ) (v : V) :
    χ.localizedMap f (Jacquet.Localization.mk π T.U χ.theta v) =
      Jacquet.Localization.mk σ T.U χ.theta (f v) := rfl

end NormalizedLocalization

section LocalizationFunctor

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Normalized `θ`-localization `r_{U,θ}` on the canonical smooth categories. -/
def normalizedLocalizationFunctor : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ T.M :=
  Jacquet.Localization.smoothFunctor T.U χ.theta T.M T.normalizes χ.invariant ⋙
    SmoothRep.twistFunctor T.inverseHalfModulus T.isOpen_ker_inverseHalfModulus

theorem normalizedLocalizationFunctor_obj_representation (A : SmoothRep.{0, uG, uV} ℂ G) :
    (χ.normalizedLocalizationFunctor.obj A).representation =
      χ.localizedAction A.representation := rfl

/-- The carrier of `r_{U,θ}(π)` is the actual quotient `E / E(U,θ)`. -/
theorem normalizedLocalizationFunctor_obj_carrier (A : SmoothRep.{0, uG, uV} ℂ G) :
    (χ.normalizedLocalizationFunctor.obj A : Type uV) =
      Jacquet.Localization.Coinvariants A.representation T.U χ.theta := rfl

theorem normalizedLocalizationFunctor_obj_apply (A : SmoothRep.{0, uG, uV} ℂ G) (m : T.M)
    (v : A) :
    (χ.normalizedLocalizationFunctor.obj A).representation m
        (Jacquet.Localization.mk A.representation T.U χ.theta v) =
      (T.inverseHalfModulus m : ℂ) •
        Jacquet.Localization.mk A.representation T.U χ.theta (A.representation m v) := rfl

theorem normalizedLocalizationFunctor_map_mk {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B)
    (v : A) :
    SmoothRep.hom (χ.normalizedLocalizationFunctor.map f)
        (Jacquet.Localization.mk A.representation T.U χ.theta v) =
      Jacquet.Localization.mk B.representation T.U χ.theta (SmoothRep.hom f v) := rfl

theorem normalizedLocalizationFunctor_hom_map {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) :
    SmoothRep.hom (χ.normalizedLocalizationFunctor.map f) =
      χ.localizedMap (SmoothRep.hom f) := rfl

end LocalizationFunctor

end Character

end Langlands.ClosedSemidirect
