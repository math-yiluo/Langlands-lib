import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.Representation.Whittaker.CharacterChange
import Langlands.Representation.Filtration.InvariantBilinear
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# Character-change and determinant-twist adapters for compact induction

Left translation by an element normalizing the inducing subgroup, and
multiplication by a character of the ambient group that is trivial on the
inducing subgroup, as actual equivalences of compactly induced representations.
They are specialized to the actual compact mirabolic model `mirabolicCompactInduced`.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-! ## Left translation by a normalizing element -/

section LeftTranslation

variable (P : Subgroup G)

/-- Left multiplication by an element of the normalizer, on `P \ G`. -/
def quotientLeft (d : G) (hd : d ∈ Subgroup.normalizer (P : Set G)) :
    LeftQuotient P → LeftQuotient P :=
  Quotient.map' (fun x => d * x) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have h' := (Subgroup.mem_normalizer_iff.mp hd (y * x⁻¹)).mp h
    simpa [mul_inv_rev, mul_assoc] using h')

theorem continuous_quotientLeft (d : G) (hd : d ∈ Subgroup.normalizer (P : Set G)) :
    Continuous (quotientLeft P d hd) :=
  (continuous_const.mul continuous_id).quotient_map' _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientLeft_mk (d : G) (hd : d ∈ Subgroup.normalizer (P : Set G)) (x : G) :
    quotientLeft P d hd (quotientMap P x) = quotientMap P (d * x) := rfl

/-- Conjugation by a normalizing element, as a map of `P`. -/
def normalizerConj (d : G) (hd : d ∈ Subgroup.normalizer (P : Set G)) (p : P) : P :=
  ⟨d * p * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd p).mp p.property⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem normalizerConj_val (d : G) (hd : d ∈ Subgroup.normalizer (P : Set G)) (p : P) :
    (normalizerConj P d hd p : G) = d * p * d⁻¹ := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The projected support of the left translate by `d`. -/
private theorem leftTranslate_support (d : G) (hd : d⁻¹ ∈ Subgroup.normalizer (P : Set G))
    (f : G → V) :
    quotientSupport P (fun g => f (d * g)) =
      quotientLeft P d⁻¹ hd '' quotientSupport P f := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨quotientMap P (d * x), ⟨d * x, hx, rfl⟩, ?_⟩
    rw [quotientLeft_mk, inv_mul_cancel_left]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨d⁻¹ * y, ?_, rfl⟩
    simpa [mul_inv_cancel_left] using hy

/-- Left translation `f ↦ (g ↦ f (d * g))` from compact induction of `σ` to
compact induction of `σ'`, when `d` normalizes `P` and `σ'` is `σ` composed with
conjugation by `d`. -/
def compactLeftTranslate (σ σ' : Representation R P V) (d : G)
    (hd : d ∈ Subgroup.normalizer (P : Set G)) (hd' : d⁻¹ ∈ Subgroup.normalizer (P : Set G))
    (hσ : ∀ p : P, σ' p = σ (normalizerConj P d hd p)) :
    (compactInduced P σ).IntertwiningMap (compactInduced P σ') where
  toFun f := ⟨⟨⟨fun g => f.val.val.val (d * g), by
      intro p g
      change f.val.val.val (d * ((p : G) * g)) = σ' p (f.val.val.val (d * g))
      have h := f.val.val.property (normalizerConj P d hd p) (d * g)
      rw [hσ]
      convert h using 2
      simp [mul_assoc]⟩, by
      obtain ⟨K, hK⟩ := f.val.property
      refine ⟨K, ?_⟩
      intro k
      apply Subtype.ext
      funext g
      have h : f.val.val.val (d * g * k) = f.val.val.val (d * g) :=
        congrArg (fun φ : EquivariantFunctions P σ => φ.1 (d * g)) (hK k)
      change f.val.val.val (d * (g * k)) = f.val.val.val (d * g)
      rw [← mul_assoc]
      exact h⟩, by
      have hc : IsCompact (quotientSupport P (fun g => f.val.val.val (d * g))) := by
        rw [leftTranslate_support P d hd' f.val.val.val]
        exact f.property.image (continuous_quotientLeft P d⁻¹ hd')
      exact hc⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' h := by
    ext f x
    change f.val.val.val (d * x * h) = f.val.val.val (d * (x * h))
    rw [mul_assoc]

@[simp] theorem compactLeftTranslate_apply (σ σ' : Representation R P V) (d : G)
    (hd : d ∈ Subgroup.normalizer (P : Set G)) (hd' : d⁻¹ ∈ Subgroup.normalizer (P : Set G))
    (hσ : ∀ p : P, σ' p = σ (normalizerConj P d hd p)) (f : CompactFunctions P σ) (g : G) :
    (compactLeftTranslate P σ σ' d hd hd' hσ f).val.val.val g = f.val.val.val (d * g) := rfl

/-- Left translation by a normalizing element is an equivalence of compactly
induced representations; its inverse is left translation by `d⁻¹`. -/
def compactLeftTranslateEquiv (σ σ' : Representation R P V) (d : G)
    (hd : d ∈ Subgroup.normalizer (P : Set G)) (hd' : d⁻¹ ∈ Subgroup.normalizer (P : Set G))
    (hσ : ∀ p : P, σ' p = σ (normalizerConj P d hd p)) :
    (compactInduced P σ).Equiv (compactInduced P σ') :=
  let e := compactLeftTranslate P σ σ' d hd hd' hσ
  let e' := compactLeftTranslate P σ' σ d⁻¹ hd' (by simpa using hd) (by
    intro p
    rw [hσ]
    congr 1
    apply Subtype.ext
    simp [mul_assoc])
  Representation.Equiv.mk
    { e.toLinearMap with
      invFun := e'
      left_inv := fun f => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        funext g
        change f.val.val.val (d * (d⁻¹ * g)) = f.val.val.val g
        rw [mul_inv_cancel_left]
      right_inv := fun f => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        funext g
        change f.val.val.val (d⁻¹ * (d * g)) = f.val.val.val g
        rw [inv_mul_cancel_left] }
    (fun g => e.isIntertwining' g)

end LeftTranslation

/-! ## Multiplication by a character trivial on the inducing subgroup -/

section CharacterMultiply

variable (P : Subgroup G) (σ : Representation R P V)

/-- The kernel of a character with open kernel, as an open subgroup. -/
def kernelOpenSubgroup (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) : OpenSubgroup G :=
  ⟨χ.ker, hχ⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem characterMultiply_support (χ : G →* Rˣ) (f : G → V) :
    quotientSupport P (fun g => (χ g : R) • f g) = quotientSupport P f := by
  unfold quotientSupport
  congr 1
  ext g
  simp only [Function.mem_support, ne_eq]
  rw [(χ g).isUnit.smul_eq_zero]

/-- Pointwise multiplication `f ↦ (g ↦ χ g • f g)` by a character with open kernel that
is trivial on `P`, as a linear endomorphism of the compactly induced module. -/
def compactCharacterMultiply (χ : G →* Rˣ) (hP : ∀ p : P, χ p = 1)
    (hχ : IsOpen (χ.ker : Set G)) :
    CompactFunctions P σ →ₗ[R] CompactFunctions P σ where
  toFun f := ⟨⟨⟨fun g => (χ g : R) • f.val.val.val g, by
      intro p g
      have hf : f.val.val.val ((p : G) * g) = σ p (f.val.val.val g) :=
        f.val.val.property p g
      change (χ ((p : G) * g) : R) • f.val.val.val ((p : G) * g) =
        σ p ((χ g : R) • f.val.val.val g)
      rw [map_mul, hP p, one_mul, hf, LinearMap.map_smul]⟩, by
      obtain ⟨K, hK⟩ := f.val.property
      refine ⟨K ⊓ kernelOpenSubgroup χ hχ, fun k => ?_⟩
      apply Subtype.ext
      funext g
      have hk := OpenSubgroup.mem_inf.mp k.property
      have h : f.val.val.val (g * k) = f.val.val.val g :=
        congrArg (fun φ : EquivariantFunctions P σ => φ.1 g) (hK ⟨k, hk.1⟩)
      have hχk : χ k = 1 := hk.2
      change (χ (g * k) : R) • f.val.val.val (g * k) = (χ g : R) • f.val.val.val g
      rw [map_mul, hχk, mul_one, h]⟩, by
      change IsCompact (quotientSupport P (fun g => (χ g : R) • f.val.val.val g))
      rw [characterMultiply_support]
      exact f.property⟩
  map_add' f h := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext g
    exact smul_add _ _ _
  map_smul' a f := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext g
    exact smul_comm _ _ _

@[simp] theorem compactCharacterMultiply_apply (χ : G →* Rˣ) (hP : ∀ p : P, χ p = 1)
    (hχ : IsOpen (χ.ker : Set G)) (f : CompactFunctions P σ) (g : G) :
    (compactCharacterMultiply P σ χ hP hχ f).val.val.val g = (χ g : R) • f.val.val.val g :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem inv_trivial (χ : G →* Rˣ) (hP : ∀ p : P, χ p = 1) (p : P) :
    χ⁻¹ p = 1 := by
  rw [MonoidHom.inv_apply, hP p, inv_one]

omit [IsTopologicalGroup G] in
private theorem isOpen_ker_inv (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsOpen ((χ⁻¹).ker : Set G) := by
  have h : ((χ⁻¹).ker : Set G) = χ.ker := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  rw [h]
  exact hχ

/-- Multiplication by a character `χ` with open kernel that is trivial on `P` identifies
the `χ`-twist of compact induction with compact induction itself. It preserves
covariance, local constancy and the projected support; its inverse multiplies by `χ⁻¹`. -/
def compactCharacterMultiplyEquiv (χ : G →* Rˣ) (hP : ∀ p : P, χ p = 1)
    (hχ : IsOpen (χ.ker : Set G)) :
    (twist χ (compactInduced P σ)).Equiv (compactInduced P σ) :=
  Representation.Equiv.mk
    { compactCharacterMultiply P σ χ hP hχ with
      invFun := compactCharacterMultiply P σ χ⁻¹ (inv_trivial P χ hP) (isOpen_ker_inv χ hχ)
      left_inv := fun f => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        funext g
        change ((χ⁻¹ g : Rˣ) : R) • (χ g : R) • f.val.val.val g = f.val.val.val g
        rw [smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
      right_inv := fun f => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        funext g
        change (χ g : R) • ((χ⁻¹ g : Rˣ) : R) • f.val.val.val g = f.val.val.val g
        rw [smul_smul, MonoidHom.inv_apply, Units.mul_inv, one_smul] }
    (fun h => by
      ext f x
      change (χ x : R) • ((χ h : R) • f.val.val.val (x * h)) =
        (χ (x * h) : R) • f.val.val.val (x * h)
      rw [smul_smul, map_mul, Units.val_mul])

@[simp] theorem compactCharacterMultiplyEquiv_apply (χ : G →* Rˣ) (hP : ∀ p : P, χ p = 1)
    (hχ : IsOpen (χ.ker : Set G)) (f : CompactFunctions P σ) (g : G) :
    (compactCharacterMultiplyEquiv P σ χ hP hχ f).val.val.val g =
      (χ g : R) • f.val.val.val g :=
  rfl

end CharacterMultiply

end Langlands.Induction

/-! ## Transport of covariant bilinear forms -/

namespace Langlands.InvariantBilinear

universe uK uH uX uY uZ

variable {k : Type uK} [Field k] {H : Type uH} [Group H]
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
variable [AddCommGroup Z] [Module k Z]

/-- Twisting the first argument by `χ` divides the simultaneous covariance by `χ`.
The underlying bilinear map is unchanged. -/
def twistLeftEquiv (χ : H →* kˣ) (ρ : Representation k H X) (σ : Representation k H Y)
    (κ κ' : H → k) (h : ∀ g, κ g = (χ g : k) * κ' g) :
    forms (twist χ ρ) σ κ ≃ₗ[k] forms ρ σ κ' where
  toFun B := ⟨B.val, fun g v w => by
    have hB : B.val ((χ g : k) • ρ g v) (σ g w) = κ g * B.val v w := B.property g v w
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, h, mul_assoc] at hB
    exact mul_left_cancel₀ (χ g).ne_zero hB⟩
  invFun B := ⟨B.val, fun g v w => by
    change B.val ((χ g : k) • ρ g v) (σ g w) = κ g * B.val v w
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, B.property g v w, h,
      mul_assoc]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equivalence in the second argument preserves the full form space. -/
def equivRight (ρ : Representation k H X) {σ : Representation k H Y}
    {τ : Representation k H Z} (χ : H → k) (e : σ.Equiv τ) :
    forms ρ σ χ ≃ₗ[k] forms ρ τ χ :=
  (flipEquiv ρ σ χ).trans ((equivLeft ρ χ e).trans (flipEquiv τ ρ χ))

end Langlands.InvariantBilinear

namespace Langlands.Induction

universe uK uG' uV' uW'

variable {k : Type uK} [Field k] {G : Type uG'} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
variable {V : Type uV'} {W : Type uW'} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Forms on compact induction of `P`, with covariance `κ = χ κ'`, are the forms with
covariance `κ'`, when `χ` has open kernel and is trivial on `P`. -/
def formsCharacterShift (P : Subgroup G) (σ : Representation k P V)
    (σ' : Representation k G W) (χ : G →* kˣ) (hP : ∀ p : P, χ p = 1)
    (hχ : IsOpen (χ.ker : Set G)) (κ κ' : G → k) (h : ∀ g, κ g = (χ g : k) * κ' g) :
    InvariantBilinear.forms (compactInduced P σ) σ' κ ≃ₗ[k]
      InvariantBilinear.forms (compactInduced P σ) σ' κ' :=
  (InvariantBilinear.equivLeft σ' κ (compactCharacterMultiplyEquiv P σ χ hP hχ).symm).trans
    (InvariantBilinear.twistLeftEquiv χ (compactInduced P σ) σ' κ κ' h)

end Langlands.Induction

/-! ## The actual compact mirabolic model -/

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis RankinSelberg

universe uF uW

variable {F : Type uF} [Field F]

/-- The character-change element `d_a = diag(a^n, …, a, 1)` lies in the mirabolic group. -/
def mirabolicCharacterChangeElement (a : Fˣ) (n : ℕ) : mirabolic n F :=
  ⟨characterChangeElement a n, by
    intro j
    rw [characterChangeElement_val]
    by_cases hj : j = Fin.last n
    · subst hj
      simp
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
      simp [hj]⟩

@[simp] theorem mirabolicCharacterChangeElement_val (a : Fˣ) (n : ℕ) :
    (mirabolicCharacterChangeElement a n : Langlands.GeneralLinear (n + 1) F) =
      characterChangeElement a n := rfl

theorem mirabolicCharacterChangeElement_inv (a : Fˣ) (n : ℕ) :
    (mirabolicCharacterChangeElement a n)⁻¹ = mirabolicCharacterChangeElement a⁻¹ n :=
  Subtype.ext (characterChangeElement_inv a n)

private theorem characterChange_conj_mem (a : Fˣ) (n : ℕ) {h : mirabolic n F}
    (hh : h ∈ Mirabolic.upperUnipotent n F) :
    mirabolicCharacterChangeElement a n * h * (mirabolicCharacterChangeElement a n)⁻¹ ∈
      Mirabolic.upperUnipotent n F :=
  (characterChangeConj a n ⟨h.val, hh⟩).property

/-- `d_a` normalizes the actual upper-unipotent subgroup of the mirabolic group. -/
theorem mirabolicCharacterChangeElement_mem_normalizer (a : Fˣ) (n : ℕ) :
    mirabolicCharacterChangeElement a n ∈
      Subgroup.normalizer (Mirabolic.upperUnipotent n F : Set (mirabolic n F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨characterChange_conj_mem a n, fun hh => ?_⟩
  have h' := characterChange_conj_mem a⁻¹ n hh
  simpa [mul_assoc, ← mirabolicCharacterChangeElement_inv] using h'

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Conjugation by `d_a` carries the standard mirabolic character of `ψ` to that of
`ψ.scale a`. -/
theorem mirabolicCharacter_characterChange (ψ : UnitaryAdditiveCharacter F) (a : Fˣ)
    (n : ℕ) (p : Mirabolic.upperUnipotent n F) :
    mirabolicCharacter ψ n (Induction.normalizerConj _ (mirabolicCharacterChangeElement a n)
        (mirabolicCharacterChangeElement_mem_normalizer a n) p) =
      mirabolicCharacter (ψ.scale a) n p := by
  rw [mirabolicCharacter_apply, mirabolicCharacter_apply,
    ← standardCharacter_characterChangeConj]
  rfl

/-- Character change on the actual compact mirabolic model (BZ76 §5.6): left
translation `f ↦ (g ↦ f (d_a * g))` is an equivariant linear equivalence from the
model of `ψ` to the model of `x ↦ ψ (a * x)`. -/
def mirabolicCharacterChangeEquiv (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (n : ℕ) :
    (mirabolicCompactInduced ψ n).Equiv (mirabolicCompactInduced (ψ.scale a) n) :=
  Induction.compactLeftTranslateEquiv _ _ _ (mirabolicCharacterChangeElement a n)
    (mirabolicCharacterChangeElement_mem_normalizer a n)
    (by
      rw [mirabolicCharacterChangeElement_inv]
      exact mirabolicCharacterChangeElement_mem_normalizer a⁻¹ n)
    (fun p => LinearMap.ext fun z => by
      simp only [mirabolicCharacterRepresentation_apply,
        mirabolicCharacter_characterChange])

@[simp] theorem mirabolicCharacterChangeEquiv_apply (ψ : UnitaryAdditiveCharacter F)
    (a : Fˣ) (n : ℕ) (f : MirabolicCompactFunctions ψ n) (g : mirabolic n F) :
    (mirabolicCharacterChangeEquiv ψ a n f).val.val.val g =
      f.val.val.val (mirabolicCharacterChangeElement a n * g) := rfl

/-- The determinant character `g ↦ |det g|^c` restricted to the mirabolic group. -/
def mirabolicDeterminantCharacter (abv : AbsoluteValue F ℝ) (n : ℕ) (c : ℂ) :
    mirabolic n F →* ℂˣ :=
  (Shahidi.determinantPower abv (n + 1) c).comp (mirabolic n F).subtype

omit [TopologicalSpace F] [IsTopologicalRing F] in
@[simp] theorem mirabolicDeterminantCharacter_apply (abv : AbsoluteValue F ℝ) (n : ℕ)
    (c : ℂ) (g : mirabolic n F) :
    (mirabolicDeterminantCharacter abv n c g : ℂ) = determinantWeight abv g.val c := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem mirabolicDeterminantCharacter_unipotent (abv : AbsoluteValue F ℝ) (n : ℕ) (c : ℂ)
    (u : Mirabolic.upperUnipotent n F) :
    mirabolicDeterminantCharacter abv n c u = 1 := by
  apply Units.ext
  have hdet : Matrix.det (u : mirabolic n F).val.val = 1 :=
    unipotent_det (Mirabolic.upperUnipotentEquiv u)
  rw [mirabolicDeterminantCharacter_apply, determinantWeight, hdet, map_one,
    Complex.ofReal_one, Complex.one_cpow, Units.val_one]

theorem isOpen_ker_mirabolicDeterminantCharacter {abv : AbsoluteValue F ℝ}
    (hopen : Shahidi.IsOpenNormOne abv) (n : ℕ) (c : ℂ) :
    IsOpen ((mirabolicDeterminantCharacter abv n c).ker : Set (mirabolic n F)) :=
  (Shahidi.isOpen_ker_determinantPower hopen (n + 1) c).preimage continuous_subtype_val

/-- Determinant twisting on the actual compact mirabolic model: multiplication by
`|det|^c` identifies the `|det|^c`-twist of the model with the model. -/
def mirabolicDeterminantTwistEquiv {abv : AbsoluteValue F ℝ}
    (hopen : Shahidi.IsOpenNormOne abv) (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (c : ℂ) :
    (twist (mirabolicDeterminantCharacter abv n c) (mirabolicCompactInduced ψ n)).Equiv
      (mirabolicCompactInduced ψ n) :=
  Induction.compactCharacterMultiplyEquiv _ _ _
    (mirabolicDeterminantCharacter_unipotent abv n c)
    (isOpen_ker_mirabolicDeterminantCharacter hopen n c)

@[simp] theorem mirabolicDeterminantTwistEquiv_apply {abv : AbsoluteValue F ℝ}
    (hopen : Shahidi.IsOpenNormOne abv) (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (c : ℂ)
    (f : MirabolicCompactFunctions ψ n) (g : mirabolic n F) :
    (mirabolicDeterminantTwistEquiv hopen ψ n c f).val.val.val g =
      determinantWeight abv g.val c * f.val.val.val g := rfl

/-- Forms on the compact model with covariance `|det|^c κ'` are the forms with
covariance `κ'`. -/
def mirabolicFormsDeterminantShift {abv : AbsoluteValue F ℝ}
    (hopen : Shahidi.IsOpenNormOne abv) (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (σ' : Representation ℂ (mirabolic n F) W)
    (c : ℂ) (κ κ' : mirabolic n F → ℂ)
    (h : ∀ g, κ g = determinantWeight abv g.val c * κ' g) :
    InvariantBilinear.forms (mirabolicCompactInduced ψ n) σ' κ ≃ₗ[ℂ]
      InvariantBilinear.forms (mirabolicCompactInduced ψ n) σ' κ' :=
  Induction.formsCharacterShift _ _ σ' (mirabolicDeterminantCharacter abv n c)
    (mirabolicDeterminantCharacter_unipotent abv n c)
    (isOpen_ker_mirabolicDeterminantCharacter hopen n c) κ κ' h

end Topology

end Langlands.Whittaker
