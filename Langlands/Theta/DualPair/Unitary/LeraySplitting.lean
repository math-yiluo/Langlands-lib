import Langlands.Theta.DualPair.Unitary.Splitting
import Langlands.Theta.Metaplectic.Exact
import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.Theta.Heisenberg.SchrodingerUnitary

/-!
# The Leray splitting of `U(ν, ν)` in the metaplectic group of pairs

GKT §11.2 (Theorem 11.6, Corollary 11.7, Definition 11.13), §12.4 (Propositions 12.27, 12.29) and
Definition 13.15 in Case `3₊` with `W` split: the Weil representation of `U(ν, ν)` constructed in
`Langlands.Theta.DualPair.Unitary.Splitting` is `ω_ψ ∘ s` for a splitting `s` of `U(ν, ν)` in the
metaplectic group `MetaplecticGroup ρ` of pairs (GKT §2.1.2) of the Schrödinger model `ρ`.

**Normalizations.** The book's symplectic form on `𝕎 = W ⊗ V` is
`⟪w ⊗ v, w' ⊗ v'⟫ = tr_{E/F}(⟨w, w'⟩ \overline{(v, v')})` (Theorem 10.28); the form of
`Langlands.Theta.DualPair.Unitary.Form` is half of it. Here:

* `hermitianTracePairing c Q = 2 · hermitianPairing c Q`, `(x, y) ↦ tr_{E/F} tr(Qᵀ x c(y)ᵀ)`, is the
  book's pairing of `𝕏^*` and `𝕏`, and `hermitianTraceSchrodinger c ν Q ψ` is the book's Schrödinger
  model `S(𝕏^*)` of the Heisenberg group of `(𝕎, ⟪,⟫)` with central character `ψ`;
* `hermitianSchrodinger_scale_comp`: the Library's model of `(½ ⟪,⟫, x ↦ ψ(2x))` is the book's model
  of `(⟪,⟫, ψ)` through `(w, t) ↦ (w, t/2)`. So the Library's character is the book's `ψ(2 ·)`, and
  the book's `ψ` is the Library's `ψ_{1/2}`.

**The splitting.**

* `UnitaryGroup.toIsometry c hc hQ`, `UnitaryGroup.toTraceIsometry c hc hQ`: `g ↦ (w ↦ w g⁻¹)`, the
  image of `U(ν, ν)` in the isometry groups of the two forms; `heisenbergAction` is the action of
  `toIsometry` on the Heisenberg group.
* `IsLerayWeil.splitting`: a representation `ω` with `IsLerayWeil c ψ χ Q μ κ ω` is the Weil
  representation of the splitting `g ↦ (g, ω g)` of `toIsometry` (`IsLerayWeil.weil_splitting`):
  `ω = ω_ψ ∘ s` (GKT Definition 13.15), in the Library's normalization.
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis Langlands.HeisenbergGroup
open Langlands.LinearMap.BilinForm (isometryGroup)

section Pairing

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The book's pairing of `𝕏^* = M_{α×ν}(E)` with `𝕏 = M_{α×ν}(E)`:
`(x, y) ↦ tr_{E/F} tr(Qᵀ x c(y)ᵀ)` (`hermitianTracePairing_apply`), twice `hermitianPairing`; its
polarized form is the book's `⟪,⟫` of GKT Theorem 10.28 on `𝕎 = W ⊗ V`. -/
def hermitianTracePairing (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  (2 : F) • hermitianPairing c Q

omit [DecidableEq ν] in
theorem hermitianTracePairing_eq_mul (Q : Matrix α α E) (x y : Matrix α ν E) :
    hermitianTracePairing c Q x y = (2 : F) * hermitianPairing c Q x y := rfl

omit [DecidableEq ν] in
theorem hermitianTracePairing_apply [NeZero (2 : F)] (Q : Matrix α α E) (x y : Matrix α ν E) :
    hermitianTracePairing c Q x y = Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  rw [hermitianTracePairing_eq_mul, hermitianPairing_apply, ← mul_assoc,
    mul_inv_cancel₀ two_ne_zero, one_mul]

variable {c}

/-- `U(ν, ν)` in the isometry group of `polarizedForm (hermitianPairing c Q)`: `g` acts by
`w ↦ w g⁻¹`. -/
def _root_.Langlands.UnitaryGroup.toIsometry (hc : Function.Involutive c) {Q : Matrix α α E}
    (hQ : Matrix.IsHermitianFor c Q) :
    ofForm c (hyperbolicForm ν E) →* isometryGroup (polarizedForm (hermitianPairing (ν := ν) c Q))
    where
  toFun g :=
    ⟨UnitaryGroup.rightMulInvEquiv c g, UnitaryGroup.polarizedForm_rightMulInvEquiv c hc hQ g⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun w => by
    change UnitaryGroup.rightMulInvEquiv c 1 w = w
    simp [UnitaryGroup.rightMulInvEquiv_apply]
  map_mul' g h := Subtype.ext <| LinearEquiv.ext fun w => by
    change UnitaryGroup.rightMulInvEquiv c (g * h) w =
      UnitaryGroup.rightMulInvEquiv c g (UnitaryGroup.rightMulInvEquiv c h w)
    simp only [UnitaryGroup.rightMulInvEquiv_apply, fromCols_toCols, _root_.mul_inv_rev,
      Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

theorem _root_.Langlands.UnitaryGroup.toIsometry_apply (hc : Function.Involutive c)
    {Q : Matrix α α E} (hQ : Matrix.IsHermitianFor c Q) (g : ofForm c (hyperbolicForm ν E)) :
    (UnitaryGroup.toIsometry (ν := ν) hc hQ g : (Matrix α ν E × Matrix α ν E) ≃ₗ[F] _) =
      UnitaryGroup.rightMulInvEquiv c g := rfl

/-- `heisenbergAction` is the action of the isometries `toIsometry` on the Heisenberg group. -/
theorem _root_.Langlands.UnitaryGroup.heisenbergAction_eq [Invertible (2 : F)]
    (hc : Function.Involutive c) {Q : Matrix α α E} (hQ : Matrix.IsHermitianFor c Q) :
    UnitaryGroup.heisenbergAction c hc hQ =
      (isometryAction (polarizedForm (hermitianPairing (ν := ν) c Q))).comp
        (UnitaryGroup.toIsometry hc hQ) :=
  rfl

/-- `U(ν, ν)` in the isometry group of the book's form `polarizedForm (hermitianTracePairing c Q)`:
`g` acts by `w ↦ w g⁻¹`. -/
def _root_.Langlands.UnitaryGroup.toTraceIsometry (hc : Function.Involutive c) {Q : Matrix α α E}
    (hQ : Matrix.IsHermitianFor c Q) :
    ofForm c (hyperbolicForm ν E) →*
      isometryGroup (polarizedForm (hermitianTracePairing (ν := ν) c Q)) where
  toFun g := ⟨UnitaryGroup.rightMulInvEquiv c g, fun w w' => by
    rw [polarizedForm_eq_mul (2 : F) (hermitianTracePairing_eq_mul c Q),
      polarizedForm_eq_mul (2 : F) (hermitianTracePairing_eq_mul c Q),
      UnitaryGroup.polarizedForm_rightMulInvEquiv c hc hQ]⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun w => by
    change UnitaryGroup.rightMulInvEquiv c 1 w = w
    simp [UnitaryGroup.rightMulInvEquiv_apply]
  map_mul' g h := Subtype.ext <| LinearEquiv.ext fun w => by
    change UnitaryGroup.rightMulInvEquiv c (g * h) w =
      UnitaryGroup.rightMulInvEquiv c g (UnitaryGroup.rightMulInvEquiv c h w)
    simp only [UnitaryGroup.rightMulInvEquiv_apply, fromCols_toCols, _root_.mul_inv_rev,
      Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

theorem _root_.Langlands.UnitaryGroup.toTraceIsometry_apply (hc : Function.Involutive c)
    {Q : Matrix α α E} (hQ : Matrix.IsHermitianFor c Q) (g : ofForm c (hyperbolicForm ν E)) :
    (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g : (Matrix α ν E × Matrix α ν E) ≃ₗ[F] _) =
      UnitaryGroup.rightMulInvEquiv c g := rfl

end Pairing

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsModuleTopology F E] (c : E →ₐ[F] E) {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν]
  [DecidableEq ν]

/-- The unit `2 ∈ Fˣ`. -/
def twoUnit (F : Type) [Field F] [Invertible (2 : F)] : Fˣ := unitOfInvertible 2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem coe_twoUnit : ((twoUnit F : Fˣ) : F) = 2 := rfl

omit [Invertible (2 : F)] in
theorem continuous_hermitianTracePairing_left (Q : Matrix α α E) (y : Matrix α ν E) :
    Continuous fun x : Matrix α ν E => hermitianTracePairing c Q x y := by
  simp only [hermitianTracePairing_eq_mul]
  exact continuous_const.mul (continuous_hermitianPairing_left c Q y)

variable (ν) in
/-- **The book's Schrödinger model** `S(𝕏^*)` of the unitary pair (GKT §12.4.1): the Schrödinger
representation of the Heisenberg group of `(𝕎, ⟪,⟫)`,
`⟪,⟫ = polarizedForm (hermitianTracePairing c Q)`,
on the Schwartz–Bruhat functions on `M_{α×ν}(E)`, with central character `ψ`. -/
def hermitianTraceSchrodinger (Q : Matrix α α E) (ψ : UnitaryAdditiveCharacter F) :
    Representation ℂ (HeisenbergGroup (polarizedForm (hermitianTracePairing (ν := ν) c Q)))
      (SchwartzBruhat (Matrix α ν E)) :=
  have := IsModuleTopology.isTopologicalAddGroup F E
  schrodingerSB ψ.continuous_complex (continuous_hermitianTracePairing_left c Q)

theorem hermitianTraceSchrodinger_apply (Q : Matrix α α E) (ψ : UnitaryAdditiveCharacter F)
    (k : HeisenbergGroup (polarizedForm (hermitianTracePairing (ν := ν) c Q)))
    (φ : SchwartzBruhat (Matrix α ν E)) :
    (hermitianTraceSchrodinger c ν Q ψ k φ : Matrix α ν E → ℂ) =
      schrodinger ψ.complex (hermitianTracePairing c Q) k φ := rfl

/-- `(w, t) ↦ (w, t / 2)`, from the Heisenberg group of the book's form to that of the Library's. -/
def traceHeisenbergEquiv (Q : Matrix α α E) :
    HeisenbergGroup (polarizedForm (hermitianTracePairing (ν := ν) c Q)) ≃*
      HeisenbergGroup (polarizedForm (hermitianPairing (ν := ν) c Q)) :=
  mulCenEquiv (twoUnit F) (polarizedForm_eq_mul _ (hermitianTracePairing_eq_mul c Q))

/-- **The book's `ψ` and the Library's `ψ(2 ·)`** (GKT Theorem 10.28 against the form `½ ⟪,⟫` of
`hermitianSymplecticForm`): the Library's Schrödinger model of `(½ ⟪,⟫, x ↦ ψ(2x))`, read through
`(w, t) ↦ (w, t/2)`, is the book's Schrödinger model of `(⟪,⟫, ψ)`. Equivalently, the Library's
model
for a character `ψ` is the book's model for `ψ_{1/2} : x ↦ ψ(x/2)`. -/
theorem hermitianSchrodinger_scale_comp (Q : Matrix α α E) (ψ : UnitaryAdditiveCharacter F) :
    (hermitianSchrodinger c ν Q (ψ.scale (twoUnit F))).comp
      (traceHeisenbergEquiv c Q).toMonoidHom = hermitianTraceSchrodinger c ν Q ψ := by
  have h2 : (ψ.scale (twoUnit F)).complex = ψ.complex.mulShift (twoUnit F : F) := by
    ext x; simp
  ext k φ : 2
  apply Subtype.ext
  change schrodinger (ψ.scale (twoUnit F)).complex (hermitianPairing c Q)
      (traceHeisenbergEquiv c Q k) φ = schrodinger ψ.complex (hermitianTracePairing c Q) k φ
  rw [h2]
  exact LinearMap.congr_fun (DFunLike.congr_fun
    (schrodinger_comp_mulCenEquiv ψ.complex (twoUnit F) (hermitianTracePairing_eq_mul c Q)) k) φ

variable {c}

/-- A representation normalizing the Library's model of `(½ ⟪,⟫, ψ(2 ·))` along `heisenbergAction`
normalizes the book's model of `(⟪,⟫, ψ)` along the isometries `toTraceIsometry`. -/
theorem normalizes_hermitianTraceSchrodinger (hc : Function.Involutive c) {Q : Matrix α α E}
    (hQ : Matrix.IsHermitianFor c Q) (ψ : UnitaryAdditiveCharacter F)
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : Normalizes (hermitianSchrodinger c ν Q (ψ.scale (twoUnit F)))
      (UnitaryGroup.heisenbergAction c hc hQ) ω) :
    Normalizes (hermitianTraceSchrodinger c ν Q ψ)
      ((isometryAction _).comp (UnitaryGroup.toTraceIsometry hc hQ)) ω := by
  intro g k
  have e : traceHeisenbergEquiv c Q (isometryAction _ (UnitaryGroup.toTraceIsometry hc hQ g) k) =
      UnitaryGroup.heisenbergAction c hc hQ g (traceHeisenbergEquiv c Q k) := rfl
  rw [← hermitianSchrodinger_scale_comp]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [e]
  exact h g (traceHeisenbergEquiv c Q k)

end Model

/-! ### The splitting of a representation `IsLerayWeil`, and its uniqueness -/

section Splitting

open Unitary.Internal

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {Q : Matrix α α E} {χ : Eˣ →* Circle}

/-- **The Weil representation `ω` is `ω_ψ ∘ s`** (GKT Corollary 11.7, Definition 13.15): a
representation with `IsLerayWeil c ψ χ Q μ κ ω` is the Weil representation of the splitting
`g ↦ (w ↦ w g⁻¹, ω g)` of `U(ν, ν)` in the metaplectic group of pairs of the Schrödinger model
`hermitianSchrodinger c ν Q ψ` (the Library's normalization: the form `½ ⟪,⟫`). -/
def IsLerayWeil.splitting [Invertible (2 : F)] {ψ : UnitaryAdditiveCharacter F}
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] {μ : Measure (Matrix α ν E)}
    [μ.IsAddHaarMeasure] {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : IsLerayWeil c ψ.complex χ Q μ κ ω) (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    MetaplecticGroup.Splitting (hermitianSchrodinger c ν Q ψ)
      (UnitaryGroup.toIsometry hE.involutive hQ) :=
  MetaplecticGroup.Splitting.ofNormalizes ω (h.normalizes hE hQ hQu hχ hres)

/-- The Weil representation of `IsLerayWeil.splitting` is `ω`. -/
@[simp] theorem IsLerayWeil.weil_splitting [Invertible (2 : F)] {ψ : UnitaryAdditiveCharacter F}
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] {μ : Measure (Matrix α ν E)}
    [μ.IsAddHaarMeasure] {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : IsLerayWeil c ψ.complex χ Q μ κ ω) (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (h.splitting hE hQ hQu hχ hres).weil = ω :=
  MetaplecticGroup.Splitting.weil_ofNormalizes _ _

omit [CharZero F] [Algebra.IsQuadraticExtension F E] [DecidableEq α] [DecidableEq ν] in
/-- The Schwartz–Bruhat functions on `M_{α×ν}(E)` are not all zero. -/
theorem exists_schwartzBruhat_ne_zero (hE : IsQuadraticInvolution c δ) :
    ∃ φ : SchwartzBruhat (Matrix α ν E), φ ≠ 0 := by
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  obtain ⟨L, hc, ho, -⟩ := CompactOpenExhaustion.exists_subset (X := Matrix α ν E) Set.univ
    Filter.univ_mem
  refine ⟨⟨_, HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule L hc ho⟩, fun h => ?_⟩
  have := congrFun (congrArg Subtype.val h) 0
  simp at this

omit [CharZero F] [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  [DecidableEq α] in
private theorem siegelParabolicOp_smul (ψ : AddChar F ℂ) (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (k : ℂ)
    (f : Matrix α ν E → ℂ) :
    siegelParabolicOp c ψ χ Q g (k • f) = k • siegelParabolicOp c ψ χ Q g f := by
  funext x; simp only [siegelParabolicOp, Pi.smul_apply, smul_eq_mul]; ring

omit [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E] in
omit [DecidableEq α] in
private theorem hermitianFourier_smul [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ)
    (μ : Measure (Matrix α ν E)) (k : ℂ) (f : Matrix α ν E → ℂ) :
    hermitianFourier c ψ Q μ (k • f) = k • hermitianFourier c ψ Q μ f := by
  funext x
  simp only [hermitianFourier, bicharacterFourier, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]; congr 1; funext y; ring

omit [CharZero F] [Algebra.IsQuadraticExtension F E] [DecidableEq α] in
/-- The scalar at the Weyl element is not zero. -/
theorem IsLerayWeil.ne_zero [MeasurableSpace (Matrix α ν E)] {ψ : AddChar F ℂ}
    {μ : Measure (Matrix α ν E)} {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : IsLerayWeil c ψ χ Q μ κ ω) (hE : IsQuadraticInvolution c δ) : κ ≠ 0 := by
  rintro rfl
  obtain ⟨φ, hφ⟩ := exists_schwartzBruhat_ne_zero (α := α) (ν := ν) hE
  have h0 : ω (weylElement c ν) (ω (weylElement c ν)⁻¹ φ) = 0 :=
    Subtype.ext (by rw [h.weylElement_apply, zero_smul]; rfl)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h0
  exact hφ h0

omit [Algebra.IsQuadraticExtension F E] in
omit [DecidableEq α] in
/-- **The scalar at the Weyl element and the representation are unique** (`κ` is not existential):
two representations `IsLerayWeil` for the same data and the same measure have the same scalar and
are equal. From the relation `w n w = p₀ w n'` of the big cell (`n = n(1)`, `n' = n(-1)`,
`p₀ ∈ P`), the scalars satisfy `κ² X = κ Y` with `X = ℱ T(n) ℱ φ ≠ 0`, `Y = T(p₀) ℱ T(n') φ`
independent of `κ`; then `P` and the Weyl element generate `U(ν, ν)`. -/
theorem IsLerayWeil.unique [MeasurableSpace (Matrix α ν E)] {ψ : AddChar F ℂ}
    {μ : Measure (Matrix α ν E)} {κ κ' : ℂ}
    {ω ω' : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (hE : IsQuadraticInvolution c δ) (h : IsLerayWeil c ψ χ Q μ κ ω)
    (h' : IsLerayWeil c ψ χ Q μ κ' ω') : κ = κ' ∧ ω = ω' := by
  have hκ := h.ne_zero hE
  have hκ' := h'.ne_zero hE
  have hc := hE.involutive
  -- the unipotent elements `n(1)` and `n(-1)` and the element `p₀` of the Siegel parabolic
  have h1 : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have h1' := WeylCellRel.herm_neg_inv c (1 : Matrix ν ν E) h1 (by simp)
  set w := weylElement c ν
  set n := siegelUnipotent c (1 : Matrix ν ν E) h1
  set n' := siegelUnipotent c (-(1 : Matrix ν ν E)⁻¹) h1'
  set p₀ := w * n * w * n'⁻¹ * w⁻¹
  have hp₀ : p₀ ∈ siegelParabolic c ν := by
    rw [mem_sieg, WeylCellRel.splitUnitaryElementMatrix_bigCell_product c 1 h1 (by simp) h1']
    simp
  have hn : n ∈ siegelParabolic c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hn' : n' ∈ siegelParabolic c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hrel : w * n * w = p₀ * w * n' := by simp only [p₀]; group
  -- the two sides of the relation, applied to `φ`, as functions
  have key : ∀ (k : ℂ)
      (ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))),
      IsLerayWeil c ψ χ Q μ k ω → ∀ φ : SchwartzBruhat (Matrix α ν E),
      (k * k) • hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c n)
          (hermitianFourier c ψ Q μ φ)) =
        k • siegelParabolicOp c ψ χ Q (mat c p₀)
          (hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c n') φ)) ∧
      (ω (w * n * w) φ : Matrix α ν E → ℂ) = (k * k) • hermitianFourier c ψ Q μ
          (siegelParabolicOp c ψ χ Q (mat c n) (hermitianFourier c ψ Q μ φ)) := by
    intro k ω hω φ
    have e1 : (ω (w * n * w) φ : Matrix α ν E → ℂ) = (k * k) • hermitianFourier c ψ Q μ
        (siegelParabolicOp c ψ χ Q (mat c n) (hermitianFourier c ψ Q μ φ)) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hω.weylElement_apply,
        hω.apply_of_mem_siegelParabolic n hn, hω.weylElement_apply, siegelParabolicOp_smul,
        hermitianFourier_smul, smul_smul]
    refine ⟨?_, e1⟩
    rw [← e1, hrel, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hω.apply_of_mem_siegelParabolic p₀ hp₀, hω.weylElement_apply,
      hω.apply_of_mem_siegelParabolic n' hn', siegelParabolicOp_smul]
  obtain ⟨φ, hφ⟩ := exists_schwartzBruhat_ne_zero (α := α) (ν := ν) hE
  obtain ⟨k1, k2⟩ := key κ ω h φ
  obtain ⟨k1', -⟩ := key κ' ω' h' φ
  set X := hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c n)
    (hermitianFourier c ψ Q μ φ))
  set Y := siegelParabolicOp c ψ χ Q (mat c p₀)
    (hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c n') φ))
  have hX : X ≠ 0 := by
    intro hX0
    rw [hX0, smul_zero] at k2
    apply hφ
    have : ω (w * n * w) φ = 0 := Subtype.ext k2
    have h2 := congrArg (ω (w * n * w)⁻¹) this
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h2
  have e : κ • X = κ' • X := by
    have a : κ • (κ • X) = κ • Y := by rw [smul_smul]; exact k1
    have b : κ' • (κ' • X) = κ' • Y := by rw [smul_smul]; exact k1'
    rw [smul_right_injective _ hκ a, smul_right_injective _ hκ' b]
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hX
  have hk : κ = κ' := by
    have := congrFun e x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hx
    exact mul_right_cancel₀ hx this
  refine ⟨hk, ?_⟩
  -- `ω` and `ω'` agree on the Siegel parabolic and at the Weyl element
  let U : Subgroup (ofForm c (hyperbolicForm ν E)) :=
    { carrier := {g | ω g = ω' g}
      mul_mem' := fun {a b} ha hb => by
        change ω (a * b) = ω' (a * b); rw [map_mul, map_mul, ha.out, hb.out]
      one_mem' := by change ω 1 = ω' 1; rw [map_one, map_one]
      inv_mem' := fun {a} ha => by
        change ω a⁻¹ = ω' a⁻¹
        have := ha.out
        calc ω a⁻¹ = ω a⁻¹ * (ω' a * ω' a⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
          _ = ω a⁻¹ * (ω a * ω' a⁻¹) := by rw [this]
          _ = ω' a⁻¹ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] }
  have : Infinite F := Infinite.of_injective _ Nat.cast_injective
  have hU := eq_top_of_siegelParabolic_le_of_weylElement_mem hE (U := U)
    (fun p hp => LinearMap.ext fun φ => Subtype.ext (by
      rw [h.apply_of_mem_siegelParabolic p hp, h'.apply_of_mem_siegelParabolic p hp]))
    (LinearMap.ext fun φ => Subtype.ext (by rw [h.weylElement_apply, h'.weylElement_apply, hk]))
  exact MonoidHom.ext fun g => (show g ∈ U from hU ▸ Subgroup.mem_top g)

end Splitting

/-! ### The Leray splitting in the book's normalization -/

section Leray

open Unitary.Internal

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {Q : Matrix α α E} {χ : Eˣ →* Circle} {ψ : UnitaryAdditiveCharacter F}

omit [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] [TopologicalSpace E] [IsModuleTopology F E]
  [Algebra.IsQuadraticExtension F E] in
private theorem hermitianPairing_eq_pr (x y : Matrix α ν E) :
    hermitianPairing c Q x y = pr c Q x y :=
  hermitianPairing_eq_hermitianSymplecticForm c Q x y

variable (c) in
/-- **The scalar at the Weyl element** of the Weil representation of the Leray splitting with data
`(χ, ψ)` (the book's `ψ`), for the Haar measure `μ`: the `κ` of `IsLerayWeil` for the Library's
character `ψ(2 ·)`; it is unique (`IsLerayWeil.unique`). It is the book's `β(w)` of Proposition
12.29 times the factor correcting the measure `μ`. -/
def lerayScalar (ψ : UnitaryAdditiveCharacter F) (χ : Eˣ →* Circle) (Q : Matrix α α E)
    [MeasurableSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) : ℂ :=
  open Classical in
  if h : ∃ κ : ℂ, ∃ ω : Representation ℂ (ofForm c (hyperbolicForm ν E))
      (SchwartzBruhat (Matrix α ν E)), IsLerayWeil c (ψ.scale (twoUnit F)).complex χ Q μ κ ω
  then h.choose else 0

variable (c) in
/-- `ω` is a representation `IsLerayWeil` for some Haar measure on the Borel σ-algebra. -/
def IsLerayWeilBorel (ψ : AddChar F ℂ) (χ : Eˣ →* Circle) (Q : Matrix α α E)
    (ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))) :
    Prop :=
  letI : MeasurableSpace (Matrix α ν E) := borel _
  ∃ (μ : Measure (Matrix α ν E)) (κ : ℂ), μ.IsAddHaarMeasure ∧ IsLerayWeil c ψ χ Q μ κ ω

variable (c) (ν) in
/-- **The Weil representation of the Leray splitting of `U(ν, ν)` with data `(χ, ψ)`** (GKT
Definition 11.13, Proposition 12.27 (1)), the book's `ψ`: the representation of
`Langlands.Theta.DualPair.Unitary.Splitting` for the Library's character `ψ(2 ·)`
(`isLerayWeil_lerayWeil`). It does not depend on a Haar measure. -/
def lerayWeil (ψ : UnitaryAdditiveCharacter F) (χ : Eˣ →* Circle) (Q : Matrix α α E) :
    Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E)) :=
  open Classical in
  if h : ∃ ω, IsLerayWeilBorel c (ψ.scale (twoUnit F)).complex χ Q ω then h.choose else 1

omit [CharZero F] [Invertible (2 : F)] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  [DecidableEq α] in
/-- Multiplying the Haar measure by `r` multiplies the Fourier transform, hence divides the scalar,
by `r`: from the measure `r • μ` to `μ`. -/
theorem IsLerayWeil.of_smul_measure [MeasurableSpace (Matrix α ν E)] {ψ' : AddChar F ℂ}
    {μ : Measure (Matrix α ν E)} {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    {r : NNReal} (h : IsLerayWeil c ψ' χ Q (r • μ) κ ω) :
    IsLerayWeil c ψ' χ Q μ (κ * (r : ℂ)) ω where
  apply_of_mem_siegelParabolic := h.apply_of_mem_siegelParabolic
  weylElement_apply φ := by
    rw [h.weylElement_apply]
    funext x
    simp only [hermitianFourier, bicharacterFourier, Pi.smul_apply, smul_eq_mul,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    ring

omit [DecidableEq α] in
/-- **Identification**: a representation `IsLerayWeil` for the Library's character `ψ(2 ·)` has
the scalar `lerayScalar c ψ χ Q μ` and is `lerayWeil c ν ψ χ Q`. -/
theorem IsLerayWeil.eq_leray (hE : IsQuadraticInvolution c δ)
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] {μ : Measure (Matrix α ν E)}
    [μ.IsAddHaarMeasure] {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : IsLerayWeil c (ψ.scale (twoUnit F)).complex χ Q μ κ ω) :
    κ = lerayScalar c ψ χ Q μ ∧ ω = lerayWeil c ν ψ χ Q := by
  constructor
  · have hex : ∃ κ : ℂ, ∃ ω : Representation ℂ (ofForm c (hyperbolicForm ν E))
        (SchwartzBruhat (Matrix α ν E)), IsLerayWeil c (ψ.scale (twoUnit F)).complex χ Q μ κ ω :=
      ⟨κ, ω, h⟩
    rw [lerayScalar, dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨ω₁, h₁⟩ := hex.choose_spec
    exact (h.unique hE h₁).1
  · have hm : ‹MeasurableSpace (Matrix α ν E)› = borel _ := BorelSpace.measurable_eq
    subst hm
    have hex : ∃ ω, IsLerayWeilBorel c (ψ.scale (twoUnit F)).complex χ Q ω :=
      ⟨ω, μ, κ, inferInstance, h⟩
    rw [lerayWeil, dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨μ₀, κ₀, hμ₀, h₀⟩ := hex.choose_spec
    let : MeasurableSpace (Matrix α ν E) := borel _
    have : BorelSpace (Matrix α ν E) := ⟨rfl⟩
    have : FiniteDimensional F E := hE.finite
    have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
    have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
    have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
    have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
    have hsc : μ₀ = MeasureTheory.Measure.addHaarScalarFactor μ₀ μ • μ :=
      MeasureTheory.Measure.isAddLeftInvariant_eq_smul μ₀ μ
    rw [hsc] at h₀
    exact (h.unique hE h₀.of_smul_measure).2

/-- **The Weil representation of the Leray splitting is `IsLerayWeil`** for the Library's character
`ψ(2 ·)`, with the scalar `lerayScalar` (this joins the book's normalization `(⟪,⟫, ψ)` and the
Library's `(½ ⟪,⟫, ψ(2 ·))`). -/
theorem isLerayWeil_lerayWeil (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E))
    [μ.IsAddHaarMeasure] :
    IsLerayWeil c (ψ.scale (twoUnit F)).complex χ Q μ (lerayScalar c ψ χ Q μ)
      (lerayWeil c ν ψ χ Q) := by
  obtain ⟨κ, ω, h⟩ := exists_isLerayWeil (ψ := ψ.scale (twoUnit F)) hE hQ hQu hχ hres μ
  obtain ⟨h1, h2⟩ := h.eq_leray hE
  rwa [← h1, ← h2]

/-- Some Haar measure on the Borel σ-algebra of `M_{α×ν}(E)` makes `lerayWeil` a representation
`IsLerayWeil`. -/
private theorem exists_isLerayWeil_lerayWeil (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    IsLerayWeilBorel c (ψ.scale (twoUnit F)).complex χ Q (lerayWeil c ν ψ χ Q) := by
  let _ : MeasurableSpace (Matrix α ν E) := borel _
  have : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := t2Space_of_finiteDimensional F (Matrix α ν E)
  exact ⟨Measure.addHaar, _, inferInstance, isLerayWeil_lerayWeil hE hQ hQu hχ hres _⟩

/-- **The Weil representation of the Leray splitting normalizes the book's Schrödinger model**:
`ω(g) ρ(w, t) ω(g)⁻¹ = ρ(w g⁻¹, t)` for the Heisenberg representation `ρ` of `(𝕎, ⟪,⟫)` with central
character `ψ` (relation (2.2) of GKT p. 47). -/
theorem lerayWeil_normalizes (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    Normalizes (hermitianTraceSchrodinger c ν Q ψ)
      ((isometryAction _).comp (UnitaryGroup.toTraceIsometry hE.involutive hQ))
      (lerayWeil c ν ψ χ Q) := by
  obtain ⟨μ, κ, hμ, h⟩ := exists_isLerayWeil_lerayWeil (ν := ν) (ψ := ψ) hE hQ hQu hχ hres
  let _ : MeasurableSpace (Matrix α ν E) := borel _
  have : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  exact normalizes_hermitianTraceSchrodinger hE.involutive hQ ψ (h.normalizes hE hQ hQu hχ hres)

/-- **The Leray splitting** `s^V_{ψ,χ}` of `U(ν, ν)` (GKT Theorem 11.6, Corollary 11.7, Definition
11.13, Case `3₊` with `W` split) in the metaplectic group of pairs of the book's Schrödinger model
`hermitianTraceSchrodinger c ν Q ψ`: `g ↦ (w ↦ w g⁻¹, lerayWeil g)`. -/
def leraySplitting (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    MetaplecticGroup.Splitting (hermitianTraceSchrodinger c ν Q ψ)
      (UnitaryGroup.toTraceIsometry hE.involutive hQ) :=
  MetaplecticGroup.Splitting.ofNormalizes _ (lerayWeil_normalizes hE hQ hQu hχ hres)

/-- **`ω_{ψ,χ} = ω_ψ ∘ s^V_{ψ,χ}`** (GKT Definition 13.15): the Weil representation of the Leray
splitting is `lerayWeil`. -/
@[simp] theorem weil_leraySplitting (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (leraySplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).weil = lerayWeil c ν ψ χ Q :=
  MetaplecticGroup.Splitting.weil_ofNormalizes _ _

/-- **The Weil representation of the Leray splitting is smooth** (GKT Proposition 13.16). -/
theorem isSmooth_lerayWeil (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    IsSmooth (lerayWeil c ν ψ χ Q) := by
  obtain ⟨μ, κ, hμ, h⟩ := exists_isLerayWeil_lerayWeil (ν := ν) (ψ := ψ) hE hQ hQu hχ hres
  let _ : MeasurableSpace (Matrix α ν E) := borel _
  have : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  exact h.isSmooth hE hQ hQu hχ hres

/-- **The Weil representation of the Leray splitting is unitary**: it preserves `∫ ‖φ‖² dμ'` for
every Haar measure `μ'`. -/
theorem lerayWeil_lintegral_enorm_sq (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ' : Measure (Matrix α ν E))
    [μ'.IsAddHaarMeasure] (g : ofForm c (hyperbolicForm ν E)) (φ : SchwartzBruhat (Matrix α ν E)) :
    ∫⁻ x, ‖(lerayWeil c ν ψ χ Q g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' =
      ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' :=
  (isLerayWeil_lerayWeil hE hQ hQu hχ hres μ').lintegral_enorm_sq hE hQ hQu hχ hres μ' g φ

/-- **The formula on the Siegel parabolic** in the book's normalization (GKT Proposition 12.27 (1),
first two formulas, with `β(m(a) n(b)) = χ(det a)`, Proposition 12.29): for
`g = [[A, B], [0, D]] ∈ P`,
`ω(g) φ(x) = χ(det A) |N det A|^{|α|/2} ψ(½ ⟪x A, x B⟫) φ(x A)`,
`⟪,⟫ = hermitianTracePairing c Q`. -/
theorem lerayWeil_apply_of_mem_siegelParabolic (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {p : ofForm c (hyperbolicForm ν E)} (hp : p ∈ siegelParabolic c ν)
    (φ : SchwartzBruhat (Matrix α ν E)) (x : Matrix α ν E) :
    (lerayWeil c ν ψ χ Q p φ : Matrix α ν E → ℂ) x =
      splittingScalar F χ (Fintype.card α) (mat c p).toBlocks₁₁.det *
        ((ψ (⅟2 * hermitianTracePairing c Q (x * (mat c p).toBlocks₁₁)
          (x * (mat c p).toBlocks₁₂)) : ℂ) *
          (φ : Matrix α ν E → ℂ) (x * (mat c p).toBlocks₁₁)) := by
  obtain ⟨μ, κ, hμ, h⟩ := exists_isLerayWeil_lerayWeil (ν := ν) (ψ := ψ) hE hQ hQu hχ hres
  let _ : MeasurableSpace (Matrix α ν E) := borel _
  rw [h.apply_of_mem_siegelParabolic p hp φ]
  simp only [siegelParabolicOp, UnitaryAdditiveCharacter.complex_apply,
    UnitaryAdditiveCharacter.scale_apply, coe_twoUnit, hermitianTracePairing_eq_mul]
  congr 3
  rw [← mul_assoc, mul_comm (2 : F), mul_assoc, invOf_eq_inv, hermitianPairing_eq_pr]

/-- **The formula at the Weyl element** in the book's normalization (GKT Proposition 12.27 (1),
third formula): `ω(w) φ(x) = κ ∫ ψ(⟪x, y⟫) φ(y) dμ(y)` with `κ = lerayScalar c ψ χ Q μ` (the book's
`β(w)` times the factor correcting the Haar measure `μ`). -/
theorem lerayWeil_weylElement_apply (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E))
    [μ.IsAddHaarMeasure] (φ : SchwartzBruhat (Matrix α ν E)) (x : Matrix α ν E) :
    (lerayWeil c ν ψ χ Q (weylElement c ν) φ : Matrix α ν E → ℂ) x =
      lerayScalar c ψ χ Q μ *
        ∫ y, (ψ (hermitianTracePairing c Q x y) : ℂ) * (φ : Matrix α ν E → ℂ) y ∂μ := by
  rw [(isLerayWeil_lerayWeil hE hQ hQu hχ hres μ).weylElement_apply]
  simp only [hermitianFourier, bicharacterFourier, Pi.smul_apply, smul_eq_mul,
    UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.scale_apply, coe_twoUnit,
    hermitianTracePairing_eq_mul, hermitianPairing_eq_pr]

/-- **The Levi formula** (GKT Proposition 12.27 (1), Proposition 12.29): `diag(a, c(a)⁻ᵀ)` acts by
`φ ↦ χ(det a) |N_{E/F} det a|^{|α|/2} φ(· a)`. -/
theorem lerayWeil_siegelLevi_apply (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (a : GL ν E) (φ : SchwartzBruhat (Matrix α ν E)) (x : Matrix α ν E) :
    (lerayWeil c ν ψ χ Q (siegelLevi c hE.involutive a) φ : Matrix α ν E → ℂ) x =
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        (((MeasureTheory.distribHaarChar F (Units.map (Algebra.norm F : E →* F)
          (Matrix.GeneralLinearGroup.det a)) : ℝ) ^ ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
        (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E)) := by
  obtain ⟨μ, κ, hμ, h⟩ := exists_isLerayWeil_lerayWeil (ν := ν) (ψ := ψ) hE hQ hQu hχ hres
  let _ : MeasurableSpace (Matrix α ν E) := borel _
  exact h.siegelLevi_apply hE hres a φ x

omit [DecidableEq α] in
/-- **Identification for a character in the Library's normalization**: a representation
`IsLerayWeil` for a character `ψ'` (of the form `½ ⟪,⟫`) is the Weil representation of the Leray
splitting for the book's character `ψ'_{1/2} : x ↦ ψ'(x / 2)`. -/
theorem IsLerayWeil.eq_leray' (hE : IsQuadraticInvolution c δ) {ψ' : UnitaryAdditiveCharacter F}
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] {μ : Measure (Matrix α ν E)}
    [μ.IsAddHaarMeasure] {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : IsLerayWeil c ψ'.complex χ Q μ κ ω) :
    κ = lerayScalar c (ψ'.scale (twoUnit F)⁻¹) χ Q μ ∧
      ω = lerayWeil c ν (ψ'.scale (twoUnit F)⁻¹) χ Q := by
  have e : (ψ'.scale (twoUnit F)⁻¹).scale (twoUnit F) = ψ' := by
    rw [UnitaryAdditiveCharacter.scale_scale, inv_mul_cancel, UnitaryAdditiveCharacter.scale_one]
  rw [← e] at h
  exact h.eq_leray hE

end Leray

/-! ### Unitarity: the Leray splitting lands in `Mp(𝕎)^{ℂ¹}` -/

section Unitary

open Unitary.Internal

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {Q : Matrix α α E} {χ : Eˣ →* Circle} {ψ : UnitaryAdditiveCharacter F}

/-- **The Leray splitting lands in `Mp(𝕎)^{ℂ¹}`** (GKT p. 49): its operators preserve the `L²`
inner product of every Haar measure. -/
theorem leraySplitting_mem_unitary (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E))
    [μ.IsAddHaarMeasure] (g : ofForm c (hyperbolicForm ν E)) :
    (leraySplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom g ∈
      MetaplecticGroup.unitary _ (schwartzBruhatInner μ) :=
  fun f f' => schwartzBruhatInner_map μ (lerayWeil c ν ψ χ Q g)
    (fun φ => lerayWeil_lintegral_enorm_sq hE hQ hQu hχ hres μ g φ) f f'

/-- **The splitting of a representation `IsLerayWeil` lands in `Mp(𝕎)^{ℂ¹}`** (GKT p. 49), for the
`L²` inner product of every Haar measure `μ'`. -/
theorem IsLerayWeil.splitting_mem_unitary [MeasurableSpace (Matrix α ν E)]
    [BorelSpace (Matrix α ν E)] {μ : Measure (Matrix α ν E)} [μ.IsAddHaarMeasure] {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : IsLerayWeil c ψ.complex χ Q μ κ ω) (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : ofForm c (hyperbolicForm ν E)) :
    (h.splitting hE hQ hQu hχ hres).toMonoidHom g ∈
      MetaplecticGroup.unitary _ (schwartzBruhatInner μ') :=
  fun f f' => schwartzBruhatInner_map μ' (ω g)
    (fun φ => h.lintegral_enorm_sq hE hQ hQu hχ hres μ' g φ) f f'

end Unitary

end Langlands.Theta
