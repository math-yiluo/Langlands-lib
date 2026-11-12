import Mathlib
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.CompletionDerivation
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.FiberRegular

/-! # Partial derivatives on completed localizations of polynomial rings -/

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

open MvPolynomial TrivSqZeroExt

section Jet

variable {S T V : Type*} [CommRing S] [CommRing T] [AddCommGroup V] [Module T V]
  [Module Tᵐᵒᵖ V] [IsCentralScalar T V]

/-- The ring map `x ↦ (f x, d x)` into the trivial square-zero extension `T ⊕ V` defined by a ring
map `f` and an additive map `d` satisfying the Leibniz rule along `f`. -/
def jetHom (f : S →+* T) (d : S →+ V) (hd : ∀ a b, d (a * b) = f a • d b + f b • d a) :
    S →+* TrivSqZeroExt T V where
  toFun x := ((f x, d x) : TrivSqZeroExt T V)
  map_one' := by
    have h := hd 1 1
    rw [mul_one, f.map_one, one_smul] at h
    exact TrivSqZeroExt.ext (map_one f) (by simpa using h)
  map_mul' a b := by
    refine TrivSqZeroExt.ext (map_mul f a b) ?_
    change d (a * b) = f a • d b + MulOpposite.op (f b) • d a
    rw [hd, op_smul_eq_smul]
  map_zero' := TrivSqZeroExt.ext (map_zero f) (map_zero d)
  map_add' a b := TrivSqZeroExt.ext (map_add f a b) (map_add d a b)

@[simp]
theorem jetHom_fst (f : S →+* T) (d : S →+ V) (hd : ∀ a b, d (a * b) = f a • d b + f b • d a)
    (x : S) : (jetHom f d hd x).fst = f x :=
  rfl

@[simp]
theorem jetHom_snd (f : S →+* T) (d : S →+ V) (hd : ∀ a b, d (a * b) = f a • d b + f b • d a)
    (x : S) : (jetHom f d hd x).snd = d x :=
  rfl

end Jet

/-- A ring map sends `∂X_w/∂X_v` to the Kronecker delta. -/
theorem map_pderiv_X {R : Type*} [CommRing R] {τ : Type*} [DecidableEq τ] {F : Type*}
    [CommRing F] (κ : MvPolynomial τ R →+* F) (v w : τ) :
    κ (pderiv v (X w)) = Pi.single (M := fun _ => F) w 1 v := by
  by_cases h : v = w
  · subst h
    simp
  · simp [pderiv_X, h, Ne.symm h]

/-- The partial derivatives `(∂g/∂X_v)_v` of polynomials, as a ring map into a trivial square-zero
extension. -/
noncomputable def pderivJet {R : Type*} [CommRing R] {τ : Type*} {F : Type*} [CommRing F]
    (κ : MvPolynomial τ R →+* F) : MvPolynomial τ R →+* TrivSqZeroExt F (τ → F) :=
  jetHom κ
    { toFun := fun g v => κ (pderiv v g)
      map_zero' := by funext v; simp
      map_add' := fun g h => by funext v; simp }
    fun a b => by
      funext v
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Derivation.leibniz, smul_eq_mul, map_add,
        map_mul, Pi.add_apply, Pi.smul_apply]

section Local

variable {R₀ : Type*} [CommRing R₀] {σ : Type*}
  {A₀ : Type*} [CommRing A₀] [Algebra (MvPolynomial σ R₀) A₀]
  (M : Submonoid (MvPolynomial σ R₀)) [IsLocalization M A₀]

variable (A₀) in
/-- `p ↦ (p, ∂p/∂X_i)` as a ring map `R₀[X_σ] → A₀ ⊕ A₀`. -/
noncomputable def polyJet (i : σ) : MvPolynomial σ R₀ →+* TrivSqZeroExt A₀ A₀ :=
  jetHom (algebraMap _ A₀) ((algebraMap _ A₀).toAddMonoidHom.comp (pderiv i).toAddMonoidHom)
    fun a b => by simp [Derivation.leibniz]

/-- The extension of `polyJet` to the localization `A₀`. -/
noncomputable def localJet (i : σ) : A₀ →+* TrivSqZeroExt A₀ A₀ :=
  IsLocalization.lift (M := M) (g := polyJet A₀ i) fun m => by
    rw [isUnit_iff_isUnit_fst]
    exact IsLocalization.map_units A₀ m

theorem localJet_algebraMap (i : σ) (p : MvPolynomial σ R₀) :
    localJet M i (algebraMap _ A₀ p) = polyJet A₀ i p :=
  IsLocalization.lift_eq _ p

theorem localJet_fst (i : σ) (a : A₀) : (localJet M i a).fst = a := by
  have : (fstHom A₀ A₀ A₀).toRingHom.comp (localJet M i) = RingHom.id A₀ :=
    IsLocalization.ringHom_ext M (RingHom.ext fun p => by
      simp [localJet_algebraMap, polyJet])
  exact RingHom.congr_fun this a

/-- The partial derivative `∂/∂X_i` on the localization `A₀` of `R₀[X_σ]`. -/
noncomputable def localDeriv (i : σ) : A₀ →+ A₀ where
  toFun a := (localJet M i a).snd
  map_zero' := by rw [map_zero, snd_zero]
  map_add' a b := by rw [map_add, snd_add]

theorem localDeriv_algebraMap (i : σ) (p : MvPolynomial σ R₀) :
    localDeriv M i (algebraMap _ A₀ p) = algebraMap _ A₀ (pderiv i p) := by
  change (localJet M i (algebraMap _ A₀ p)).snd = _
  rw [localJet_algebraMap]
  rfl

theorem localDeriv_mul (i : σ) (a b : A₀) :
    localDeriv M i (a * b) = a * localDeriv M i b + b * localDeriv M i a := by
  change (localJet M i (a * b)).snd = a * (localJet M i b).snd + b * (localJet M i a).snd
  rw [map_mul, snd_mul, localJet_fst, localJet_fst, op_smul_eq_smul, smul_eq_mul, smul_eq_mul]

end Local

section Completion

variable {R₀ : Type*} [CommRing R₀] {σ μ : Type*} [DecidableEq σ] [DecidableEq μ]
  {A₀ : Type*} [CommRing A₀] [Algebra (MvPolynomial σ R₀) A₀]
  (M : Submonoid (MvPolynomial σ R₀)) [IsLocalization M A₀] (I : Ideal A₀)

/-- The derivations `∂/∂X_i` (for `i ∈ σ`) extended to the completion `Â₀`, and `0` for the
indices in `μ`. -/
noncomputable def hatDeriv : σ ⊕ μ → AdicCompletion I A₀ →+ AdicCompletion I A₀
  | Sum.inl i => completionDeriv I (localDeriv M i) (localDeriv_mul M i)
  | Sum.inr _ => 0

omit [DecidableEq σ] [DecidableEq μ] in
theorem hatDeriv_mul (v : σ ⊕ μ) (x y : AdicCompletion I A₀) :
    hatDeriv M I v (x * y) = x * hatDeriv M I v y + y * hatDeriv M I v x := by
  rcases v with i | j
  · exact completionDeriv_mul I (localDeriv M i) (localDeriv_mul M i) x y
  · simp [hatDeriv]

omit [DecidableEq σ] [DecidableEq μ] in
theorem hatDeriv_inl_algebraMap (i : σ) (p : MvPolynomial σ R₀) :
    hatDeriv (μ := μ) M I (Sum.inl i) (algebraMap A₀ _ (algebraMap _ A₀ p)) =
      algebraMap A₀ _ (algebraMap _ A₀ (pderiv i p)) := by
  simp only [hatDeriv, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [completionDeriv_of, localDeriv_algebraMap]

variable {F : Type*} [CommRing F] (ρ : MvPolynomial μ (AdicCompletion I A₀) →+* F)

/-- On coefficients: `b ↦ (b, (∂b/∂X_v)_v)` with values reduced along `ρ`. -/
noncomputable def coeffJet : AdicCompletion I A₀ →+* TrivSqZeroExt F (σ ⊕ μ → F) :=
  jetHom (ρ.comp C)
    { toFun := fun b v => ρ (C (hatDeriv M I v b))
      map_zero' := by funext v; simp
      map_add' := fun a b => by funext v; simp }
    fun a b => by
      funext v
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, hatDeriv_mul, map_add, map_mul,
        RingHom.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The partial derivatives on `Â₀[Y_μ]` reduced along `ρ`, as a ring map into a trivial
square-zero extension. -/
noncomputable def completedJet :
    MvPolynomial μ (AdicCompletion I A₀) →+* TrivSqZeroExt F (σ ⊕ μ → F) :=
  eval₂Hom (coeffJet M I ρ) fun j => inl (ρ (X j)) + inr (Pi.single (Sum.inr j) 1)

theorem completedJet_fst (f : MvPolynomial μ (AdicCompletion I A₀)) :
    (completedJet M I ρ f).fst = ρ f := by
  have : (fstHom F F (σ ⊕ μ → F)).toRingHom.comp (completedJet M I ρ) = ρ :=
    MvPolynomial.ringHom_ext (fun b => by simp [completedJet, coeffJet])
      (fun j => by simp [completedJet])
  exact RingHom.congr_fun this f

variable [Algebra (MvPolynomial (σ ⊕ μ) R₀) (MvPolynomial μ (AdicCompletion I A₀))]
  (hB₁ : ∀ p, algebraMap (MvPolynomial (σ ⊕ μ) R₀) (MvPolynomial μ (AdicCompletion I A₀))
    (rename Sum.inl p) = C (algebraMap A₀ _ (algebraMap _ A₀ p)))
  (hB₂ : ∀ j, algebraMap (MvPolynomial (σ ⊕ μ) R₀) (MvPolynomial μ (AdicCompletion I A₀))
    (X (Sum.inr j)) = X j)

include hB₁ hB₂ in
theorem completedJet_snd_algebraMap (g : MvPolynomial (σ ⊕ μ) R₀) :
    (completedJet M I ρ (algebraMap _ _ g)).snd =
      fun v => ρ (algebraMap _ (MvPolynomial μ (AdicCompletion I A₀)) (pderiv v g)) := by
  set κ := ρ.comp (algebraMap (MvPolynomial (σ ⊕ μ) R₀) (MvPolynomial μ (AdicCompletion I A₀)))
  have hcoeff : ∀ p : MvPolynomial σ R₀, completedJet M I ρ (algebraMap _ _ (rename Sum.inl p)) =
      coeffJet M I ρ (algebraMap A₀ _ (algebraMap _ A₀ p)) := fun p => by
    rw [hB₁, completedJet, eval₂Hom_C]
  have : (completedJet M I ρ).comp (algebraMap _ _) = pderivJet κ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun v => ?_)
    · refine TrivSqZeroExt.ext (by simp [completedJet_fst, pderivJet, κ]) ?_
      have h := hcoeff (C a)
      rw [rename_C] at h
      rw [RingHom.comp_apply, h]
      funext v
      rcases v with i | j
      · simp [coeffJet, pderivJet, hatDeriv_inl_algebraMap]
      · simp [coeffJet, pderivJet, hatDeriv]
    · refine TrivSqZeroExt.ext (by simp [completedJet_fst, pderivJet, κ]) ?_
      funext w
      simp only [pderivJet, jetHom_snd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_pderiv_X]
      rcases v with i | j
      · have h := hcoeff (X i)
        rw [rename_X] at h
        rw [RingHom.comp_apply, h]
        rcases w with i' | j'
        · simp only [coeffJet, jetHom_snd, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
            hatDeriv_inl_algebraMap]
          have := map_pderiv_X ((ρ.comp C).comp ((algebraMap A₀ (AdicCompletion I A₀)).comp
            (algebraMap (MvPolynomial σ R₀) A₀))) i' i
          simp only [RingHom.comp_apply] at this
          rw [this]
          simp [Pi.single_apply]
        · simp [coeffJet, hatDeriv]
      · rw [RingHom.comp_apply, hB₂]
        simp [completedJet]
  have h := congrArg TrivSqZeroExt.snd (RingHom.congr_fun this g)
  exact h

include M hB₁ hB₂ in
/-- **Regularity of fibres of completed polynomial extensions.** Let `A₀` be a localization of
`R₀[X_σ]` over a Noetherian ring `R₀`, `I` an ideal of `A₀`, and suppose `Â₀[Y_μ]` is regular,
where `Â₀` is the `I`-adic completion, viewed as an `R₀[X_σ, Y_μ]`-algebra by `X_i ↦ X_i`,
`Y_j ↦ Y_j`. Then its fibre over every prime `N` of `R₀[X_σ, Y_μ]` whose residue field is formally
smooth over `R₀` is regular. -/
theorem isRegularRing_fiber_completedPolynomial [Fintype σ] [Fintype μ] [IsNoetherianRing R₀]
    [IsRegularRing (MvPolynomial μ (AdicCompletion I A₀))]
    (N : Ideal (MvPolynomial (σ ⊕ μ) R₀)) [N.IsPrime]
    [Algebra.FormallySmooth R₀ N.ResidueField] :
    IsRegularRing (N.Fiber (MvPolynomial μ (AdicCompletion I A₀))) :=
  isRegularRing_fiber_of_jacobian N
    (fun r _ => completedJet M I (algebraMap _ r.ResidueField))
    (fun _ _ b => completedJet_fst M I _ b)
    (fun _ _ g => completedJet_snd_algebraMap M I _ hB₁ hB₂ g)

end Completion

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing
