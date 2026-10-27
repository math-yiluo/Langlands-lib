import Langlands.Algebra.PolynomialEndomorphism
import Langlands.Algebra.RenardModuleLocalization

/-! # Localization of a linear endomorphism at the powers of `X` (Renard A.III.1, example 5) -/

universe u v x w

open Polynomial

noncomputable section

namespace Langlands.Renard.EndomorphismLocalization

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- The actual polynomial evaluation module of `a`, in which `X` acts as `a`. -/
abbrev EvalModule (a : Module.End R V) : Type v :=
  Module.AEval' a

variable (R) in
/-- The multiplicative set of powers of the polynomial variable. -/
abbrev powersX : Submonoid R[X] :=
  Submonoid.powers X

/-- The actual localization carrier `V_a`: the evaluation module localized at the powers of `X`. -/
abbrev Localized (a : Module.End R V) : Type (max u v) :=
  LocalizedModule (powersX R) (EvalModule a)

/-- The coefficient action on `V_a` is the action of constant polynomials. -/
theorem smul_eq_C_smul (a : Module.End R V) (r : R) (z : Localized a) :
    r • z = (C r : R[X]) • z :=
  (algebraMap_smul R[X] r z).symm

/-- The canonical map `ι : V → V_a`, `v ↦ v / 1`. -/
def iota (a : Module.End R V) : V →ₗ[R] Localized a :=
  ((LocalizedModule.mkLinearMap (powersX R) (EvalModule a)).restrictScalars R).comp
    (Module.AEval'.of a).toLinearMap

theorem iota_def (a : Module.End R V) :
    iota a = ((LocalizedModule.mkLinearMap (powersX R) (EvalModule a)).restrictScalars R).comp
      (Module.AEval'.of a).toLinearMap :=
  rfl

theorem iota_apply (a : Module.End R V) (v : V) :
    iota a v = LocalizedModule.mk (Module.AEval'.of a v) 1 :=
  rfl

/-- Multiplication by `X` on `V_a`, as an `R`-linear endomorphism. -/
def localizedEnd (a : Module.End R V) : Module.End R (Localized a) :=
  (algebraMap R[X] (Module.End R[X] (Localized a)) X).restrictScalars R

theorem localizedEnd_apply (a : Module.End R V) (z : Localized a) :
    localizedEnd a z = (X : R[X]) • z :=
  rfl

/-- Mathlib's division by `X` on `V_a`, as an `R`-linear endomorphism. -/
def localizedInv (a : Module.End R V) : Module.End R (Localized a) :=
  (LocalizedModule.divBy (⟨X, Submonoid.mem_powers X⟩ : powersX R)).restrictScalars R

theorem localizedInv_apply (a : Module.End R V) (z : Localized a) :
    localizedInv a z = LocalizedModule.divBy (⟨X, Submonoid.mem_powers X⟩ : powersX R) z :=
  rfl

theorem localizedEnd_localizedInv (a : Module.End R V) (z : Localized a) :
    localizedEnd a (localizedInv a z) = z :=
  ModuleLocalization.scalar_divBy (powersX R) ⟨X, Submonoid.mem_powers X⟩ z

theorem localizedInv_localizedEnd (a : Module.End R V) (z : Localized a) :
    localizedInv a (localizedEnd a z) = z :=
  ModuleLocalization.divBy_scalar (powersX R) ⟨X, Submonoid.mem_powers X⟩ z

/-- The localized endomorphism `ã` as an actual `R`-linear automorphism of `V_a`. -/
def localizedEquiv (a : Module.End R V) : Localized a ≃ₗ[R] Localized a :=
  LinearEquiv.ofLinearMap (localizedEnd a) (localizedInv a)
    (LinearMap.ext (localizedEnd_localizedInv a)) (LinearMap.ext (localizedInv_localizedEnd a))

theorem localizedEquiv_apply (a : Module.End R V) (z : Localized a) :
    localizedEquiv a z = localizedEnd a z :=
  rfl

theorem localizedEquiv_symm_apply (a : Module.End R V) (z : Localized a) :
    (localizedEquiv a).symm z = localizedInv a z :=
  rfl

theorem localizedEnd_mul_localizedInv (a : Module.End R V) :
    localizedEnd a * localizedInv a = 1 :=
  LinearMap.ext (localizedEnd_localizedInv a)

theorem localizedInv_mul_localizedEnd (a : Module.End R V) :
    localizedInv a * localizedEnd a = 1 :=
  LinearMap.ext (localizedInv_localizedEnd a)

/-- `ã` is a unit of the actual endomorphism ring, by the localization itself. -/
theorem isUnit_localizedEnd (a : Module.End R V) : IsUnit (localizedEnd a) :=
  ⟨⟨localizedEnd a, localizedInv a, localizedEnd_mul_localizedInv a,
    localizedInv_mul_localizedEnd a⟩, rfl⟩

/-- The canonical intertwining identity `ã (ι v) = ι (a v)`. -/
theorem iota_intertwines (a : Module.End R V) (v : V) :
    iota a (a v) = localizedEnd a (iota a v) := by
  rw [iota_apply, iota_apply, localizedEnd_apply, LocalizedModule.smul'_mk,
    Module.AEval'.X_smul_of]

theorem localizedEnd_pow_apply (a : Module.End R V) (n : ℕ) (z : Localized a) :
    (localizedEnd a ^ n) z = (X ^ n : R[X]) • z := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, localizedEnd_apply, smul_smul, ← pow_succ']

/-! ### Fractions with denominator a power of `X` -/

/-- The fraction `v / Xⁿ`: the actual `LocalizedModule` class of `(AEval'.of a v, Xⁿ)`. -/
def frac (a : Module.End R V) (v : V) (n : ℕ) : Localized a :=
  LocalizedModule.mk (Module.AEval'.of a v) (Submonoid.pow X n)

theorem frac_zero (a : Module.End R V) (v : V) : frac a v 0 = iota a v := by
  rw [frac, iota_apply]
  congr 1

/-- Representative formula for the `X`-action: `ã (v / Xⁿ) = a v / Xⁿ`. -/
theorem localizedEnd_frac (a : Module.End R V) (v : V) (n : ℕ) :
    localizedEnd a (frac a v n) = frac a (a v) n := by
  rw [frac, frac, localizedEnd_apply, LocalizedModule.smul'_mk, Module.AEval'.X_smul_of]

/-- Representative formula for the inverse: `ã⁻¹ (v / Xⁿ) = v / Xⁿ⁺¹`. -/
theorem localizedInv_frac (a : Module.End R V) (v : V) (n : ℕ) :
    localizedInv a (frac a v n) = frac a v (n + 1) := by
  rw [frac, frac, localizedInv_apply, ModuleLocalization.divBy_mk]
  congr 1

theorem localizedEnd_frac_succ (a : Module.End R V) (v : V) (n : ℕ) :
    localizedEnd a (frac a v (n + 1)) = frac a v n := by
  rw [← localizedInv_frac, localizedEnd_localizedInv]

/-- The source's inverse-shift reading: `v / Xⁿ = ã⁻ⁿ (ι v)`. -/
theorem frac_eq_localizedInv_pow (a : Module.End R V) (v : V) (n : ℕ) :
    frac a v n = (localizedInv a ^ n) (iota a v) := by
  induction n with
  | zero => rw [pow_zero, frac_zero]; rfl
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ← ih, localizedInv_frac]

theorem localizedEnd_pow_frac (a : Module.End R V) (v : V) (n : ℕ) :
    (localizedEnd a ^ n) (frac a v n) = iota a v := by
  rw [localizedEnd_pow_apply, frac, LocalizedModule.smul'_mk, iota_apply]
  exact LocalizedModule.mk_cancel (S := powersX R) (M := EvalModule a) (Submonoid.pow X n) _

theorem frac_add (a : Module.End R V) (v w : V) (n : ℕ) :
    frac a (v + w) n = frac a v n + frac a w n := by
  rw [frac_eq_localizedInv_pow, frac_eq_localizedInv_pow, frac_eq_localizedInv_pow, map_add,
    map_add]

theorem frac_smul (a : Module.End R V) (r : R) (v : V) (n : ℕ) :
    frac a (r • v) n = r • frac a v n := by
  rw [frac_eq_localizedInv_pow, frac_eq_localizedInv_pow, map_smul, map_smul]

/-- Every element of `V_a` is a fraction `v / Xⁿ`. -/
theorem frac_surjective (a : Module.End R V) (z : Localized a) :
    ∃ (v : V) (n : ℕ), frac a v n = z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨n, hn⟩ := s.property
    refine ⟨(Module.AEval'.of a).symm m, n, ?_⟩
    rw [frac, LinearEquiv.apply_symm_apply]
    congr 1
    exact Subtype.ext hn

/-- Equality of fractions, through the actual `LocalizedModule` relation. -/
theorem frac_eq_frac_iff (a : Module.End R V) (v w : V) (m n : ℕ) :
    frac a v m = frac a w n ↔ ∃ k : ℕ, (a ^ (k + n)) v = (a ^ (k + m)) w := by
  rw [frac, frac, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, k, rfl⟩, hk⟩
    refine ⟨k, (Module.AEval'.of a).injective ?_⟩
    simp only [Submonoid.smul_def, Submonoid.pow_apply, Module.AEval'.X_pow_smul_of,
      Module.End.smul_def, ← Module.End.mul_apply, ← pow_add] at hk
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨Submonoid.pow X k, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.pow_apply, Module.AEval'.X_pow_smul_of,
      Module.End.smul_def, ← Module.End.mul_apply, ← pow_add]
    rw [hk]

/-! ### The universal property -/

/-- Unique factorization of `(L, aL, ι)` through every invertible endomorphism of a target in the
independent universe `w`. -/
def HasUniversalProperty {L : Type x} [AddCommGroup L] [Module R L] (a : Module.End R V)
    (aL : Module.End R L) (ι : V →ₗ[R] L) : Prop :=
  ∀ (W : Type w) [AddCommGroup W] [Module R W] (b : Module.End R W), IsUnit b →
    ∀ f : V →ₗ[R] W, (∀ v, f (a v) = b (f v)) →
      ∃! g : L →ₗ[R] W, (∀ z, g (aL z) = b (g z)) ∧ g.comp ι = f

variable {W : Type w} [AddCommGroup W] [Module R W]

/-- The evaluation module of an invertible endomorphism is local for the powers of `X`. -/
theorem evalModule_isSLocal (b : Module.End R W) (hb : IsUnit b) :
    ModuleLocalization.IsSLocal (powersX R) (EvalModule b) := by
  rw [ModuleLocalization.isSLocal_iff_bijective]
  rintro ⟨_, n, rfl⟩
  have hfun : (fun m : EvalModule b => (X ^ n : R[X]) • m) =
      Module.AEval'.of b ∘ (b ^ n) ∘ (Module.AEval'.of b).symm := by
    funext m
    rw [Function.comp_apply, Function.comp_apply, ← Module.End.smul_def,
      ← Module.AEval'.X_pow_smul_of, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (Module.AEval'.of b).bijective.comp
    (((Module.End.isUnit_iff _).mp (hb.pow n)).comp (Module.AEval'.of b).symm.bijective)

/-- An intertwiner `f`, as an actual polynomial-linear map of evaluation modules. -/
def polyMap (a : Module.End R V) (b : Module.End R W) (f : V →ₗ[R] W)
    (hf : ∀ v, f (a v) = b (f v)) : EvalModule a →ₗ[R[X]] EvalModule b :=
  LinearMap.ofAEval a ((Module.AEval'.of b).toLinearMap.comp f) fun v => by
    change Module.AEval'.of b (f (a v)) = (X : R[X]) • Module.AEval'.of b (f v)
    rw [hf, Module.AEval'.X_smul_of]

theorem polyMap_of (a : Module.End R V) (b : Module.End R W) (f : V →ₗ[R] W)
    (hf : ∀ v, f (a v) = b (f v)) (v : V) :
    polyMap a b f hf (Module.AEval'.of a v) = Module.AEval'.of b (f v) :=
  rfl

/-- The factorization `g : V_a → W`, from the actual localized-module lift of `polyMap`. -/
def factor (a : Module.End R V) (b : Module.End R W) (hb : IsUnit b) (f : V →ₗ[R] W)
    (hf : ∀ v, f (a v) = b (f v)) : Localized a →ₗ[R] W :=
  (Module.AEval'.of b).symm.toLinearMap.comp
    ((ModuleLocalization.factor (powersX R) (evalModule_isSLocal b hb)
      (polyMap a b f hf)).restrictScalars R)

theorem factor_apply (a : Module.End R V) (b : Module.End R W) (hb : IsUnit b)
    (f : V →ₗ[R] W) (hf : ∀ v, f (a v) = b (f v)) (z : Localized a) :
    factor a b hb f hf z = (Module.AEval'.of b).symm
      (ModuleLocalization.factor (powersX R) (evalModule_isSLocal b hb) (polyMap a b f hf) z) :=
  rfl

theorem factor_intertwines (a : Module.End R V) (b : Module.End R W) (hb : IsUnit b)
    (f : V →ₗ[R] W) (hf : ∀ v, f (a v) = b (f v)) (z : Localized a) :
    factor a b hb f hf (localizedEnd a z) = b (factor a b hb f hf z) := by
  rw [factor_apply, factor_apply, localizedEnd_apply, map_smul, Module.AEval'.of_symm_X_smul]

theorem factor_comp_iota (a : Module.End R V) (b : Module.End R W) (hb : IsUnit b)
    (f : V →ₗ[R] W) (hf : ∀ v, f (a v) = b (f v)) :
    (factor a b hb f hf).comp (iota a) = f := by
  ext v
  rw [LinearMap.comp_apply, factor_apply, iota_apply, ← LocalizedModule.mkLinearMap_apply,
    ← LinearMap.comp_apply, ModuleLocalization.factor_comp, polyMap_of,
    LinearEquiv.symm_apply_apply]

/-- An intertwiner `g` out of `V_a` satisfies `bⁿ (g (v / Xⁿ)) = g (ι v)`. -/
theorem pow_apply_frac (a : Module.End R V) (b : Module.End R W) (g : Localized a →ₗ[R] W)
    (hg : ∀ z, g (localizedEnd a z) = b (g z)) (v : V) (n : ℕ) :
    (b ^ n) (g (frac a v n)) = g (iota a v) := by
  have key : ∀ z, g ((localizedEnd a ^ n) z) = (b ^ n) (g z) := by
    intro z
    induction n generalizing z with
    | zero => rfl
    | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, hg, pow_succ, Module.End.mul_apply]
  rw [← key, localizedEnd_pow_frac]

/-- Intertwiners out of `V_a` agreeing after `ι` are equal, as soon as `b` is injective. -/
theorem eq_of_intertwines (a : Module.End R V) (b : Module.End R W)
    (hb : Function.Injective b) (g g' : Localized a →ₗ[R] W)
    (hg : ∀ z, g (localizedEnd a z) = b (g z)) (hg' : ∀ z, g' (localizedEnd a z) = b (g' z))
    (h : g.comp (iota a) = g'.comp (iota a)) : g = g' := by
  ext z
  obtain ⟨v, n, rfl⟩ := frac_surjective a z
  have hbn : Function.Injective (b ^ n) := by
    rw [Module.End.coe_pow]
    exact hb.iterate n
  apply hbn
  rw [pow_apply_frac a b g hg, pow_apply_frac a b g' hg']
  exact LinearMap.congr_fun h v

/-- Representative formula: `g (v / Xⁿ) = b⁻ⁿ (f v)`, with `b⁻¹` an endomorphism of `W`. -/
theorem factor_frac (a : Module.End R V) (b : Module.End R W) (hb : IsUnit b)
    (f : V →ₗ[R] W) (hf : ∀ v, f (a v) = b (f v)) (v : V) (n : ℕ) :
    factor a b hb f hf (frac a v n) =
      ((hb.unit⁻¹ ^ n : (Module.End R W)ˣ) : Module.End R W) (f v) := by
  have h := pow_apply_frac a b (factor a b hb f hf) (factor_intertwines a b hb f hf) v n
  rw [← LinearMap.comp_apply (factor a b hb f hf) (iota a), factor_comp_iota] at h
  have hu : ((hb.unit⁻¹ ^ n : (Module.End R W)ˣ) : Module.End R W) * b ^ n = 1 := by
    have h1 : ((hb.unit⁻¹ ^ n : (Module.End R W)ˣ) : Module.End R W) *
        ((hb.unit ^ n : (Module.End R W)ˣ) : Module.End R W) = 1 := by
      rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    rwa [Units.val_pow_eq_pow_val hb.unit n, IsUnit.unit_spec] at h1
  rw [← h, ← Module.End.mul_apply, hu, Module.End.one_apply]

theorem factor_unique (a : Module.End R V) (b : Module.End R W) (hb : IsUnit b)
    (f : V →ₗ[R] W) (hf : ∀ v, f (a v) = b (f v)) (g : Localized a →ₗ[R] W)
    (hg : ∀ z, g (localizedEnd a z) = b (g z)) (hgf : g.comp (iota a) = f) :
    g = factor a b hb f hf :=
  eq_of_intertwines a b ((Module.End.isUnit_iff b).mp hb).injective g _ hg
    (factor_intertwines a b hb f hf) (hgf.trans (factor_comp_iota a b hb f hf).symm)

/-- The concrete pair `(V_a, ã)` with `ι` has the universal property, for every target universe. -/
theorem hasUniversalProperty (a : Module.End R V) :
    HasUniversalProperty.{u, v, max u v, w} a (localizedEnd a) (iota a) := by
  intro W _ _ b hb f hf
  exact ⟨factor a b hb f hf, ⟨factor_intertwines a b hb f hf, factor_comp_iota a b hb f hf⟩,
    fun g hg => factor_unique a b hb f hf g hg.1 hg.2⟩

/-- Renard's example 5 over an arbitrary field, with source and target universes independent:
`ã` is invertible, `ι` intertwines `a` with `ã`, and the pair has the universal property. -/
def FieldStatement : Prop :=
  ∀ (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V] (a : Module.End k V),
    IsUnit (localizedEnd a) ∧ (∀ v, iota a (a v) = localizedEnd a (iota a v)) ∧
      HasUniversalProperty.{u, v, max u v, w} a (localizedEnd a) (iota a)

theorem fieldStatement : FieldStatement.{u, v, w} := by
  intro k _ V _ _ a
  exact ⟨isUnit_localizedEnd a, iota_intertwines a, hasUniversalProperty a⟩

/-- The evaluation module is the carrier of the published polynomial-module object. -/
theorem toPolynomialObj_eq
    (A : Langlands.Algebra.PolynomialEndomorphism.EndomorphismCat.{u, v} R) :
    Langlands.Algebra.PolynomialEndomorphism.toPolynomialObj R A =
      ModuleCat.of R[X] (EvalModule (Langlands.Algebra.PolynomialEndomorphism.endomorphism R A)) :=
  rfl

end Langlands.Renard.EndomorphismLocalization
