import Langlands.Automorphic.OperatorScalarCentralCharacter
import Langlands.Automorphic.OperatorRealizationCountable
import Langlands.Algebra.SchurProof
import Langlands.Automorphic.IrreducibleCentralCharacterStatement

/-! # Central characters of irreducible operator realizations

An irreducible actual operator realization `S` of `GL_n` over a number field has countable
complex dimension, so by Schur's lemma every operator commuting with the operator algebra
is a scalar. The scalar matrices at finite places commute with all operators, so they act
by scalars. Fixing a nonzero function `f₀` and a point `x₀` where it does not vanish, the
ideles whose scalar matrices act by the ratio of the values of `f₀` at `z x₀` and `x₀` form
a closed subgroup containing the principal ideles and every local finite unit group; by
idele density it is the whole idele group. The ratio is then a continuous character trivial
on principal ideles, and it is the unique central character of `S`.
-/

noncomputable section
universe uF

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL ContinuousRationalFunctions
open scoped NumberField

variable {F : Type uF} [Field F] [NumberField F]

local instance irreducibleCentralRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance irreducibleCentralContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance irreducibleCentralSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance irreducibleCentralFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance irreducibleCentralStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance irreducibleCentralRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable {n : ℕ} (S : OperatorRealization F n)

/-- A linear operator commuting with the three generating operator families commutes with
the whole operator algebra. -/
theorem commute_representation_of_commute (A : S.Space →ₗ[ℂ] S.Space)
    (hd : ∀ (d : FiniteAdelicGL F n) (f : S.Space),
      A (S.finiteRepresentation d f) = S.finiteRepresentation d (A f))
    (hk : ∀ (k : standardInfiniteCompact F n) (f : S.Space),
      A (S.compactRepresentation k f) = S.compactRepresentation k (A f))
    (he : ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space),
      A (S.envelopingAction u f) = S.envelopingAction u (A f))
    (a : automorphicOperatorAlgebra F n) :
    ∀ f : S.Space, A (S.representation a f) = S.representation a (A f) := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction with
  | mem b hb =>
    rcases hb with (⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · exact hd d
    · exact hk k
    · exact he u
  | algebraMap c =>
    intro f
    have h : ∀ g : S.Space,
        S.representation ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c⟩ g = c • g :=
      fun g => rfl
    exact (congrArg A (h f)).trans ((A.map_smul c f).trans (h (A f)).symm)
  | add b₁ b₂ h₁ h₂ ih₁ ih₂ =>
    intro f
    have h : ∀ g : S.Space, S.representation ⟨b₁ + b₂, Subalgebra.add_mem _ h₁ h₂⟩ g =
        S.representation ⟨b₁, h₁⟩ g + S.representation ⟨b₂, h₂⟩ g := fun g => rfl
    exact (congrArg A (h f)).trans ((A.map_add _ _).trans
      ((congrArg₂ (· + ·) (ih₁ f) (ih₂ f)).trans (h (A f)).symm))
  | mul b₁ b₂ h₁ h₂ ih₁ ih₂ =>
    intro f
    have h : ∀ g : S.Space, S.representation ⟨b₁ * b₂, Subalgebra.mul_mem _ h₁ h₂⟩ g =
        S.representation ⟨b₁, h₁⟩ (S.representation ⟨b₂, h₂⟩ g) := fun g => rfl
    exact (congrArg A (h f)).trans ((ih₁ _).trans
      ((congrArg (S.representation ⟨b₁, h₁⟩) (ih₂ f)).trans (h (A f)).symm))

/-- Schur's lemma for an irreducible realization: an operator commuting with the operator
algebra is a scalar. -/
theorem exists_eq_smul_of_commute (hS : S.IsIrreducible) (A : S.Space →ₗ[ℂ] S.Space)
    (hA : ∀ (a : automorphicOperatorAlgebra F n) (f : S.Space),
      A (S.representation a f) = S.representation a (A f)) :
    ∃ c : ℂ, ∀ f : S.Space, A f = c • f := by
  let φ : Representation.IntertwiningMap S.representation S.representation :=
    A.intertwiningMap_of_isIntertwiningMap S.representation S.representation hA
  let ψ := Representation.IntertwiningMap.equivAlgEnd S.representation φ
  have hsimple : IsSimpleModule (MonoidAlgebra ℂ (automorphicOperatorAlgebra F n))
      S.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule S.representation).mp hS
  have hrank : Module.rank ℂ S.representation.asModule ≤ Cardinal.aleph0 := by
    rw [S.representation.asModuleEquiv.rank_eq]
    exact S.rank_le_aleph0 hS
  obtain ⟨c, hc⟩ :=
    (Langlands.Renard.schurScalarOfModuleRankCountable _ _ hsimple hrank).2 ψ
  refine ⟨c, fun f => ?_⟩
  exact (LinearMap.congr_fun hc f).symm

/-- In an irreducible realization, the scalar matrix of a unit at one finite place acts by
a scalar. -/
theorem exists_localScalar_eq_smul (hS : S.IsIrreducible) (v : FinitePlace F)
    (a : (FiniteCompletion F v)ˣ) :
    ∃ c : ℂ, ∀ f : S.Space,
      S.finiteRepresentation (localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a))
        f = c • f := by
  set e := localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a)
  have hcomm : ∀ d : FiniteAdelicGL F n, e * d = d * e := fun d =>
    (localInclusion_scalar_commute F n v a d).eq
  refine S.exists_eq_smul_of_commute hS (S.finiteRepresentation e)
    (S.commute_representation_of_commute _ ?_ ?_ ?_)
  · intro d f
    calc S.finiteRepresentation e (S.finiteRepresentation d f)
        = S.finiteRepresentation (e * d) f := S.finiteRepresentation_mul_apply e d f
      _ = S.finiteRepresentation (d * e) f :=
          congrArg (fun y => S.finiteRepresentation y f) (hcomm d)
      _ = S.finiteRepresentation d (S.finiteRepresentation e f) :=
          (S.finiteRepresentation_mul_apply d e f).symm
  · intro k f
    exact S.finiteRepresentation_compactRepresentation e k f
  · intro u f
    exact S.finiteRepresentation_envelopingAction e u f

/-- In an irreducible realization, left translation by the scalar matrix of a local idele at
a finite place is multiplication by a constant. -/
theorem exists_scalar_finiteIdeleInclusion (hS : S.IsIrreducible) (v : FinitePlace F)
    (a : (FiniteCompletion F v)ˣ) :
    ∃ c : ℂ, ∀ (f : S.Space) (x : AdelicGL F n),
      evaluate F n (S.toContinuous f) (AdelicGL.scalar F n (finiteIdeleInclusion F v a) * x) =
        c * evaluate F n (S.toContinuous f) x := by
  obtain ⟨c, hc⟩ := S.exists_localScalar_eq_smul hS v a
  exact ⟨c, fun f x => (S.evaluate_scalar_finiteIdeleInclusion v a f x).trans
    ((congrArg (fun g => evaluate F n (S.toContinuous g) x) (hc f)).trans
      (S.evaluate_toContinuous_smul c f x))⟩

/-- Left translation by the scalar matrix of a principal idele is the identity. -/
theorem exists_scalar_diagonalUnits (a : Fˣ) :
    ∃ c : ℂ, ∀ (f : S.Space) (x : AdelicGL F n),
      evaluate F n (S.toContinuous f) (AdelicGL.scalar F n (diagonalUnits F a) * x) =
        c * evaluate F n (S.toContinuous f) x := by
  refine ⟨1, fun f x => ?_⟩
  rw [AdelicGL.scalar_diagonalUnits, evaluate_rational, one_mul]

/-- The ratio of the values of `f₀` at `z x₀` and at `x₀`, for the scalar matrix of the
idele `z`. -/
def scalarRatio (f₀ : S.Space) (x₀ : AdelicGL F n) (z : Ideles F) : ℂ :=
  evaluate F n (S.toContinuous f₀) (AdelicGL.scalar F n z * x₀) /
    evaluate F n (S.toContinuous f₀) x₀

theorem continuous_scalarRatio (f₀ : S.Space) (x₀ : AdelicGL F n) :
    Continuous (S.scalarRatio f₀ x₀) :=
  ((continuous_evaluate F n _).comp
    ((AdelicGL.scalar F n).continuous.mul continuous_const)).div_const _

/-- The scalar matrix of `z` acts on the functions of `S` by left multiplication through
the ratio `scalarRatio f₀ x₀ z`. -/
def ScalarActsByRatio (f₀ : S.Space) (x₀ : AdelicGL F n) (z : Ideles F) : Prop :=
  ∀ (f : S.Space) (x : AdelicGL F n),
    evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
      S.scalarRatio f₀ x₀ z * evaluate F n (S.toContinuous f) x

section Ratio

variable {S} {f₀ : S.Space} {x₀ : AdelicGL F n}

theorem scalarActsByRatio_of_exists (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0)
    {z : Ideles F} {c : ℂ}
    (hc : ∀ (f : S.Space) (x : AdelicGL F n),
      evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
        c * evaluate F n (S.toContinuous f) x) :
    S.ScalarActsByRatio f₀ x₀ z := by
  have hr : S.scalarRatio f₀ x₀ z = c :=
    calc S.scalarRatio f₀ x₀ z
        = c * evaluate F n (S.toContinuous f₀) x₀ / evaluate F n (S.toContinuous f₀) x₀ :=
          congrArg (· / evaluate F n (S.toContinuous f₀) x₀) (hc f₀ x₀)
      _ = c := mul_div_cancel_right₀ c h0
  intro f x
  exact (hc f x).trans (congrArg (· * evaluate F n (S.toContinuous f) x) hr.symm)

theorem scalarRatio_one (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) :
    S.scalarRatio f₀ x₀ 1 = 1 :=
  calc S.scalarRatio f₀ x₀ 1
      = evaluate F n (S.toContinuous f₀) x₀ / evaluate F n (S.toContinuous f₀) x₀ :=
        congrArg (fun y => evaluate F n (S.toContinuous f₀) y /
          evaluate F n (S.toContinuous f₀) x₀) (by rw [map_one, one_mul])
    _ = 1 := div_self h0

theorem scalar_mul_mul (z w : Ideles F) (x : AdelicGL F n) :
    AdelicGL.scalar F n (z * w) * x = AdelicGL.scalar F n z * (AdelicGL.scalar F n w * x) := by
  rw [map_mul, mul_assoc]

theorem scalar_mul_scalar_inv_mul (z : Ideles F) (x : AdelicGL F n) :
    AdelicGL.scalar F n z * (AdelicGL.scalar F n z⁻¹ * x) = x := by
  rw [← mul_assoc, ← map_mul (AdelicGL.scalar F n) z z⁻¹, mul_inv_cancel, map_one, one_mul]

theorem scalarRatio_mul {z : Ideles F} (hz : S.ScalarActsByRatio f₀ x₀ z) (w : Ideles F) :
    S.scalarRatio f₀ x₀ (z * w) = S.scalarRatio f₀ x₀ z * S.scalarRatio f₀ x₀ w :=
  calc S.scalarRatio f₀ x₀ (z * w)
      = evaluate F n (S.toContinuous f₀)
          (AdelicGL.scalar F n z * (AdelicGL.scalar F n w * x₀)) /
            evaluate F n (S.toContinuous f₀) x₀ :=
        congrArg (fun y => evaluate F n (S.toContinuous f₀) y /
          evaluate F n (S.toContinuous f₀) x₀) (scalar_mul_mul z w x₀)
    _ = S.scalarRatio f₀ x₀ z *
          evaluate F n (S.toContinuous f₀) (AdelicGL.scalar F n w * x₀) /
            evaluate F n (S.toContinuous f₀) x₀ :=
        congrArg (· / evaluate F n (S.toContinuous f₀) x₀) (hz f₀ _)
    _ = S.scalarRatio f₀ x₀ z * S.scalarRatio f₀ x₀ w := mul_div_assoc _ _ _

theorem scalarRatio_ne_zero (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) {z : Ideles F}
    (hz : S.ScalarActsByRatio f₀ x₀ z) : S.scalarRatio f₀ x₀ z ≠ 0 := by
  intro hzero
  have h := hz f₀ (AdelicGL.scalar F n z⁻¹ * x₀)
  apply h0
  calc evaluate F n (S.toContinuous f₀) x₀
      = evaluate F n (S.toContinuous f₀)
          (AdelicGL.scalar F n z * (AdelicGL.scalar F n z⁻¹ * x₀)) :=
        (congrArg (evaluate F n (S.toContinuous f₀)) (scalar_mul_scalar_inv_mul z x₀)).symm
    _ = S.scalarRatio f₀ x₀ z *
          evaluate F n (S.toContinuous f₀) (AdelicGL.scalar F n z⁻¹ * x₀) := h
    _ = 0 := (congrArg (· * _) hzero).trans (zero_mul _)

theorem scalarActsByRatio_one (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) :
    S.ScalarActsByRatio f₀ x₀ 1 :=
  scalarActsByRatio_of_exists h0 (c := 1) fun f x =>
    calc evaluate F n (S.toContinuous f) (AdelicGL.scalar F n 1 * x)
        = evaluate F n (S.toContinuous f) x :=
          congrArg (evaluate F n (S.toContinuous f)) (by rw [map_one, one_mul])
      _ = 1 * evaluate F n (S.toContinuous f) x := (one_mul _).symm

theorem scalarActsByRatio_mul (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) {z w : Ideles F}
    (hz : S.ScalarActsByRatio f₀ x₀ z) (hw : S.ScalarActsByRatio f₀ x₀ w) :
    S.ScalarActsByRatio f₀ x₀ (z * w) :=
  scalarActsByRatio_of_exists h0 (c := S.scalarRatio f₀ x₀ z * S.scalarRatio f₀ x₀ w)
    fun f x =>
      calc evaluate F n (S.toContinuous f) (AdelicGL.scalar F n (z * w) * x)
          = evaluate F n (S.toContinuous f)
              (AdelicGL.scalar F n z * (AdelicGL.scalar F n w * x)) :=
            congrArg (evaluate F n (S.toContinuous f)) (scalar_mul_mul z w x)
        _ = S.scalarRatio f₀ x₀ z *
              (S.scalarRatio f₀ x₀ w * evaluate F n (S.toContinuous f) x) :=
            (hz f _).trans (congrArg (S.scalarRatio f₀ x₀ z * ·) (hw f x))
        _ = _ := (mul_assoc _ _ _).symm

theorem scalarActsByRatio_inv (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) {z : Ideles F}
    (hz : S.ScalarActsByRatio f₀ x₀ z) : S.ScalarActsByRatio f₀ x₀ z⁻¹ := by
  have hne := scalarRatio_ne_zero h0 hz
  refine scalarActsByRatio_of_exists h0 (c := (S.scalarRatio f₀ x₀ z)⁻¹) fun f x => ?_
  have h : evaluate F n (S.toContinuous f) x = S.scalarRatio f₀ x₀ z *
      evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z⁻¹ * x) :=
    (congrArg (evaluate F n (S.toContinuous f)) (scalar_mul_scalar_inv_mul z x)).symm.trans
      (hz f _)
  exact (inv_mul_cancel_left₀ hne _).symm.trans (congrArg _ h.symm)

variable (S f₀ x₀) in
/-- The ideles whose scalar matrices act through `scalarRatio f₀ x₀`. -/
def ratioSubgroup (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) : Subgroup (Ideles F) where
  carrier := {z | S.ScalarActsByRatio f₀ x₀ z}
  one_mem' := scalarActsByRatio_one h0
  mul_mem' := fun hz hw => scalarActsByRatio_mul h0 hz hw
  inv_mem' := fun hz => scalarActsByRatio_inv h0 hz

theorem isClosed_ratioSubgroup (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) :
    IsClosed (ratioSubgroup S f₀ x₀ h0 : Set (Ideles F)) := by
  have h : (ratioSubgroup S f₀ x₀ h0 : Set (Ideles F)) =
      ⋂ (f : S.Space) (x : AdelicGL F n), {z : Ideles F |
        evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
          S.scalarRatio f₀ x₀ z * evaluate F n (S.toContinuous f) x} := by
    ext z
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun f => isClosed_iInter fun x => isClosed_eq ?_ ?_
  · exact (continuous_evaluate F n _).comp ((AdelicGL.scalar F n).continuous.mul continuous_const)
  · exact (S.continuous_scalarRatio f₀ x₀).mul continuous_const

end Ratio

/-- In an irreducible realization, every idele acts through `scalarRatio f₀ x₀`, when `f₀`
does not vanish at `x₀`. -/
theorem scalarActsByRatio_of_irreducible (hS : S.IsIrreducible) {f₀ : S.Space}
    {x₀ : AdelicGL F n} (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) (z : Ideles F) :
    S.ScalarActsByRatio f₀ x₀ z := by
  have htop : ratioSubgroup S f₀ x₀ h0 = ⊤ :=
    IdeleDensity.eq_top_of_isClosed (ratioSubgroup S f₀ x₀ h0) ∅ (isClosed_ratioSubgroup h0)
      (fun a => scalarActsByRatio_of_exists h0 (S.exists_scalar_diagonalUnits a).choose_spec)
      (fun v _ a => scalarActsByRatio_of_exists h0
        (S.exists_scalar_finiteIdeleInclusion hS v a).choose_spec)
  have hz : z ∈ ratioSubgroup S f₀ x₀ h0 := by
    rw [htop]
    exact Subgroup.mem_top z
  exact hz

/-- A nonzero function in an irreducible realization does not vanish at some point. -/
theorem exists_evaluate_ne_zero (hS : S.IsIrreducible) :
    ∃ (f₀ : S.Space) (x₀ : AdelicGL F n), evaluate F n (S.toContinuous f₀) x₀ ≠ 0 := by
  have hnt : Nontrivial (Subrepresentation S.representation) := hS.toNontrivial
  obtain ⟨f₀, hf₀⟩ : ∃ f : S.Space, f ≠ 0 := by
    by_contra! h
    apply (bot_ne_top : (⊥ : Subrepresentation S.representation) ≠ ⊤)
    apply Subrepresentation.ext
    change (⊥ : Submodule ℂ S.Space) = ⊤
    rw [eq_comm, eq_bot_iff]
    intro x _
    exact (Submodule.mem_bot ℂ).mpr (h x)
  refine ⟨f₀, ?_⟩
  by_contra! h
  apply hf₀
  apply S.toContinuous_injective
  rw [map_zero]
  apply toContinuousMap_injective F n
  rw [map_zero]
  ext x
  exact h x

/-- **Central characters of irreducible realizations.** An irreducible actual operator
realization has exactly one central character. -/
theorem existsUnique_hasCentralCharacter (hS : S.IsIrreducible) :
    ∃! χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ, S.HasCentralCharacter χ := by
  obtain ⟨f₀, x₀, h0⟩ := S.exists_evaluate_ne_zero hS
  have hall := S.scalarActsByRatio_of_irreducible hS h0
  let r : Ideles F →* ℂ :=
    { toFun := S.scalarRatio f₀ x₀
      map_one' := scalarRatio_one h0
      map_mul' := fun z w => scalarRatio_mul (hall z) w }
  let ψ : Ideles F →* ℂˣ := r.toHomUnits
  have hψ : ∀ z, ((ψ z : ℂˣ) : ℂ) = S.scalarRatio f₀ x₀ z := fun z => rfl
  have hψc : Continuous ψ :=
    Units.isEmbedding_val₀.continuous_iff.mpr (S.continuous_scalarRatio f₀ x₀)
  let χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ :=
    { toMonoidHom := QuotientGroup.lift (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F) ψ (by
        rintro _ ⟨a, rfl⟩
        apply Units.ext
        rw [hψ, Units.val_one]
        have h := hall (diagonalUnits F a) f₀ x₀
        rw [AdelicGL.scalar_diagonalUnits, evaluate_rational] at h
        exact (mul_eq_right₀ h0).mp h.symm)
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
          hψc }
  have hχ : ∀ z : Ideles F, (centralIdeleCharacter F χ z : ℂ) = S.scalarRatio f₀ x₀ z :=
    fun z => rfl
  have huniq : ∀ χ' : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ, S.HasCentralCharacter χ' →
      ∀ z : Ideles F, (centralIdeleCharacter F χ' z : ℂ) = S.scalarRatio f₀ x₀ z := by
    intro χ' hχ' z
    have h := S.centralCharacter_evaluate χ' hχ' f₀ z x₀
    rw [scalarRatio, h, mul_div_assoc, div_self h0, mul_one]
  refine ⟨χ, ?_, ?_⟩
  · apply S.hasCentralCharacter_of_centralCharacterSubgroup_eq_top χ
    rw [eq_top_iff]
    intro z _
    refine (S.mem_centralCharacterSubgroup χ z).mpr fun f x => ?_
    rw [hχ]
    exact hall z f x
  · intro χ' hχ'
    ext q
    induction q using QuotientGroup.induction_on with
    | H z =>
      change (centralIdeleCharacter F χ' z : ℂ) = (centralIdeleCharacter F χ z : ℂ)
      rw [huniq χ' hχ' z, hχ]

end OperatorRealization

/-- **Central characters of irreducible realizations**
(Borel–Jacquet 1979, 4.3(iv) and 4.6, with Schur's lemma): every irreducible actual
operator realization of `GL_n` over a number field has exactly one central character. -/
theorem OperatorRealization.irreducibleCentralCharacter :
    OperatorRealization.IrreducibleCentralCharacterStatement.{uF} := by
  intro F _ _ n S hS
  exact S.existsUnique_hasCentralCharacter hS

end Langlands.Automorphic
