import Langlands.Representation.Intertwining.PQFiniteActionRegularity
import Langlands.Representation.Intertwining.PQIntertwiningOperatorProof
import Langlands.Representation.Exponents.FiniteActionSpectrumProof

/-! # Finite action quotients of central subgroups -/

noncomputable section

namespace Langlands.CentralActionQuotient

open PQFiniteActionRegularity

variable {B : Type*} [CommGroup B]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A jointly injective family of equivariant maps `ρ → σ` puts the action kernel of `σ`
inside the action kernel of `ρ`. -/
theorem groupAlgebraKernel_le_of_jointlyInjective {X : Type*}
    (ρ : Representation ℂ B V) (σ : Representation ℂ B W)
    (F : X → ρ.IntertwiningMap σ) (hF : ∀ v : V, (∀ x, F x v = 0) → v = 0) :
    groupAlgebraKernel σ (MonoidHom.id B) ≤ groupAlgebraKernel ρ (MonoidHom.id B) := by
  intro c hc
  rw [mem_groupAlgebraKernel_iff] at hc ⊢
  apply LinearMap.ext
  intro v
  apply hF
  intro x
  rw [intertwining_groupAlgebra_apply (F x) (MonoidHom.id B) c v, hc]
  rfl

/-- A larger action kernel has a smaller action quotient. -/
theorem finite_actionQuotient_of_kernel_le
    (ρ : Representation ℂ B V) (σ : Representation ℂ B W)
    (h : groupAlgebraKernel ρ (MonoidHom.id B) ≤ groupAlgebraKernel σ (MonoidHom.id B))
    [Module.Finite ℂ (actionQuotient ρ)] :
    Module.Finite ℂ (actionQuotient σ) :=
  Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ h).toLinearMap
    (Ideal.Quotient.factor_surjective h)

/-- An action through scalars has a finite action quotient. -/
theorem finite_actionQuotient_of_scalar (ρ : Representation ℂ B V) (c : B → ℂ)
    (hc : ∀ b, ρ b = c b • (1 : Module.End ℂ V)) :
    Module.Finite ℂ (actionQuotient ρ) := by
  have hle : Submodule.span ℂ (Set.range ρ) ≤ Submodule.span ℂ {(1 : Module.End ℂ V)} := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [hc b]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have : Module.Finite ℂ (Submodule.span ℂ (Set.range ρ)) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact finite_actionQuotient_of_finite_span ρ

/-- An action through scalars has at most the scalar character as generalized character. -/
theorem eq_of_isGeneralizedEigencharacter_of_scalar (ρ : Representation ℂ B V)
    (c : B →* ℂˣ) (hc : ∀ b, ρ b = (c b : ℂ) • (1 : Module.End ℂ V))
    (χ : B →* ℂˣ) (hχ : IsGeneralizedEigencharacter ρ χ) : χ = c := by
  obtain ⟨k, v, hv, h⟩ := (isGeneralizedEigencharacter_iff ρ χ).mp hχ
  ext b
  have hb := h b
  rw [hc b, ← sub_smul, smul_pow, LinearMap.smul_apply, one_pow,
    Module.End.one_apply] at hb
  have hpow : ((c b : ℂ) - (χ b : ℂ)) ^ k = 0 := by
    by_contra hne
    exact hv ((smul_eq_zero.mp hb).resolve_left hne)
  exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)).symm

/-- A finite action quotient admits only finitely many generalized characters. -/
theorem finite_generalizedEigencharacters (ρ : Representation ℂ B V)
    [Module.Finite ℂ (actionQuotient ρ)] :
    {χ : B →* ℂˣ | IsGeneralizedEigencharacter ρ χ}.Finite := by
  let I := groupAlgebraKernel ρ (MonoidHom.id B)
  let Φ : {χ : B →* ℂˣ | IsGeneralizedEigencharacter ρ χ} → (actionQuotient ρ →ₐ[ℂ] ℂ) :=
    fun χ => Ideal.Quotient.liftₐ I (PQKernelCharacters.characterAlgebraHom χ.val)
      (fun c hc => RingHom.mem_ker.mp
        (PQKernelCharacters.kernel_le_characterKernel ρ χ.val χ.property hc))
  have hΦ : Function.Injective Φ := by
    intro χ₁ χ₂ h
    apply Subtype.ext
    ext b
    have hb : PQKernelCharacters.characterAlgebraHom χ₁.val (MonoidAlgebra.of ℂ B b) =
        PQKernelCharacters.characterAlgebraHom χ₂.val (MonoidAlgebra.of ℂ B b) :=
      congrArg (fun φ => φ (Ideal.Quotient.mk I (MonoidAlgebra.of ℂ B b))) h
    simpa [PQKernelCharacters.characterAlgebraHom] using hb
  have : Finite (actionQuotient ρ →ₐ[ℂ] ℂ) := FiniteActionSpectrum.finite_algHom
  have : Finite {χ : B →* ℂˣ | IsGeneralizedEigencharacter ρ χ} := Finite.of_injective Φ hΦ
  exact Set.toFinite _

variable {H : Type*} [Group H]

/-- A finitely generated representation on which a central subgroup acts locally finitely
has a finite action quotient for that subgroup. -/
theorem finite_actionQuotient_of_locallyFinite (ρ : Representation ℂ H V) (ι : B →* H)
    (hι : ∀ b, ι b ∈ Subgroup.center H)
    (hloc : ∀ v : V, ∃ U : Subrepresentation (ρ.comp ι), Module.Finite ℂ U.toSubmodule ∧ v ∈ U)
    [Module.Finite (MonoidAlgebra ℂ H) ρ.asModule] :
    Module.Finite ℂ (actionQuotient (ρ.comp ι)) := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := MonoidAlgebra ℂ H) (M := ρ.asModule)
  choose U hUfin hUmem using hloc
  let U₀ : Subrepresentation (ρ.comp ι) := S.sup fun s => U (ρ.asModuleEquiv s)
  have hsup : ∀ T : Finset ρ.asModule, (T.sup fun s => U (ρ.asModuleEquiv s)).toSubmodule =
      T.sup fun s => (U (ρ.asModuleEquiv s)).toSubmodule := by
    intro T
    induction T using Finset.induction_on with
    | empty => rfl
    | insert s T hs ih =>
      rw [Finset.sup_insert, Finset.sup_insert, Subrepresentation.toSubmodule_sup, ih]
  have hU₀ : U₀.toSubmodule = S.sup fun s => (U (ρ.asModuleEquiv s)).toSubmodule := hsup S
  have hfin : Module.Finite ℂ U₀.toSubmodule := by
    rw [Module.Finite.iff_fg, hU₀]
    exact Submodule.fg_finset_sup S _ fun s _ => Module.Finite.iff_fg.mp (hUfin _)
  have hmem : ∀ s ∈ S, ρ.asModuleEquiv s ∈ U₀ := by
    intro s hs
    have h₁ : U (ρ.asModuleEquiv s) ≤ U₀ := Finset.le_sup (f := fun s => U (ρ.asModuleEquiv s)) hs
    exact h₁ (hUmem _)
  let incl : U₀.toRepresentation.IntertwiningMap (ρ.comp ι) :=
    { toLinearMap := U₀.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let Ψ := Representation.asAlgebraHom U₀.toRepresentation
  have hker : groupAlgebraKernel (ρ.comp ι) (MonoidHom.id B) = RingHom.ker Ψ := by
    ext c
    rw [mem_groupAlgebraKernel_iff, RingHom.mem_ker]
    constructor
    · intro hc
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      have := intertwining_groupAlgebra_apply incl (MonoidHom.id B) c w
      change (incl (Representation.asAlgebraHom (U₀.toRepresentation.comp (MonoidHom.id B))
        c w)) = _ at this
      change incl (Ψ c w) = 0
      rw [show Ψ = Representation.asAlgebraHom
        (U₀.toRepresentation.comp (MonoidHom.id B)) from rfl, this, hc]
      rfl
    · intro hc
      let X := centralGroupAlgebraAction ρ ι hι c
      let Xm := Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ X
      have hS' : (S : Set ρ.asModule) ⊆ LinearMap.ker Xm := by
        intro s hs
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        have h₁ := intertwining_groupAlgebra_apply incl (MonoidHom.id B) c
          ⟨ρ.asModuleEquiv s, hmem s hs⟩
        have h₂ : Ψ c = 0 := hc
        change incl (Representation.asAlgebraHom
          (U₀.toRepresentation.comp (MonoidHom.id B)) c _) = _ at h₁
        rw [show Representation.asAlgebraHom (U₀.toRepresentation.comp (MonoidHom.id B)) =
          Ψ from rfl, h₂] at h₁
        exact h₁.symm.trans rfl
      have htop : LinearMap.ker Xm = ⊤ := by
        rw [eq_top_iff, ← hS, Submodule.span_le]
        exact hS'
      apply LinearMap.ext
      intro v
      have := (LinearMap.mem_ker (f := Xm)).mp (htop ▸ Submodule.mem_top (x := ρ.asModuleEquiv.symm v))
      exact this
  let ι' : MonoidAlgebra ℂ B ⧸ RingHom.ker Ψ →ₐ[ℂ] Module.End ℂ U₀.toSubmodule :=
    Ideal.kerLiftAlg Ψ
  have : Module.Finite ℂ (MonoidAlgebra ℂ B ⧸ RingHom.ker Ψ) :=
    Module.Finite.of_injective ι'.toLinearMap (Ideal.kerLiftAlg_injective Ψ)
  exact Module.Finite.of_surjective
    (Ideal.quotientEquivAlgOfEq ℂ hker.symm).toLinearMap
    (Ideal.quotientEquivAlgOfEq ℂ hker.symm).surjective

end Langlands.CentralActionQuotient
