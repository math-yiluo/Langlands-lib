import Langlands.Representation.Archimedean.RealSubquotientMain
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible

/-!
# Harish-Chandra's subquotient theorem for `GL_n(ℝ)`

Proof of `Langlands.Archimedean.RealPrincipalSeriesSubquotientStatement`: every irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module is a quotient of a stable space of `O(n)`-finite functions
in a principal series of `GL_n(ℝ)`. The argument is Lepowsky's (Wallach, *Real reductive groups
I*, §3.5), with the Harish-Chandra homomorphism replaced by the principal series themselves; see
the helper modules `RealSubquotientEval`, `RealSubquotientProjection`, `RealSubquotientSymbol`,
`RealSubquotientFinite`, `RealSubquotientAverage`, `RealSubquotientKType`, `RealSubquotientMain`.
-/

noncomputable section

open scoped Matrix TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

namespace RealSubquotient

open InfinitesimalCharacter

theorem act_sum_right {n d : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (P : UU n →ₐ[ℂ] Module.End ℂ M) (b : Matrix (Fin d) (Fin d) (UU n)) {ι : Type*}
    (s : Finset ι) (T : ι → (Fin d → ℂ) →ₗ[ℂ] M) :
    act P b (∑ r ∈ s, T r) = ∑ r ∈ s, act P b (T r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [act_zero_right]
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.sum_insert hr, act_add_right, ih]

/-- A finite-dimensional space of `K`-intertwiners is spanned by finitely many intertwiners. -/
theorem exists_spanning_intertwiners {K : Type*} [Group K] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ K V) (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ)
    (h : FiniteDimensional ℂ (gkIntertwiners ρ d τ)) :
    ∃ (m : ℕ) (ω : Fin m → (Fin d → ℂ) →ₗ[ℂ] V), (∀ r, ω r ∈ gkIntertwiners ρ d τ) ∧
      ∀ T ∈ gkIntertwiners ρ d τ, ∃ c : Fin m → ℂ, T = ∑ r, c r • ω r := by
  set B := Module.finBasis ℂ (gkIntertwiners ρ d τ)
  refine ⟨_, fun r => (B r : (Fin d → ℂ) →ₗ[ℂ] V), fun r => (B r).2, fun T hT =>
    ⟨B.repr ⟨T, hT⟩, ?_⟩⟩
  have := congrArg Subtype.val (B.sum_repr ⟨T, hT⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  exact this.symm

end RealSubquotient

open RealSubquotient InfinitesimalCharacter in
/-- **Harish-Chandra's subquotient theorem for `GL_n(ℝ)`.** -/
theorem realPrincipalSeriesSubquotient : RealPrincipalSeriesSubquotientStatement.{uV} := by
  intro n V _ _ ρ π hgk hirr hadm
  classical
  have : Nontrivial V := hirr.1
  obtain ⟨d, τ, D, T0, hτ, hD, hT0, hT0ne, hd⟩ := exists_ktype hgk
  have hinf := InfinitesimalCharacter.realGKModuleInfinitesimalCharacter n V ρ π hgk hirr hadm
  choose lam hlam using fun l => hinf (Cgel n l) (Cgel_mem_center l)
  have hfin := finite_fibre (fun l _ => xiPoly_Cgel_top hτ hD hd l) lam
  set Zf := hfin.toFinset
  choose m ω0 hω0 hspan using fun s : (Fin n → ℂ) × (Fin n → Fin 2) =>
    exists_spanning_intertwiners (realStandardRep n (psList s.1 s.2)) d τ
      (realStandardAdmissible n (psList s.1 s.2) d τ hτ)
  let ι := Σ s : (Fin n → ℂ) × (Fin n → Fin 2), Fin (m s)
  let F : Finset ι := (Zf ×ˢ Finset.univ).sigma fun _ => Finset.univ
  let Ms : ι → Type := fun i => PS i.1.1 i.1.2
  let P : ∀ i : ι, UU n →ₐ[ℂ] Module.End ℂ (Ms i) := fun i => psAct i.1.1 i.1.2
  let ω : ∀ i : ι, (Fin d → ℂ) →ₗ[ℂ] Ms i := fun i => ω0 i.1 i.2
  have hρPv : ∀ k u, ρ k * envelopingAction π u = envelopingAction π (AdU k u) * ρ k :=
    fun k u => rho_mul_envelopingAction hgk.2.2.2 k u
  have hkill : ∀ b ∈ Bsub τ, (∀ i ∈ F, act (P i) b (ω i) = 0) →
      act (envelopingAction π) b T0 = 0 := by
    intro b hb hbF
    refine act_T0_eq_zero_of_kill hτ hD hd hgk hirr lam hlam hT0 hT0ne hb
      fun a ha e T hT => ?_
    have haZ : a ∈ Zf := hfin.mem_toFinset.2 ha
    obtain ⟨c, rfl⟩ := hspan (a, e) T hT
    rw [act_sum_right]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [act_smul_right]
    have := hbF ⟨(a, e), r⟩ (Finset.mem_sigma.2 ⟨Finset.mem_product.2 ⟨haZ, Finset.mem_univ _⟩,
      Finset.mem_univ _⟩)
    rw [show act (psAct a e) b (ω0 (a, e) r) = 0 from this, smul_zero]
  have hsimple : ∀ b ∈ Bsub τ, act (envelopingAction π) b T0 ≠ 0 →
      ∃ b' ∈ Bsub τ, act (envelopingAction π) (b' * b) T0 = T0 := by
    intro b hb hne
    have hbT0 := act_mem (envelopingAction π) hρPv hb hT0
    obtain ⟨c, hc⟩ := exists_act_eq_of_irreducible hgk hirr hbT0 hne (T' := T0)
    exact ⟨avg τ c, avg_mem_Bsub hτ c, by
      rw [act_mul]; exact act_avg hτ (envelopingAction π) hρPv hbT0 hT0 hc⟩
  obtain ⟨⟨⟨a, e⟩, r⟩, -, c, hc, hic⟩ :=
    exists_single_kill F P ω (envelopingAction π) T0 hT0ne hkill hsimple
  have hρPs : ∀ k u, realStandardRep n (psList a e) k * psAct a e u =
      psAct a e (AdU k u) * realStandardRep n (psList a e) k := fun k u =>
    rho_mul_envelopingAction (isRealGKModule_realStandardModule n (psList a e)).2.2.2 k u
  have hS0 := act_mem (psAct a e) hρPs hc (hω0 (a, e) r)
  obtain ⟨W, hW, T, hT, hmap⟩ := exists_subquotient_of_kill hτ hgk hirr hS0 hT0 hT0ne hic
  exact ⟨List.ofFn (RealJacquetFrobenius.chars a e), by simp, W, hW, T, hT, hmap⟩

end Langlands.Archimedean
