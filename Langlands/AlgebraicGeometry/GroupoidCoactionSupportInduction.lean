import Langlands.AlgebraicGeometry.GroupoidCoactionScalarChangeCocycle
import Langlands.AlgebraicGeometry.GroupoidCoactionInvariantRadical
import Langlands.AlgebraicGeometry.GroupoidCoactionExhaustion

/-! # Noetherian induction for finite coaction vanishing -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

/-- A property of commutative rings follows by induction on nonzero ideal
quotients of a Noetherian ring. The property need not include an explicit
invariance under ring isomorphisms. -/
theorem noetherian_quotient_induction
    (P : ∀ (S : Type u) [CommRing S], Prop)
    (hstep : ∀ (S : Type u) [CommRing S] [IsNoetherianRing S],
      (∀ (J : Ideal S), J ≠ ⊥ → P (S ⧸ J)) → P S)
    (B : Type u) [CommRing B] [IsNoetherianRing B] : P B := by
  have haux : ∀ (I : Ideal B) (S : Type u) [CommRing S] (f : B →+* S),
      Function.Surjective f → RingHom.ker f = I → P S := by
    intro I
    induction I using WellFoundedGT.induction with
    | ind I ih =>
      intro S _ f hf hI
      let : IsNoetherianRing S := isNoetherianRing_of_surjective B S f hf
      apply hstep S
      intro J hJ
      let g : B →+* S ⧸ J := (Ideal.Quotient.mk J).comp f
      have hlt : I < RingHom.ker g := by
        rw [← hI, RingHom.ker_eq_comap_bot,
          ← RingHom.comap_ker, Ideal.mk_ker]
        exact (Ideal.orderEmbeddingOfSurjective f hf).strictMono
          (bot_lt_iff_ne_bot.mpr hJ)
      exact ih (RingHom.ker g) hlt (S ⧸ J) g
        (Ideal.Quotient.mk_surjective.comp hf) rfl
  exact haux (RingHom.ker (RingHom.id B)) B (RingHom.id B) Function.surjective_id rfl

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

/-- Degree-one vanishing for every finite coefficient coaction. -/
def FiniteCoactionVanishing (t : B →+* C) : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (θ : GroupoidCoaction t M), θ.OneCohomologyVanishes

/-- Each finite coefficient coaction can be treated assuming vanishing on
modules annihilated by a nonzero invariant ideal. -/
def HasFiniteSupportVanishingStep (t : B →+* C) : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (θ : GroupoidCoaction t M),
    ∃ I : Ideal B, I ≠ ⊥ ∧ IsInvariantIdeal t I ∧
      (FiniteAnnihilatorVanishing.{u, v} t I → θ.OneCohomologyVanishes)

/-- A coefficient coaction over the zero ring has vanishing degree-one
cohomology. -/
theorem oneCohomologyVanishes_of_subsingleton [Subsingleton B]
    {M : Type v} [AddCommGroup M] [Module B M] (θ : GroupoidCoaction t M) :
    θ.OneCohomologyVanishes := by
  let : Subsingleton M := Module.subsingleton B M
  intro x hcy
  clear hcy
  refine ⟨0, ?_⟩
  have hx : x = 0 := by
    induction x with
    | tmul c m => rw [Subsingleton.elim m 0, tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  simp [hx]

/-- The reduced support step and vanishing for every nonzero invariant
quotient imply vanishing for every finite coaction. Nonreduced rings are
handled by nilradical power dévissage. -/
theorem finiteCoactionVanishing_of_quotients [IsNoetherianRing B]
    (hE : RingEtaleEquivalenceRelation t)
    (hstep : ∀ [IsReduced B] [Nontrivial B], HasFiniteSupportVanishingStep.{u, v} t)
    (hquot : ∀ (I : Ideal B), I ≠ ⊥ → ∀ hI : IsInvariantIdeal t I,
      FiniteCoactionVanishing.{u, v}
        (RingEtaleEquivalenceRelation.quotientTarget I hI.symm)) :
    FiniteCoactionVanishing.{u, v} t := by
  intro M _ _ _ θ
  rcases subsingleton_or_nontrivial B with hB | hB
  · let : Subsingleton B := hB
    exact oneCohomologyVanishes_of_subsingleton θ
  · let : Nontrivial B := hB
    by_cases hnil : nilradical B = ⊥
    · let : IsReduced B := nilradical_eq_bot_iff.mp hnil
      obtain ⟨I, hI0, hI, hfinish⟩ := hstep M θ
      exact hfinish (finiteAnnihilatorVanishing_of_quotient hE I hI (hquot I hI0 hI))
    · have hbot : IsInvariantIdeal t (⊥ : Ideal B) := by simp [IsInvariantIdeal]
      have hnilinv : IsInvariantIdeal t (nilradical B) := hbot.radical hE
      apply oneCohomologyVanishes_of_le_radical_annihilator hE (nilradical B) hnilinv
        (finiteAnnihilatorVanishing_of_quotient hE (nilradical B) hnilinv
          (hquot (nilradical B) hnil hnilinv)) θ
      exact Ideal.radical_mono bot_le

/-- Finite-coefficient vanishing implies degree-one vanishing for arbitrary
coefficient modules over a Noetherian ring. -/
theorem oneCohomologyVanishes_of_finiteCoactionVanishing [IsNoetherianRing B]
    (hE : RingEtaleEquivalenceRelation t)
    (hfinite : FiniteCoactionVanishing.{u, v} t)
    {M : Type v} [AddCommGroup M] [Module B M] (θ : GroupoidCoaction t M) :
    θ.OneCohomologyVanishes := by
  apply oneCohomologyVanishes_of_finite_subcoactions θ hE
  intro H _ θH _
  exact hfinite H θH

end Langlands.AlgebraicGeometry.GroupoidCoaction
