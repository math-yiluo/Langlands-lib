import Langlands.GroupScheme.HomScheme.AdicSystem
import Langlands.GroupScheme.HomScheme.InfinitesimalSurjection
import Langlands.GroupScheme.HomScheme.FibreComparison

/-! # Successive lifting of actual adic Hom families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

/-- Equality after relative evaluation is equality after raw base change, since the
canonical pullback comparisons are isomorphisms. -/
theorem evaluate_eq_iff_baseChange_eq {S : Scheme.{u}} {H G : GroupScheme S}
    {T T' : Over S} (a : T' ⟶ T) (f g : RelativeHom H G T) :
    evaluate a f = evaluate a g ↔
      (baseChange a.left).map f = (baseChange a.left).map g := by
  constructor
  · intro hfg
    apply (cancel_mono
      (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) G).hom).mp
    rw [evaluate_comparison, evaluate_comparison, hfg]
  · intro hfg
    simp only [evaluate, Descent.pullHom, hfg]

namespace Adic

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The ring map underlying a successive adic transition. -/
abbrev transitionRingHom (n : ℕ) :
    A ⧸ I ^ (n + 1 + 1) →+* A ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factorPow I (n + 1).le_succ

theorem transitionRingHom_surjective (n : ℕ) :
    Function.Surjective (transitionRingHom I n) :=
  Ideal.Quotient.factor_surjective _

/-- Every successive adic transition has square-zero kernel. -/
theorem transitionRingHom_ker_sq (n : ℕ) :
    RingHom.ker (transitionRingHom I n) ^ 2 = ⊥ := by
  change RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := I) (n + 1).le_succ)) ^ 2 = ⊥
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  apply Ideal.map_mk_eq_bot_of_le
  exact Ideal.pow_le_pow_right (by omega : n + 1 + 1 ≤ (n + 1) * 2)

/-- Infinitesimal lifting implies surjectivity of every actual Hom restriction in an
adic tower with multiplicative-type source and smooth target. -/
theorem step_surjective_of_infinitesimal
    (hInf : MultiplicativeTypeInfinitesimalLiftStatement.{u})
    (H G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) (n : ℕ) :
    Function.Surjective (evaluate (H := H) (G := G) (transitionOver I n)) := by
  let p := transition I n
  let H' := (baseChange (quotientMap I (n + 1))).obj H
  let G' := (baseChange (quotientMap I (n + 1))).obj G
  let eH := Descent.pullbackComparison (quotientMap I (n + 1)) p (quotientMap I n)
    (transition_quotientMap I n) H
  let eG := Descent.pullbackComparison (quotientMap I (n + 1)) p (quotientMap I n)
    (transition_quotientMap I n) G
  have hH' : RelativeMultiplicativeType.IsMultiplicativeType H' :=
    hH.baseChange (quotientMap I (n + 1))
  have : Smooth G'.X.hom := by
    change Smooth (pullback.snd G.X.hom (quotientMap I (n + 1)))
    infer_instance
  obtain ⟨hlift, -⟩ := infinitesimal_lifting_of_surjection hInf
    (transitionRingHom I n) (transitionRingHom_surjective I n)
    ⟨2, transitionRingHom_ker_sq I n⟩ H' G' hH'
  intro f₀
  obtain ⟨f, hf⟩ := hlift (eH.hom ≫ f₀ ≫ eG.inv)
  refine ⟨f, ?_⟩
  change eH.inv ≫ (baseChange p).map f ≫ eG.hom = f₀
  change (baseChange p).map f = eH.hom ≫ f₀ ≫ eG.inv at hf
  rw [hf]
  simp

/-- Formal Hom effectivity and infinitesimal lifting give a global lift of any
homomorphism on the first adic quotient. -/
theorem first_quotient_surjective_of_infinitesimal
    (hInf : MultiplicativeTypeInfinitesimalLiftStatement.{u})
    (H G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (heff : Function.Surjective (System.restrict I H G)) :
    Function.Surjective ((baseChange (quotientMap I 0)).map (X := H) (Y := G)) := by
  intro f₀
  exact System.exists_lift_of_step_surjective I H G heff
    (step_surjective_of_infinitesimal I hInf H G hH) f₀

end Adic

end Langlands.GroupScheme.HomScheme
