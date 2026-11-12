import Langlands.GroupScheme.Rational.MaximalLeviParabolicFamilyStatement
import Langlands.GroupScheme.Rational.MaximalLeviParabolicCountProof
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Selecting a separated finite family by the actual maximal-Levi count -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem separated_family_of_no_injective_three
    {α : Type w} (R : α → α → Prop)
    (hrefl : ∀ a, R a a) (hsymm : ∀ {a b}, R a b → R b a)
    (hthree : ∀ f : Fin 3 → α, ¬ Function.Injective f) (a₀ : α) :
    ∃ n : ℕ, n ≤ 2 ∧ ∃ f : Fin n → α,
      (∀ i j, R (f i) (f j) → i = j) ∧ (∀ a, ∃ i, R a (f i)) := by
  classical
  by_cases h : ∀ a, R a a₀
  · refine ⟨1, by decide, fun _ => a₀, ?_, ?_⟩
    · intro i j _
      exact Subsingleton.elim i j
    · intro a
      exact ⟨0, h a⟩
  · obtain ⟨a₁, ha₁⟩ := not_forall.mp h
    refine ⟨2, by decide, ![a₀, a₁], ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (ha₁ (hsymm hij))
      · exact False.elim (ha₁ hij)
      · rfl
    · intro a
      by_cases ha₀ : R a a₀
      · exact ⟨0, ha₀⟩
      by_cases ha₁' : R a a₁
      · exact ⟨1, ha₁'⟩
      have h01 : a₀ ≠ a₁ := by
        intro he
        subst a₁
        exact ha₁ (hrefl a₀)
      have h02 : a₀ ≠ a := by
        intro he
        subst a
        exact ha₀ (hrefl a₀)
      have h12 : a₁ ≠ a := by
        intro he
        subst a
        exact ha₁' (hrefl a₁)
      exfalso
      apply hthree ![a₀, a₁, a]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all

/-- A source maximal Levi admits a separated family of at most two actual
parabolics, covering all parabolics with a conjugate embedded Levi. -/
theorem maximalLeviParabolicFamily : MaximalLeviParabolicFamilyStatement.{u} := by
  classical
  intro k _ G hG P M p l hp hl hproper hmax
  let S := {F : SubgroupFunctor G //
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (lQ : M ⟶ Q),
      IsParabolicSubgroup q ∧ IsRationalLeviSubgroup lQ ∧
      lQ ≫ q = l ≫ p ∧ SubgroupFunctor.range q = F}
  have hS (s : S) := s.property
  choose Qs qs ls hqs hls hcs hes using hS
  have hthree : ∀ f : Fin 3 → S, ¬ Function.Injective f := by
    intro f hf
    have hinj : Function.Injective (fun i => SubgroupFunctor.range (qs (f i))) := by
      intro i j he
      apply hf
      apply Subtype.ext
      simpa only [hes] using he
    have hcount := maximalLeviParabolicCount k G hG P M p l hp hl hproper hmax
      3 (fun i => Qs (f i)) (fun i => qs (f i)) (fun i => ls (f i))
      (fun i => hqs (f i)) (fun i => hls (f i)) (fun i => hcs (f i)) hinj
    omega
  let s₀ : S := ⟨SubgroupFunctor.range p, P, p, l, hp, hl, rfl, rfl⟩
  obtain ⟨n, hn, f, hsep, hcover⟩ := separated_family_of_no_injective_three
    (fun s t : S => s.1.IsRationallyConjugate t.1)
    (fun s => SubgroupFunctor.IsRationallyConjugate.refl s.1)
    (fun h => h.symm) hthree s₀
  have hrad (a : Fin n) := (hls (f a)).exists_unipotentRadical
  choose Us rs hrs hmuls using hrad
  refine ⟨n, hn, (fun a => Qs (f a)), Us, (fun a => qs (f a)),
    (fun a => ls (f a)), rs, (fun a => hqs (f a)), (fun a => hls (f a)),
    hrs, hmuls, (fun a => hcs (f a)), ?_, ?_⟩
  · intro a b hab
    apply hsep a b
    simpa only [hes] using hab
  · intro Q' L' q' l' hq' hl' e g hcomp
    let q'' := q' ≫ (G.innerIso g).inv
    let l'' := e.hom ≫ l'
    have hq'' : IsParabolicSubgroup q'' := hq'.comp_iso (G.innerIso g).symm
    have hl'' : IsRationalLeviSubgroup l'' := hl'.iso_comp e
    have hc'' : l'' ≫ q'' = l ≫ p := by
      calc
        l'' ≫ q'' = (e.hom ≫ l' ≫ q') ≫ (G.innerIso g).inv := by
          simp only [l'', q'', Category.assoc]
        _ = l ≫ p := by rw [hcomp]; simp
    let s : S := ⟨SubgroupFunctor.range q'', Q', q'', l'', hq'', hl'', hc'', rfl⟩
    obtain ⟨a, ha⟩ := hcover s
    refine ⟨a, ?_⟩
    have hconj : (SubgroupFunctor.range q').IsRationallyConjugate
        (SubgroupFunctor.range q'') := by
      refine ⟨g⁻¹, ?_⟩
      rw [innerIso_inv_hom]
      change SubgroupFunctor.range q' =
        (SubgroupFunctor.range (q' ≫ (G.innerIso g).symm.hom)).comap (G.innerIso g).inv
      rw [SubgroupFunctor.range_comp_iso, Iso.symm_inv,
        SubgroupFunctor.comap_iso_hom_inv]
    apply hconj.trans
    simpa only [hes] using ha

end Langlands.GroupScheme
