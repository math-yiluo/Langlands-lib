/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence

/-! The degreewise split exact sequence of an exhaustive split filtration. -/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Identity minus successor on the direct sum of the filtration stages. -/
noncomputable def filteredTelescopeMap {A : Type u} [CommRing A]
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (step : ∀ n, F n ⟶ F (n + 1)) : (∐ F) ⟶ ∐ F :=
  Sigma.desc fun n ↦ Sigma.ι F n - step n ≫ Sigma.ι F (n + 1)

/-- Augmentation from the direct sum, induced by the inclusions in the union. -/
noncomputable def filteredTelescopeAugmentation {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) : (∐ F) ⟶ P :=
  Sigma.desc ι

/-- Compatibility makes the telescope maps a short complex. -/
theorem filteredTelescope_comp_zero {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n) :
    filteredTelescopeMap F step ≫ filteredTelescopeAugmentation P F ι = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [filteredTelescopeMap, filteredTelescopeAugmentation, Preadditive.sub_comp,
    Category.assoc, hcompat]

/-- A recursive finite-sum retraction of identity minus successor. -/
private theorem telescope_retraction {C : Type*} [Category C] [Preadditive C]
    (F : ℕ → C) (D : C) (j : ∀ n, F n ⟶ D)
    (hD : IsColimit (Cofan.mk D j)) (step : ∀ n, F n ⟶ F (n + 1))
    (a : D ⟶ D) (ha : ∀ n, j n ≫ a = j n - step n ≫ j (n + 1))
    (hsplit : ∀ n, ∃ r : F (n + 1) ⟶ F n, step n ≫ r = 𝟙 (F n)) :
    ∃ l : D ⟶ D, a ≫ l = 𝟙 D := by
  classical
  choose r hr using hsplit
  let t : ∀ n, F n ⟶ D := fun n ↦
    Nat.rec (motive := fun n ↦ F n ⟶ D) 0 (fun n t ↦ r n ≫ (t - j n)) n
  let l : D ⟶ D := Cofan.IsColimit.desc hD t
  refine ⟨l, Cofan.IsColimit.hom_ext hD _ _ (fun n ↦ ?_)⟩
  change j n ≫ (a ≫ l) = j n ≫ 𝟙 D
  rw [← Category.assoc, ha, Preadditive.sub_comp, Category.assoc]
  rw [show j n ≫ l = t n from Cofan.IsColimit.fac hD t n,
    show j (n + 1) ≫ l = t (n + 1) from Cofan.IsColimit.fac hD t (n + 1)]
  simp only [Category.comp_id]
  change t n - step n ≫ (r n ≫ (t n - j n)) = j n
  rw [← Category.assoc, hr, Category.id_comp]
  exact sub_sub_cancel _ _

/-- Exhaustive monic stages identify the augmentation as the cokernel of the telescope. -/
private theorem telescope_exact {A : Type u} [CommRing A]
    (P D : ModuleCat.{max u v} A) (F : ℕ → ModuleCat.{max u v} A)
    (j : ∀ n, F n ⟶ D) (hD : IsColimit (Cofan.mk D j))
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ x : P, ∃ n y, ι n y = x)
    (a : D ⟶ D) (b : D ⟶ P) (hab : a ≫ b = 0)
    (ha : ∀ n, j n ≫ a = j n - step n ≫ j (n + 1))
    (hb : ∀ n, j n ≫ b = ι n) :
    (ShortComplex.mk a b hab).Exact := by
  let E : ℕ ⥤ ModuleCat.{max u v} A := Functor.ofSequence step
  let c : Cocone E :=
    { pt := P
      ι := NatTrans.ofSequence ι (by
        intro n
        simpa [E, Functor.ofSequence_map_homOfLE_succ] using hcompat n) }
  have : PreservesColimitsOfSize.{0, 0}
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v, u, 0, 0} (R := A)
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{max u v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits.{max u v, max u v} _
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{max u v} A)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})
      (forget AddCommGrpCat.{max u v})
  have : ReflectsColimit E (forget (ModuleCat.{max u v} A)) :=
    reflectsColimit_of_reflectsIsomorphisms E _
  have hc : IsColimit c := by
    apply isColimitOfReflects (forget (ModuleCat.{max u v} A))
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨n, y, hy⟩ := hexhaustive x
      exact ⟨n, y, hy.symm⟩
    · intro n x y h
      have hxy : x = y := (ModuleCat.mono_iff_injective (ι n)).mp (hmono n) h
      exact ⟨n, 𝟙 n, by simp [hxy]⟩
  have hcok : IsColimit (CokernelCofork.ofπ b hab) := by
    let cone (s : CokernelCofork a) : Cocone E :=
      { pt := s.pt
        ι := NatTrans.ofSequence (fun n ↦ j n ≫ s.π) (by
          intro n
          have hz := congrArg (fun z ↦ j n ≫ z) s.condition
          rw [← Category.assoc, ha, Preadditive.sub_comp, Category.assoc] at hz
          simp only [comp_zero] at hz
          simpa [E, Functor.ofSequence_map_homOfLE_succ] using
            (sub_eq_zero.mp hz).symm) }
    refine Cofork.IsColimit.mk _ (fun s ↦ hc.desc (cone s)) ?_ ?_
    · intro s
      apply Cofan.IsColimit.hom_ext hD
      intro n
      change j n ≫ (b ≫ hc.desc (cone s)) = j n ≫ s.π
      rw [← Category.assoc, hb]
      exact hc.fac (cone s) n
    · intro s m hm
      apply hc.hom_ext
      intro n
      have hn := congrArg (fun z ↦ j n ≫ z) hm
      change j n ≫ (b ≫ m) = j n ≫ s.π at hn
      rw [← Category.assoc, hb] at hn
      exact hn.trans (hc.fac (cone s) n).symm
  exact (ShortComplex.mk a b hab).exact_of_g_is_cokernel hcok

/-- The explicitly constructed telescope sequence is split exact in each degree.
Source: Stacks Project, Tags 09KL--09KM, admissible telescope sequence.
(blueprint: lem-pc-filtered-free-telescope-splitting)

Proof: write S = direct sum of F n, a = identity minus successor, and b for the
augmentation induced by the compatible inclusions. These are precisely the maps
in the statement; they commute with differentials because their summand maps do.
Compatibility gives b a = 0. Work in an arbitrary degree k, identifying S.X k
with the direct sum of (F n).X k by preservation of coproducts by evaluation.
Every vector has finite support. The zeroth coordinate of a(x) is x_0; once the
coordinates before n vanish, its nth coordinate is x_n. Induction therefore
proves that a is injective. Exhaustion proves that b is surjective.
For exactness at S, take z with b(z) = 0 and choose N containing its finite support.
For i <= N let t(i,N) be the composite of the transition maps, with t(N,N) = id.
The relations e_i(x) - e_(i+1)(step_i(x)) = a(e_i(x)) show, by a finite
sum, that z is congruent modulo image(a) to e_N(sum_i t(i,N)(z_i)).
The image of this last coefficient under ι_N is b(z) = 0. Since ι_N is monic,
the coefficient is zero. Thus kernel(b) = image(a), in every degree.

Choose the given degree-k retractions r_i of step_i. For i < j define r(j,i)
by composing r_(j-1), ..., r_i, and put r(i,i) = id. Define a linear map
l : S.X k -> S.X k on the jth summand by giving its ith coordinate as
-r(j,i) for i < j, and zero for i >= j. This has finite support on every
summand and hence defines a map out of the direct sum. In l a on summand n,
the coordinates below n cancel using step_n followed by r_n = id; coordinate
n is id and coordinates above n vanish. Hence l a = id.
Let p = id - a l. It kills image(a). By the kernel calculation and surjectivity
of b, it factors uniquely as s b for a linear s : P.X k -> S.X k.
Equivalently s(x) = p(z) for any lift b(z) = x; differences of lifts lie in
image(a), which p kills, so this formula is independent of the lift and linear.
Then b s = id by surjectivity, and a l + s b = id by definition of p.
These three identities give the required ShortComplex.Splitting. The retractions
need not commute with differentials: the splitting is only degreewise. No
K-projectivity, zero initial stage or boundedness assumption is used here.

For its downstream use, the coproduct S is K-projective whenever the stages are:
restrict a map to an acyclic complex to each summand, choose a null homotopy,
and assemble the components by degreewise coproducts. The split exact sequence
gives a distinguished triangle S -> S -> P -> S[1] in the homotopy category.
K-projectivity is left orthogonality to acyclic complexes, stable under shifts
and extensions; the exact Hom sequence then makes P K-projective. These final
two arguments are separate checked proofs in the assembly, not hypotheses or
conclusions of this construction lemma. Zero rings and zero filtrations are included. -/
theorem filteredTelescope_degreewise_splitting {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k)) :
    ∀ k : ℤ, Nonempty
      (((ShortComplex.mk (filteredTelescopeMap F step)
        (filteredTelescopeAugmentation P F ι)
        (filteredTelescope_comp_zero P F ι step hcompat)).map
          (HomologicalComplex.eval (ModuleCat.{max u v} A) (.up ℤ) k)).Splitting) := by
  intro k
  let ev := HomologicalComplex.eval (ModuleCat.{max u v} A) (.up ℤ) k
  let D := (∐ F).X k
  let G : ℕ → ModuleCat.{max u v} A := fun n ↦ (F n).X k
  let j : ∀ n, G n ⟶ D := fun n ↦ (Sigma.ι F n).f k
  have hD : IsColimit (Cofan.mk D j) :=
    (Cofan.isColimitMapCoconeEquiv ev F (Cofan.mk _ (Sigma.ι F)))
      (isColimitOfPreserves ev (coproductIsCoproduct F))
  let a := (filteredTelescopeMap F step).f k
  let b := (filteredTelescopeAugmentation P F ι).f k
  have ha : ∀ n, j n ≫ a = j n - (step n).f k ≫ j (n + 1) := by
    intro n
    have h := Sigma.ι_comp_desc
      (fun n ↦ Sigma.ι F n - step n ≫ Sigma.ι F (n + 1)) n
    exact congrArg (fun f ↦ f.f k) h
  have hb : ∀ n, j n ≫ b = (ι n).f k := by
    intro n
    exact congrArg (fun f ↦ f.f k) (Sigma.ι_comp_desc ι n)
  have hab : a ≫ b = 0 := congrArg (fun f ↦ f.f k)
    (filteredTelescope_comp_zero P F ι step hcompat)
  have hi : ∀ n, Mono ((ι n).f k) := by
    intro n
    have := hmono n
    exact inferInstance
  have he := telescope_exact (P.X k) D G j hD (fun n ↦ (ι n).f k)
    (fun n ↦ (step n).f k) hi
    (fun n ↦ congrArg (fun f ↦ f.f k) (hcompat n)) (hexhaustive k) a b hab ha hb
  obtain ⟨l, hl⟩ := telescope_retraction G D j hD (fun n ↦ (step n).f k)
    a ha (fun n ↦ hsplit n k)
  have hep : Epi b := by
    apply (ModuleCat.epi_iff_surjective b).mpr
    intro x
    obtain ⟨n, y, hy⟩ := hexhaustive k x
    refine ⟨j n y, ?_⟩
    exact (congrArg (fun f ↦ f y) (hb n)).trans hy
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction _ he l hl hep⟩

end CochainComplex
