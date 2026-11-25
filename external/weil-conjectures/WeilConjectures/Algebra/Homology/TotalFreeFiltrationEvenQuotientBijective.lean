/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationEvenQuotientMap
import all WeilConjectures.Algebra.Homology.TotalFreeFiltrationOddQuotientBijective

/-!
# Degreewise bijectivity of the even column quotient map

Source: Stacks Project, Tag 09KP, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-even-quotient-bijective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

private lemma lower_range_le_full (a : ℕ) (k : ℤ) :
    LinearMap.range (lower K S e a k).hom ≤ LinearMap.range (full K a k).hom := by
  rintro x ⟨y, rfl⟩
  exact ⟨(e a).hom.f (k + a) ((S a).f.f (k + a) y), rfl⟩

private lemma odd_le_even_sup (j : ℕ) (k : ℤ) :
    term K S e (2 * j + 1) k ≤
      term K S e (2 * j) k ⊔ LinearMap.range (lower K S e j k).hom := by
  classical
  apply iSup_le
  intro a
  apply sup_le
  · split_ifs with ha
    · apply le_trans _ le_sup_left
      apply le_trans _ (le_iSup _ a)
      apply le_sup_of_le_left
      rw [ite_eq_left (by omega)]
    · exact bot_le
  · split_ifs with ha
    · by_cases haj : a = j
      · subst a
        exact le_sup_right
      · apply le_trans _ le_sup_left
        apply le_trans _ (le_iSup _ a)
        apply le_sup_of_le_left
        rw [ite_eq_left (by omega)]
        exact lower_range_le_full K S e a k
    · exact bot_le

private lemma column_projection (j : ℕ) (k : ℤ) :
    ∃ r : (K.total (ComplexShape.up ℤ)).X k ⟶ (K.X (-(j : ℤ))).X (k + j),
      full K j k ≫ r = 𝟙 _ ∧
      ∀ a : ℕ, a < j → full K a k ≫ r = 0 := by
  classical
  let f : ∀ p q (_hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = k),
      (K.X p).X q ⟶ (K.X (-(j : ℤ))).X (k + j) :=
    fun p q hi ↦ if hp : p = -(j : ℤ) then
      (K.XXIsoOfEq _ _ _ hp (by dsimp at hi; omega)).hom else 0
  refine ⟨K.totalDesc f, ?_, ?_⟩
  · change K.ιTotal (ComplexShape.up ℤ) (-(j : ℤ)) (k + j) k _ ≫
      K.totalDesc f = 𝟙 _
    rw [HomologicalComplex₂.ι_totalDesc]
    simp [f]
  · intro a ha
    change K.ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (k + a) k _ ≫
      K.totalDesc f = 0
    rw [HomologicalComplex₂.ι_totalDesc]
    exact dite_eq_right (by omega)

/-- Injectivity of the even quotient component.
Source: Stacks Project, Tag 09KP, proof, disjointness of the lower range and even term.
Proof. Projecting to column -j kills earlier columns and proves the lower range meets
the even term trivially.
(blueprint: lem-pc-derived-total-filtration-even-quotient-injective)
-/
theorem evenQuotientComponent_injective
    (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) (k : ℤ) :
    Function.Injective (evenQuotientComponent K S e h_positive j k) := by
  obtain ⟨r, hr, hearlier⟩ := column_projection K j k
  have hzero : term K S e (2 * j) k ≤ LinearMap.ker r.hom := by
    apply iSup_le
    intro a
    apply sup_le
    · split_ifs with ha
      · rintro y ⟨z, rfl⟩
        exact congrArg (fun f ↦ f z) (hearlier a (by omega))
      · exact bot_le
    · split_ifs with ha
      · apply le_trans (lower_range_le_full K S e a k)
        rintro y ⟨z, rfl⟩
        exact congrArg (fun f ↦ f z) (hearlier a (by omega))
      · exact bot_le
  let p : (complex K S e h_positive (2 * j + 1)).X k ⟶
      (K.X (-(j : ℤ))).X (k + j) :=
    ModuleCat.ofHom (r.hom.comp (term K S e (2 * j + 1) k).subtype)
  have hp : (step K S e h_positive (2 * j)).f k ≫ p = 0 := by
    exact restrictMap_projection_zero (K.total (ComplexShape.up ℤ))
      (term K S e (2 * j)) (term K S e (2 * j + 1))
      (differential_mem K S e h_positive (2 * j))
      (differential_mem K S e h_positive (2 * j + 1))
      (fun l ↦ term_mono K S e (Nat.le_succ (2 * j)) l) k _ r
      (fun x hx ↦ hzero hx)
  let hc := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)
    (step K S e h_positive (2 * j))
  let q := hc.desc (CokernelCofork.ofπ p hp)
  have hq : (cokernel.π (step K S e h_positive (2 * j))).f k ≫ q = p :=
    Cofork.IsColimit.π_desc hc
  have hcomp : evenQuotientComponent K S e h_positive j k ≫ q =
      (S j).f.f (k + j) ≫ (e j).hom.f (k + j) := by
    change lowerToOdd K S e h_positive j k ≫
      (cokernel.π (step K S e h_positive (2 * j))).f k ≫ q = _
    rw [hq]
    change lower K S e j k ≫ r = _
    simp only [lower, Category.assoc, hr, Category.comp_id]
  have hs := (h_exact j).map_of_exact
    (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) (k + j))
  have : Mono ((S j).f.f (k + j)) := hs.mono_f
  have : Mono ((S j).f.f (k + j) ≫ (e j).hom.f (k + j)) := inferInstance
  have hinj := (ModuleCat.mono_iff_injective
    ((S j).f.f (k + j) ≫ (e j).hom.f (k + j))).mp inferInstance
  intro x y hxy
  apply hinj
  have h := congrArg (fun f ↦ f x) hcomp
  have h' := congrArg (fun f ↦ f y) hcomp
  exact h.symm.trans ((congrArg q hxy).trans h')

/-- Surjectivity of the even quotient component.
Source: Stacks Project, Tag 09KP, proof, decomposition of the odd term by the new lower range.
Proof. Every odd filtration element is an even element plus a lower-column element;
the cokernel projection kills the even part.
(blueprint: lem-pc-derived-total-filtration-even-quotient-surjective)
-/
theorem evenQuotientComponent_surjective
    (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) (k : ℤ) :
    Function.Surjective (evenQuotientComponent K S e h_positive j k) := by
  have _ := h_exact j
  let π := (cokernel.π (step K S e h_positive (2 * j))).f k
  have hπ : Function.Surjective π := (ModuleCat.epi_iff_surjective π).mp inferInstance
  intro z
  obtain ⟨x, hx⟩ := hπ z
  obtain ⟨y, hy, w, hw, heq⟩ := (Submodule.mem_sup).mp
    (odd_le_even_sup K S e j k x.property)
  obtain ⟨v, rfl⟩ := hw
  let y' : (complex K S e h_positive (2 * j)).X k := ⟨y, hy⟩
  have hdecomp : x = (step K S e h_positive (2 * j)).f k y' +
      lowerToOdd K S e h_positive j k v := by
    apply Subtype.ext
    exact heq.symm
  have hz : (step K S e h_positive (2 * j)).f k ≫ π = 0 :=
    congrArg (fun f ↦ f.f k) (cokernel.condition (step K S e h_positive (2 * j)))
  refine ⟨v, ?_⟩
  change π (lowerToOdd K S e h_positive j k v) = z
  rw [← hx, hdecomp, map_add]
  have hzero := congrArg (fun f ↦ f y') hz
  change π ((step K S e h_positive (2 * j)).f k y') = 0 at hzero
  rw [hzero, zero_add]

/-- (blueprint: lem-pc-derived-total-filtration-even-quotient-bijective) -/
theorem evenQuotientComponent_bijective
    (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) (k : ℤ) :
    Function.Bijective (evenQuotientComponent K S e h_positive j k) := by
  exact ⟨evenQuotientComponent_injective K S e h_positive h_exact j k,
    evenQuotientComponent_surjective K S e h_positive h_exact j k⟩

end CochainComplex.TotalFreeFiltration
