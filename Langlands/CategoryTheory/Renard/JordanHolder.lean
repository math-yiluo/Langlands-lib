import Langlands.CategoryTheory.Renard.JordanHolderStatements
import Langlands.CategoryTheory.RenardNoetherIsomorphisms
import Mathlib.Order.JordanHolder

/-!
# Proof of Renard's Jordan–Hölder theorem in an abelian category

Proof of `Langlands.Renard.JordanHolderStatement` (Renard 2026, Appendix A.VI.3)
in an arbitrary abelian category, for the published actual composition chains
and their actual cokernel factors. The route derives, on the actual subobjects
of an object, the cover criterion for simple quotients and a Jordan–Hölder
lattice structure from the public second Noether isomorphism, and then applies
Mathlib's order-theoretic Jordan–Hölder theorem.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

section Criterion

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- A subobject `D ≤ B` killed by the projection `B ⟶ B/A` lies below `A`. -/
private theorem le_of_ofLE_comp_π_eq_zero {A B D : Subobject X} (h : A ≤ B) (hD : D ≤ B)
    (hz : Subobject.ofLE D B hD ≫ cokernel.π (Subobject.ofLE A B h) = 0) : D ≤ A := by
  obtain ⟨l, hl⟩ := exists_lift_of_comp_cokernel_π (Subobject.ofLE A B h) _ hz
  refine Subobject.le_of_comm l ?_
  rw [← Subobject.ofLE_arrow h, reassoc_of% hl, Subobject.ofLE_arrow]

/-- A subobject `D ≤ B` whose inclusion is an epimorphism equals `B`. -/
private theorem eq_of_epi_ofLE {B D : Subobject X} (hD : D ≤ B)
    [Epi (Subobject.ofLE D B hD)] : D = B := by
  have := isIso_of_mono_of_epi (Subobject.ofLE D B hD)
  refine le_antisymm hD (Subobject.le_of_comm (inv (Subobject.ofLE D B hD)) ?_)
  rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]

/-- If `A < B`, the actual quotient `B/A` is nonzero. -/
private theorem not_isZero_cokernel_ofLE {A B : Subobject X} (h : A < B) :
    ¬ IsZero (cokernel (Subobject.ofLE A B h.le)) := by
  intro hz
  have hBA : B ≤ A := le_of_ofLE_comp_π_eq_zero h.le le_rfl (hz.eq_of_tgt _ _)
  exact lt_irrefl A (lt_of_lt_of_le h hBA)

/-- For subobjects `A ≤ B` of `X`, the actual quotient `B/A` is simple exactly
when `B` covers `A` in the order of subobjects of `X`. -/
theorem simple_cokernel_ofLE_iff_covBy (A B : Subobject X) (h : A ≤ B) :
    Simple (cokernel (Subobject.ofLE A B h)) ↔ A ⋖ B := by
  constructor
  · intro hs
    have hlt : A < B := by
      refine lt_of_le_of_ne h (fun hAB => ?_)
      subst hAB
      have : Epi (Subobject.ofLE A A h) := by
        rw [Subobject.ofLE_refl]
        infer_instance
      exact Simple.not_isZero _ (isZero_cokernel_of_epi (Subobject.ofLE A A h))
    refine covBy_iff_lt_and_eq_or_eq.mpr ⟨hlt, fun D hAD hDB => ?_⟩
    by_cases hz : Subobject.ofLE D B hDB ≫ cokernel.π (Subobject.ofLE A B h) = 0
    · exact Or.inl (le_antisymm (le_of_ofLE_comp_π_eq_zero h hDB hz) hAD)
    · right
      have hepi := epi_of_nonzero_to_simple hz
      have : Epi (Subobject.ofLE D B hDB) := by
        refine Preadditive.epi_of_cancel_zero _ (fun {Z} g hg => ?_)
        have w : Subobject.ofLE A B h ≫ g = 0 := by
          rw [← Subobject.ofLE_comp_ofLE A D B hAD hDB, Category.assoc, hg, comp_zero]
        have hd : (Subobject.ofLE D B hDB ≫ cokernel.π (Subobject.ofLE A B h)) ≫
            cokernel.desc _ g w = 0 := by
          rw [Category.assoc, cokernel.π_desc, hg]
        have hd0 : cokernel.desc _ g w = 0 := by
          rw [← cancel_epi (Subobject.ofLE D B hDB ≫ cokernel.π (Subobject.ofLE A B h)),
            hd, comp_zero]
        rw [← cokernel.π_desc (Subobject.ofLE A B h) g w, hd0, comp_zero]
      exact eq_of_epi_ofLE hDB
  · intro hcov
    have hQ := not_isZero_cokernel_ofLE hcov.lt
    refine simple_of_cosimple _ (fun {Z} f _ => ?_)
    have hAk : Subobject.ofLE A B h ≫ cokernel.π (Subobject.ofLE A B h) ≫ f = 0 := by
      rw [cokernel.condition_assoc, zero_comp]
    have hAD : A ≤ Subobject.mk
        (kernel.ι (cokernel.π (Subobject.ofLE A B h) ≫ f) ≫ B.arrow) :=
      Subobject.le_mk_of_comm (kernel.lift _ _ hAk) (by simp)
    have hDB : Subobject.mk
        (kernel.ι (cokernel.π (Subobject.ofLE A B h) ≫ f) ≫ B.arrow) ≤ B :=
      Subobject.mk_le_of_comm _ rfl
    rcases (covBy_iff_lt_and_eq_or_eq.mp hcov).2 _ hAD hDB with hD | hD
    · have hf : f = cokernel.desc _ _ hAk := by
        rw [← cancel_epi (cokernel.π (Subobject.ofLE A B h)), cokernel.π_desc]
      have hmono : Mono f := by
        rw [hf]
        refine mono_cokernel_desc_of_factors _ _ hAk (fun {W} g hg => ?_)
        refine ⟨kernel.lift _ g hg ≫ Subobject.ofMkLE _ A hD.le, ?_⟩
        rw [← cancel_mono B.arrow]
        simp
      have := isIso_of_mono_of_epi f
      exact ⟨fun _ hf0 => hQ (IsZero.of_mono_eq_zero f hf0), fun _ => this⟩
    · have hs : Subobject.ofLEMk B _ hD.ge ≫
          kernel.ι (cokernel.π (Subobject.ofLE A B h) ≫ f) = 𝟙 _ := by
        rw [← cancel_mono B.arrow]
        simp
      have hk : cokernel.π (Subobject.ofLE A B h) ≫ f = 0 := by
        calc cokernel.π (Subobject.ofLE A B h) ≫ f
            = (Subobject.ofLEMk B _ hD.ge ≫
                kernel.ι (cokernel.π (Subobject.ofLE A B h) ≫ f)) ≫
                  cokernel.π (Subobject.ofLE A B h) ≫ f := by
              rw [hs, Category.id_comp]
          _ = 0 := by simp
      have hf0 : f = 0 := by
        rw [← cancel_epi (cokernel.π (Subobject.ofLE A B h)), comp_zero]
        exact hk
      subst hf0
      refine ⟨fun _ => (hQ ?_).elim, fun hne => (hne rfl).elim⟩
      exact IsZero.of_mono_eq_zero (0 : cokernel (Subobject.ofLE A B h) ⟶ Z) rfl

end Criterion

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cover relation on actual subobjects satisfies the Jordan–Hölder laws. -/
@[instance_reducible] private def subobjectJordanHolderLattice (X : C) :
    JordanHolderLattice (Subobject X) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hx hy h := hx.wcovBy.sup_eq hy.wcovBy h
  isMaximal_inf_left_of_isMaximal_sup := by
    intro A B _ hB
    have hB' : B ⋖ B ⊔ A := by simpa only [sup_comm] using hB
    have := (simple_cokernel_ofLE_iff_covBy B (B ⊔ A) le_sup_left).mpr hB'
    obtain ⟨e, _⟩ := secondIso C X B A
    have hs := Simple.of_iso e
    have h := (simple_cokernel_ofLE_iff_covBy (B ⊓ A) A inf_le_right).mp hs
    simpa only [inf_comm] using h

private local instance (X : C) : JordanHolderLattice (Subobject X) :=
  subobjectJordanHolderLattice X

/-- A total interval quotient, agreeing with `B/A` whenever `A ≤ B`. -/
private def intervalQuotient {X : C} (p : Subobject X × Subobject X) : C :=
  cokernel (Subobject.ofLE (p.1 ⊓ p.2) p.2 inf_le_right)

private theorem intervalQuotient_eq {X : C} (A B : Subobject X) (h : A ≤ B) :
    intervalQuotient (A, B) = cokernel (Subobject.ofLE A B h) := by
  change cokernel (Subobject.ofLE (A ⊓ B) B inf_le_right) = _
  suffices ∀ (P : Subobject X) (hP : P ≤ B), P = A →
      cokernel (Subobject.ofLE P B hP) = cokernel (Subobject.ofLE A B h) from
    this (A ⊓ B) inf_le_right (inf_eq_left.mpr h)
  intro P hP hPA
  subst P
  rfl

private theorem intervalIso_quotient {X : C}
    {p q : Subobject X × Subobject X}
    (h : JordanHolderLattice.Iso p q) :
    Nonempty (intervalQuotient p ≅ intervalQuotient q) := by
  apply h.rel (fun p q => Nonempty (intervalQuotient p ≅ intervalQuotient q))
  · exact ⟨Iso.refl _⟩
  · rintro _ _ ⟨e⟩
    exact ⟨e.symm⟩
  · rintro _ _ _ ⟨e⟩ ⟨f⟩
    exact ⟨e.trans f⟩
  · intro A B _
    obtain ⟨e, _⟩ := secondIso C X A B
    rw [intervalQuotient_eq A (A ⊔ B) le_sup_left,
      intervalQuotient_eq (A ⊓ B) B inf_le_right]
    exact ⟨e.symm⟩

private def compositionChainSeries {X : C} {n : ℕ} (c : CompositionChain X n) :
    CompositionSeries (Subobject X) where
  length := n
  toFun := c.subobject
  step i := (simple_cokernel_ofLE_iff_covBy _ _ (c.le_succ i)).mp (c.simple_factor i)

/-- Renard A.VI.3: equal length and isomorphic actual composition factors. -/
theorem jordanHolder (C : Type u) [Category.{v} C] [Abelian C] :
    JordanHolderStatement C := by
  intro X n m c d
  let s := compositionChainSeries c
  let t := compositionChainSeries d
  have hb : s.head = t.head := c.subobject_zero.trans d.subobject_zero.symm
  have ht : s.last = t.last := c.subobject_last.trans d.subobject_last.symm
  obtain ⟨e, he⟩ := CompositionSeries.jordan_holder s t hb ht
  change Fin n ≃ Fin m at e
  have hnm : n = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  refine ⟨hnm, e, fun i => ?_⟩
  have h := intervalIso_quotient (he i)
  change Nonempty (intervalQuotient (c.subobject i.castSucc, c.subobject i.succ) ≅
    intervalQuotient (d.subobject (e i).castSucc, d.subobject (e i).succ)) at h
  rw [intervalQuotient_eq _ _ (c.le_succ i),
    intervalQuotient_eq _ _ (d.le_succ (e i))] at h
  exact h

end

end Langlands.Renard
