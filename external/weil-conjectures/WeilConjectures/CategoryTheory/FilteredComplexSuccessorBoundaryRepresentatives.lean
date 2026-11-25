/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Representative covers of successor filtered boundaries

Source: Stacks Project, Homology, Tag 012K, displayed boundary and differential formulas.
(blueprint: lem-sp-filtered-complex-successor-boundary-representatives).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem step_mono (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n : ℤ) : Mono ((F.step p).arrow.f n) := by
  change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step p).arrow)
  infer_instance

private theorem exists_pullback_of_le {A B : C} (m : A ⟶ B) [Mono m]
    (S : Subobject B) (hS : S ≤ imageSubobject m) :
    (Subobject.«exists» m).obj ((Subobject.pullback m).obj S) = S := by
  rw [Subobject.exists_iso_map]
  have h := Subobject.inf_eq_map_pullback' (MonoOver.mk m) S
  change Subobject.mk m ⊓ S =
    (Subobject.map m).obj ((Subobject.pullback m).obj S) at h
  rw [← h, inf_eq_right.mpr (by simpa only [imageSubobject_mono] using hS)]

private theorem graded_boundary_image (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (p n s : ℤ) :
    let U := F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
      (F.complexStep (p - s + 1) (n - 1))
    let V := (Subobject.pullback ((F.step p).arrow.f n)).obj U
    imageSubobject (V.arrow ≫
      (F.complexQuotientπ p (p + 1) (by omega)).f n) = F.complexBoundaries p n s := by
  let m := (F.step p).arrow.f n
  have := step_mono K F p n
  let l := (Subobject.ofLE (F.step (p + 1)) (F.step p)
    (F.antitone_step (show p ≤ p + 1 by omega))).f n
  let q := (F.complexQuotientπ p (p + 1) (by omega)).f n
  let U := F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
    (F.complexStep (p - s + 1) (n - 1))
  let V := (Subobject.pullback m).obj U
  have hU : (Subobject.«exists» m).obj V = U :=
    exists_pullback_of_le m U inf_le_left
  have hl : l ≫ m = (F.step (p + 1)).arrow.f n :=
    congrArg (fun f ↦ f.f n) (Subobject.ofLE_arrow (F.antitone_step (show p ≤ p + 1 by omega)))
  have hL : (Subobject.«exists» m).obj (imageSubobject l) = F.complexStep (p + 1) n := by
    rw [Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi (factorThruImageSubobject l),
      ← Category.assoc, imageSubobject_arrow_comp, hl]
    rfl
  have hq : l ≫ q = 0 :=
    congrArg (fun f ↦ f.f n) (cokernel.condition
      (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))))
  change imageSubobject (V.arrow ≫ q) = _
  unfold DecreasingFiltration.complexBoundaries
  change _ = (Subobject.«exists» q).obj
    ((Subobject.pullback m).obj (U ⊔ F.complexStep (p + 1) n))
  rw [← hU, ← hL, ← Subobject.exists_obj_sup m,
    Subobject.exists_iso_map m, Subobject.pullback_map_self,
    Subobject.exists_obj_sup, Subobject.exists_obj_eq_imageSubobject,
    Subobject.exists_obj_eq_imageSubobject]
  rw [← imageSubobject_comp_of_epi (factorThruImageSubobject l),
    ← Category.assoc, imageSubobject_arrow_comp, hq, imageSubobject_zero, sup_bot_eq]

/-- Successor boundaries admit an epimorphic cover by actual incoming cycle representatives.
Source: Stacks Project, Homology, Tag 012K, displayed boundary and differential formulas.
(blueprint: lem-sp-filtered-complex-successor-boundary-representatives).

Proof. Write j = (p,q), n = p+q. The relation gives i = (p-r,q+r-1), of total
degree n-1. Put U = F^p K^n intersect d(F^(p-r) K^(n-1)). Pull U back to F^p K^n.
Its graded image is B_(r+1): the added F^(p+1) has zero graded image, and pullback
along the mono F^p K^n -> K^n preserves sums of subobjects lying in F^p K^n.
Thus the map from this pullback to B_(r+1) is epic. Pull back the epimorphism
F^(p-r) K^(n-1) -> d(F^(p-r) K^(n-1)) along U's inclusion into that image.
This gives an epic cover of U, hence an epic composite e onto B_(r+1), together
with maps t and tprime with dt = tprime. Since tprime lies in F^p, t lies in the
incoming r-cycle representative subobject. Its graded projection therefore factors
through the incoming graded cycles, giving x. The graded projection of tprime is
e followed by the successor-boundary inclusion. Boundaries lie in successor cycles by
d squared = zero. Factoring the latter projection through that mono gives the
last displayed equation. The construction uses finite pullbacks and image
factorizations only; covers compose because epimorphisms are stable under pullback
in an abelian category. -/
theorem filteredComplex_successor_boundary_representatives
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (_hr : 1 ≤ r)
    (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j) :
    ∃ (A : C) (e : A ⟶ (F.complexBoundaries j.1 (j.1 + j.2) (r + 1) : C)),
      Epi e ∧
      ∃ (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
        (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
        (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C)),
        t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫ K.d (i.1 + i.2) (j.1 + j.2) =
          t' ≫ (F.step j.1).arrow.f (j.1 + j.2) ∧
        x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
          t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2) ∧
        e ≫ Subobject.ofLE _ _
            (filteredComplex_boundaries_le_cycles K F j.1 (j.1 + j.2) (r + 1)) ≫
            (F.complexCycles j.1 (j.1 + j.2) (r + 1)).arrow =
          t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) := by
  have hp : i.1 + r = j.1 := congrArg (fun k : ℤ × ℤ ↦ k.1) hij
  have hq : i.2 + (1 - r) = j.2 := congrArg (fun k : ℤ × ℤ ↦ k.2) hij
  have hn : i.1 + i.2 + 1 = j.1 + j.2 := by omega
  have hpred : j.1 + j.2 - 1 = i.1 + i.2 := by omega
  have hfil : j.1 - (r + 1) + 1 = i.1 := by omega
  let mi := (F.step i.1).arrow.f (i.1 + i.2)
  let mj := (F.step j.1).arrow.f (j.1 + j.2)
  let d := mi ≫ K.d (i.1 + i.2) (j.1 + j.2)
  let qi := (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2)
  let qj := (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2)
  let U := F.complexStep j.1 (j.1 + j.2) ⊓ imageSubobject d
  let V := (Subobject.pullback mj).obj U
  let B := F.complexBoundaries j.1 (j.1 + j.2) (r + 1)
  have hImage : (Subobject.«exists» (K.d (i.1 + i.2) (j.1 + j.2))).obj
      (F.complexStep i.1 (i.1 + i.2)) = imageSubobject d := by
    change (Subobject.«exists» (K.d (i.1 + i.2) (j.1 + j.2))).obj
      (imageSubobject mi) = imageSubobject d
    rw [Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi (factorThruImageSubobject mi),
      ← Category.assoc, imageSubobject_arrow_comp]
  have hB : imageSubobject (V.arrow ≫ qj) = B := by
    have h := graded_boundary_image K F j.1 (j.1 + j.2) (r + 1)
    dsimp only at h
    rw [hpred, hfil, hImage] at h
    exact h
  have hBV : B.Factors (V.arrow ≫ qj) :=
    (Subobject.imageSubobject_le_iff _ _).1 (le_of_eq hB)
  let e₀ := B.factorThru (V.arrow ≫ qj) hBV
  have he₀ : Epi e₀ := by
    apply epi_of_imageSubobject_comp_arrow_eq
    simpa only [e₀, Subobject.factorThru_arrow] using hB
  have hU : U.Factors (V.arrow ≫ mj) :=
    (pullback_factors_iff mj U V.arrow).1 (Subobject.factors_self V)
  have hI : (imageSubobject d).Factors (V.arrow ≫ mj) :=
    Subobject.factors_of_le _ inf_le_right hU
  obtain ⟨A, e₁, he₁, t, ht⟩ := surjective_up_to_refinements_of_epi
    (factorThruImageSubobject d) ((imageSubobject d).factorThru _ hI)
  let := he₀
  let := he₁
  let t' := e₁ ≫ V.arrow
  have hdt : t ≫ mi ≫ K.d (i.1 + i.2) (j.1 + j.2) = t' ≫ mj := by
    have h := ht =≫ (imageSubobject d).arrow
    simpa only [d, t', Category.assoc, Subobject.factorThru_arrow,
      imageSubobject_arrow_comp] using h.symm
  let W := F.complexStep i.1 (i.1 + i.2) ⊓
    (Subobject.pullback (K.d (i.1 + i.2) (i.1 + i.2 + 1))).obj
      (F.complexStep (i.1 + r) (i.1 + i.2 + 1))
  have hW : W.Factors (t ≫ mi) := by
    apply (Subobject.inf_factors _).2
    constructor
    · exact imageSubobject_factors_comp_self mi t
    · apply (pullback_factors_iff _ _ _).2
      rw [hp, hn, Category.assoc, hdt]
      exact imageSubobject_factors_comp_self mj t'
  let S := (Subobject.pullback mi).obj
    (W ⊔ F.complexStep (i.1 + 1) (i.1 + i.2))
  have hS : S.Factors t :=
    (pullback_factors_iff mi _ _).2
      (Subobject.factors_of_le _ le_sup_left hW)
  let Z := F.complexCycles i.1 (i.1 + i.2) r
  have hZ : Z.Factors (S.arrow ≫ qi) :=
    (Subobject.exists_le_iff qi S Z).1 le_rfl
  have hx : Z.Factors (t ≫ qi) := by
    rw [← Subobject.factorThru_arrow S t hS, Category.assoc]
    exact Subobject.factors_of_factors_right _ hZ
  let x := Z.factorThru (t ≫ qi) hx
  refine ⟨A, e₁ ≫ e₀, inferInstance, t, t', x, hdt, ?_, ?_⟩
  · exact Subobject.factorThru_arrow Z _ hx
  · simp only [Category.assoc, Subobject.ofLE_arrow]
    change e₁ ≫ e₀ ≫ B.arrow = (e₁ ≫ V.arrow) ≫ qj
    simp only [e₀, Subobject.factorThru_arrow, Category.assoc]


end CategoryTheory
