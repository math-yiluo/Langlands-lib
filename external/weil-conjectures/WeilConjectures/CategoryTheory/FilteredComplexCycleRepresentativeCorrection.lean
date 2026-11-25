/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A representative of a zero page class is locally an incoming boundary plus a
term of one higher filtration. This assertion only concerns target boundaries;
it neither corrects a source representative nor constructs successor cycles.
Source: Stacks Project, Homology, Tag 012K, displayed boundary formula.
(blueprint: lem-sp-filtered-complex-cycle-representative-correction).

Proof. The kernel of the page cokernel is the boundary inclusion, so y factors
through graded boundaries. Pull back the epimorphism defining their image to
lift y to the pullback of (F^p intersect d(F^(p-r+1))) plus F^(p+1).
The difference from the given t has zero graded projection. The kernel of that
projection is F^(p+1), so this difference also lifts to F^(p+1). Pull back the
sum epimorphism to split the first lift into an incoming boundary and a higher
filtration term. Finally pull back the image epimorphism defining d(F^(p-r+1))
to obtain b. Combine the two higher filtration terms to obtain c. Thus
et = db + c in K. All pullbacks of epimorphisms are epic in an abelian category,
and their composite is epic. No projectivity or arbitrary global lifting is used. -/
private theorem filteredComplex_boundary_representative_lift
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (_hr : 1 ≤ r)
    (j : ℤ × ℤ) (p n : ℤ)
    (hp : p = j.1 - r + 1) (hn : n = j.1 + j.2 - 1) (A : C)
    (t : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
    (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C))
    (hy : y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
      t ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2))
    (hy0 : y ≫ filteredComplexPageπ K F r j = 0) :
    ∃ (B : C) (e : B ⟶ A), Epi e ∧
      ∃ (b : B ⟶ (F.step p : CochainComplex C ℤ).X n)
        (c : B ⟶ (F.step (j.1 + 1) : CochainComplex C ℤ).X (j.1 + j.2)),
        e ≫ t ≫ (F.step j.1).arrow.f (j.1 + j.2) =
          b ≫ (F.step p).arrow.f n ≫
            K.d n (j.1 + j.2) +
              c ≫ (F.step (j.1 + 1)).arrow.f (j.1 + j.2) := by
  let m := (F.step j.1).arrow.f (j.1 + j.2)
  let q := (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2)
  let l := Subobject.ofLE (F.step (j.1 + 1)) (F.step j.1)
    (F.antitone_step (show j.1 ≤ j.1 + 1 by omega))
  let d := (F.step p).arrow.f n ≫ K.d n (j.1 + j.2)
  let R := F.complexStep j.1 (j.1 + j.2) ⊓ imageSubobject d
  let L := F.complexStep (j.1 + 1) (j.1 + j.2)
  let V := (Subobject.pullback m).obj (R ⊔ L)
  have hI : (Subobject.«exists» (K.d (j.1 + j.2 - 1) (j.1 + j.2))).obj
      (F.complexStep (j.1 - r + 1) (j.1 + j.2 - 1)) = imageSubobject d := by
    rw [← hp, ← hn]
    change (Subobject.«exists» (K.d n (j.1 + j.2))).obj
      (imageSubobject ((F.step p).arrow.f n)) = _
    rw [Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi (factorThruImageSubobject ((F.step p).arrow.f n)),
      ← Category.assoc, imageSubobject_arrow_comp]
  have hB : F.complexBoundaries j.1 (j.1 + j.2) r = (Subobject.«exists» q).obj V := by
    unfold DecreasingFiltration.complexBoundaries
    rw [hI]
  let k := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F j.1 (j.1 + j.2) r)
  have hy0' : y ≫ cokernel.π k = 0 := hy0
  let v := Abelian.monoLift k y hy0'
  have hv : v ≫ k = y := Abelian.monoLift_comp k y hy0'
  let w := v ≫ (Subobject.isoOfEq _ _ hB).hom
  obtain ⟨ve, heve, hve⟩ := Subobject.exists_fac q V
  let := heve
  obtain ⟨A₁, e₁, he₁, a, ha⟩ :=
    surjective_up_to_refinements_of_epi ve w
  let := he₁
  have haq : a ≫ V.arrow ≫ q = e₁ ≫ t ≫ q := by
    rw [← hve, ← Category.assoc, ← ha]
    dsimp only [w]
    simp only [Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow]
    rw [← Subobject.ofLE_arrow
      (filteredComplex_boundaries_le_cycles K F j.1 (j.1 + j.2) r), ← Category.assoc v,
      hv, hy]
  have hzero : (e₁ ≫ t - a ≫ V.arrow) ≫ q = 0 := by
    simp only [Preadditive.sub_comp, Category.assoc, haq, sub_self]
  have hex := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk l (cokernel.π l) (cokernel.condition l))
    (cokernelIsCokernel l)).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) (j.1 + j.2))
  obtain ⟨A₂, e₂, he₂, aL, haL⟩ := hex.exact_up_to_refinements
    (e₁ ≫ t - a ≫ V.arrow) hzero
  change A₂ ⟶ (F.step (j.1 + 1) : CochainComplex C ℤ).X (j.1 + j.2) at aL
  change e₂ ≫ (e₁ ≫ t - a ≫ V.arrow) = aL ≫ l.f (j.1 + j.2) at haL
  let := he₂
  have hav : (R ⊔ L).Factors (a ≫ V.arrow ≫ m) := by
    simpa only [Category.assoc] using
      (pullback_factors_iff m (R ⊔ L) (a ≫ V.arrow)).mp
        (Subobject.factors_comp_arrow a)
  let aS := (R ⊔ L).factorThru (a ≫ V.arrow ≫ m) hav
  let := Subobject.epi_supDesc R L
  obtain ⟨A₃, e₃, he₃, z, hz⟩ :=
    surjective_up_to_refinements_of_epi (Subobject.supDesc R L) (e₂ ≫ aS)
  let := he₃
  let zR := z ≫ biprod.fst
  let zL := z ≫ biprod.snd
  have hzRL : e₃ ≫ e₂ ≫ a ≫ V.arrow ≫ m = zR ≫ R.arrow + zL ≫ L.arrow := by
    have h := congrArg (fun f ↦ f ≫ (R ⊔ L).arrow) hz
    simpa only [aS, Subobject.factorThru_arrow, Category.assoc, Subobject.supDesc,
      Subobject.ofLE_arrow, biprod.desc_eq, Preadditive.comp_add, Preadditive.add_comp,
      zR, zL] using h
  have hzI : (imageSubobject d).Factors (zR ≫ R.arrow) :=
    Subobject.factors_of_le _ inf_le_right (Subobject.factors_comp_arrow zR)
  let zI := (imageSubobject d).factorThru (zR ≫ R.arrow) hzI
  obtain ⟨A₄, e₄, he₄, b, hb⟩ :=
    surjective_up_to_refinements_of_epi (factorThruImageSubobject d) zI
  let := he₄
  have hbd : b ≫ d = e₄ ≫ zR ≫ R.arrow := by
    have h := congrArg (fun f ↦ f ≫ (imageSubobject d).arrow) hb
    simpa only [Category.assoc, imageSubobject_arrow_comp, zI,
      Subobject.factorThru_arrow] using h.symm
  have hmono : Mono ((F.step (j.1 + 1)).arrow.f (j.1 + j.2)) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) (j.1 + j.2)).map
      (F.step (j.1 + 1)).arrow)
    infer_instance
  have hzL : (Subobject.mk ((F.step (j.1 + 1)).arrow.f (j.1 + j.2))).Factors
      (zL ≫ L.arrow) := by
    have h := Subobject.factors_comp_arrow (P := L) zL
    simpa only [L, DecreasingFiltration.complexStep, imageSubobject_mono] using h
  obtain ⟨cL, hcL⟩ := (Subobject.mk_factors_iff _ _).mp hzL
  change A₃ ⟶ (F.step (j.1 + 1) : CochainComplex C ℤ).X (j.1 + j.2) at cL
  change cL ≫ (F.step (j.1 + 1)).arrow.f (j.1 + j.2) = zL ≫ L.arrow at hcL
  have hlm : l.f (j.1 + j.2) ≫ m = (F.step (j.1 + 1)).arrow.f (j.1 + j.2) :=
    congrArg (fun f : (F.step (j.1 + 1) : CochainComplex C ℤ) ⟶ K ↦
      f.f (j.1 + j.2)) (Subobject.ofLE_arrow
        (F.antitone_step (show j.1 ≤ j.1 + 1 by omega)))
  refine ⟨A₄, e₄ ≫ e₃ ≫ e₂ ≫ e₁, inferInstance, b,
    e₄ ≫ cL + e₄ ≫ e₃ ≫ aL, ?_⟩
  have hLa := congrArg (fun f ↦ f ≫ m) haL
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hlm] at hLa
  have hsplit := (sub_eq_iff_eq_add).mp hLa
  change (e₄ ≫ e₃ ≫ e₂ ≫ e₁) ≫ t ≫ m =
    b ≫ d + (e₄ ≫ cL + e₄ ≫ e₃ ≫ aL) ≫
      (F.step (j.1 + 1)).arrow.f (j.1 + j.2)
  calc
    _ = e₄ ≫ e₃ ≫ (aL ≫ (F.step (j.1 + 1)).arrow.f (j.1 + j.2) +
        e₂ ≫ a ≫ V.arrow ≫ m) := by
      simpa only [Category.assoc] using congrArg (fun f ↦ e₄ ≫ e₃ ≫ f) hsplit
    _ = e₄ ≫ e₃ ≫ aL ≫ (F.step (j.1 + 1)).arrow.f (j.1 + j.2) +
        e₄ ≫ (zR ≫ R.arrow + zL ≫ L.arrow) := by
      rw [Preadditive.comp_add, Preadditive.comp_add]
      rw [← Category.assoc e₃, hzRL]
    _ = _ := by
      simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc, hcL]
      rw [← hbd]
      abel


/-- A representative whose differential is a page boundary can be corrected to a
successor-cycle representative without changing its source graded class.
Source: Stacks Project, Homology, Tag 012K, displayed cycle and boundary formulas.
(blueprint: lem-sp-filtered-complex-cycle-representative-correction).

Proof. Write p = i.1 and n = i.1 + i.2. The relation gives j.1 = p+r and
j.1+j.2 = n+1. Since the target page is the cokernel of its boundary inclusion,
hy0 factors y through the target graded boundary subobject. Pull back the image
epimorphism defining this subobject, and the epimorphism onto the sum of the
unquotiented boundary subobject with F^(p+r+1). The equality of target graded
classes then says, after pulling back the graded quotient epimorphism's kernel,
that dt is a sum of an incoming boundary and a term in F^(p+r+1). Pull back the
image epimorphism from F^((p+r)-r+1) = F^(p+1) defining that incoming boundary.
On the resulting epic cover e of A, obtain a morphism b into F^(p+1) with
d(e t - b) in F^(p+r+1). Include b into F^p; this is possible since F is
antitone. Thus e t - b factors through the unquotiented (r+1)-cycle intersection.
Its graded projection factors through the image defining successor graded cycles,
giving z. The graded projection kills b, so z has exactly the same graded class
as e x, by hx. Each cover is a pullback of an image or cokernel epimorphism and
is epic in an abelian category; their finite composite e is epic. This proves
the displayed equality without projectivity or elementwise lifting. -/
theorem filteredComplex_cycle_representative_correction
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j)
    (A : C)
    (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
    (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
    (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
    (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C))
    (ht : t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫
      K.d (i.1 + i.2) (j.1 + j.2) = t' ≫ (F.step j.1).arrow.f (j.1 + j.2))
    (hx : x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
      t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2))
    (hy : y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
      t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2))
    (hy0 : y ≫ filteredComplexPageπ K F r j = 0) :
    ∃ (B : C) (e : B ⟶ A), Epi e ∧
      ∃ z : B ⟶ (F.complexCycles i.1 (i.1 + i.2) (r + 1) : C),
        z ≫ (F.complexCycles i.1 (i.1 + i.2) (r + 1)).arrow =
          e ≫ x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow := by
  have hp : i.1 + r = j.1 := congrArg (fun k : ℤ × ℤ ↦ k.1) hij
  have hq : i.2 + (1 - r) = j.2 := congrArg (fun k : ℤ × ℤ ↦ k.2) hij
  have hn : i.1 + i.2 + 1 = j.1 + j.2 := by omega
  have hpred : j.1 + j.2 - 1 = i.1 + i.2 := by omega
  have hfil : j.1 - r + 1 = i.1 + 1 := by omega
  obtain ⟨B, e, he, b, c, hbc⟩ :=
    filteredComplex_boundary_representative_lift K F r hr j (i.1 + 1) (i.1 + i.2)
      hfil.symm hpred.symm A t' y hy hy0
  let inc := Subobject.ofLE (F.step (i.1 + 1)) (F.step i.1)
    (F.antitone_step (show i.1 ≤ i.1 + 1 by omega))
  let u := e ≫ t - b ≫ inc.f (i.1 + i.2)
  let m := (F.step i.1).arrow.f (i.1 + i.2)
  let q := (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2)
  have hinc : inc.f (i.1 + i.2) ≫ m = (F.step (i.1 + 1)).arrow.f (i.1 + i.2) :=
    congrArg (fun f : (F.step (i.1 + 1) : CochainComplex C ℤ) ⟶ K ↦
      f.f (i.1 + i.2)) (Subobject.ofLE_arrow
        (F.antitone_step (show i.1 ≤ i.1 + 1 by omega)))
  have hu : u ≫ m ≫ K.d (i.1 + i.2) (j.1 + j.2) =
      c ≫ (F.step (j.1 + 1)).arrow.f (j.1 + j.2) := by
    dsimp only [u]
    simp only [Preadditive.sub_comp, Category.assoc]
    rw [← Category.assoc (inc.f (i.1 + i.2)), hinc]
    change e ≫ (t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫
      K.d (i.1 + i.2) (j.1 + j.2)) - _ = _
    rw [ht, hbc]
    exact add_sub_cancel_left _ _
  let R := F.complexStep i.1 (i.1 + i.2) ⊓
    (Subobject.pullback (K.d (i.1 + i.2) (i.1 + i.2 + 1))).obj
      (F.complexStep (i.1 + (r + 1)) (i.1 + i.2 + 1))
  have huR : R.Factors (u ≫ m) := by
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      rw [hn, show i.1 + (r + 1) = j.1 + 1 by omega, Category.assoc, hu]
      exact imageSubobject_factors_comp_self _ _
  let W := (Subobject.pullback m).obj (R ⊔ F.complexStep (i.1 + 1) (i.1 + i.2))
  have huW : W.Factors u := (pullback_factors_iff _ _ _).mpr
    (Subobject.sup_factors_of_factors_left huR)
  let z := (Subobject.factorThru W u huW) ≫ (Subobject.imageFactorisation q W).F.e
  have hz : z ≫ (F.complexCycles i.1 (i.1 + i.2) (r + 1)).arrow = u ≫ q := by
    change z ≫ ((Subobject.«exists» q).obj W).arrow = _
    dsimp only [z]
    rw [Category.assoc, ← Subobject.imageFactorisation_F_m,
      (Subobject.imageFactorisation q W).F.fac]
    simp
  have hqzero : inc.f (i.1 + i.2) ≫ q = 0 :=
    congrArg (fun f ↦ f.f (i.1 + i.2)) (cokernel.condition inc)
  refine ⟨B, e, he, z, ?_⟩
  rw [hz]
  dsimp only [u]
  simp only [Preadditive.sub_comp, Category.assoc, hqzero, comp_zero, sub_zero]
  simpa only [Category.assoc, q] using congrArg (fun f ↦ e ≫ f) hx.symm

end CategoryTheory
