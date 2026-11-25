/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.SecondFiltrationRowGradedCycles
import WeilConjectures.CategoryTheory.SecondFiltrationRowBoundarySubobject
import WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru

/-! # The normalized row-cycle comparison with the first quotient page

Source: Stacks Project, Homology, Tag 0130, clauses 2 and 4, and Tag 012K.
(blueprint: lem-sp-second-filtration-row-cycle-comparison).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The diagonal inclusion of a mapped row term, using the canonical extension
isomorphism before its total coprojection. This is a concrete map, independent
of page differentials or choices of quotient comparisons.
Source: Stacks Project, Tag 0130, the second-filtration graded identification.
(blueprint: lem-sp-second-filtration-row-cycle-comparison). -/
noncomputable def secondFiltrationRowι
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (r : ℕ) (s : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).X r ⟶
      (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip.total
        (ComplexShape.up ℤ)).X (s + (r : ℤ)) :=
  (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
    ComplexShape.embeddingUpNat (by rfl)).inv ≫
    (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
      (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
        change (r : ℤ) + s = s + (r : ℤ)
        omega)

private theorem pullback_kernelSubobject
    {C : Type*} [Category C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply le_kernelSubobject
    have hf := (Subobject.factors_pullback_obj_iff f (kernelSubobject g) _).mp
      ((Subobject.le_iff_factors_arrow _ _).mp le_rfl)
    simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp hf
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
    apply kernelSubobject_factors
    simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)

private theorem kernelSubobject_of_cokernel
    {C : Type*} [Category C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)
    (hg : IsColimit (CokernelCofork.ofπ g h)) :
    kernelSubobject g = imageSubobject f :=
  ((ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk f g h)).mp
    (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk f g h) hg)).symm

private theorem iso_of_kernelSubobject_eq
    {C : Type*} [Category C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : X ⟶ Z) [Epi f] [Epi g]
    (h : kernelSubobject f = kernelSubobject g) :
    ∃ e : Y ≅ Z, f ≫ e.hom = g := by
  have hf : kernel.ι f ≫ g = 0 := by
    apply (kernelSubobject_factors_iff g _).mp
    rw [← h]
    exact kernelSubobject_factors f _ (kernel.condition f)
  have hg : kernel.ι g ≫ f = 0 := by
    apply (kernelSubobject_factors_iff f _).mp
    rw [h]
    exact kernelSubobject_factors g _ (kernel.condition g)
  let a := Abelian.epiDesc f g hf
  let b := Abelian.epiDesc g f hg
  have ha : f ≫ a = g := Abelian.comp_epiDesc f g hf
  have hb : g ≫ b = f := Abelian.comp_epiDesc g f hg
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply (cancel_epi f).1
    simp only [← Category.assoc, ha, hb, Category.comp_id]
  · apply (cancel_epi g).1
    simp only [← Category.assoc, hb, ha, Category.comp_id]

private theorem row_cycle_lift
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (r : ℕ) (s : ℤ) :
    ∃ t : (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r) ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)),
      t ≫ (L.step s).arrow.f (s + (r : ℤ)) =
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).iCycles r ≫
          secondFiltrationRowι F I r s := by
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj I).flip
  let R := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  let n := s + (r : ℤ)
  let m := (L.step s).arrow.f n
  have : Mono m := by
    change Mono ((HomologicalComplex.eval B (ComplexShape.up ℤ) n).map (L.step s).arrow)
    infer_instance
  have hi : imageSubobject (J.ιTotal (ComplexShape.up ℤ) (r : ℤ) s n
      (by change (r : ℤ) + s = n; dsimp [n]; omega)) ≤ L.complexStep s n := by
    rw [hL]
    dsimp only [HomologicalComplex₂.secondFiltration]
    have hmem : s ∈ Finset.Icc s n := Finset.mem_Icc.mpr ⟨le_rfl, by dsimp [n]; omega⟩
    have hh := Finset.le_sup (f := fun i ↦ imageSubobject
      (J.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n)) hmem
    have hn : n - s = (r : ℤ) := by dsimp [n]; omega
    rw [hn, J.ιTotalOrZero_eq (ComplexShape.up ℤ) (r : ℤ) s n
      (by change (r : ℤ) + s = n; dsimp [n]; omega)] at hh
    exact hh
  have ha : imageSubobject (R.iCycles r ≫ secondFiltrationRowι F I r s) ≤
      imageSubobject m := by
    apply le_trans (imageSubobject_comp_le _ _) ?_
    apply le_trans (imageSubobject_comp_le _ _) hi
  have hm : (Subobject.mk m).Factors (R.iCycles r ≫ secondFiltrationRowι F I r s) := by
    rw [← imageSubobject_mono m]
    apply Subobject.factors_of_le _ ha
    simpa using imageSubobject_factors_comp_self
      (R.iCycles r ≫ secondFiltrationRowι F I r s) (𝟙 _)
  exact (Subobject.mk_factors_iff m _).mp hm

set_option linter.unusedVariables false in
/-- Row cycles have canonical lifts to the filtration and graded cycles. Their
quotient is row homology, normalized by the row homology projection. No page
*differential* occurs in this statement.
Source: Stacks Project, Tag 0130, clauses 2 and 4; Tag 012K, the first-page
cycle/boundary formulas.
(blueprint: lem-sp-second-filtration-row-cycle-comparison).

Proof. Write J for the flipped mapped extended bicomplex. Lift its diagonal
inclusion through L^s in degree s+r. The equality of subobjects hL and membership
of s in the interval [s,s+r] give the unique lift through the monomorphism.
The projection onto the (r,s) summand kills every summand of L^(s+1); it descends
to the graded quotient and is inverse to the diagonal lift followed by the
graded projection. Check both identities on the diagonal coprojections.
On the graded quotient the complex-coordinate differential disappears and the
resolution differential remains. Thus this graded comparison identifies the
row cycles and boundaries with its kernel and image. Apply the first-page
cycles-boundaries identities to obtain the same subobjects as complexCycles
and complexBoundaries. Restrict the lifted diagonal map to row cycles to get t,
and factor its graded class through the identified cycle subobject to get x.
The cokernel of the boundary inclusion is row homology; its universal property
gives e with x followed by the page projection and e.hom equal to homologyπ.
Its inverse is obtained from the inverse graded comparison, so e is an iso.
Extension by zero preserves this calculation at all natural degrees: for r=0
both incoming boundary images are zero. The normalizations determine t and x
by monicity and e by the epic projection from row cycles. This remains valid
for negative s, since the interval is [s,s+r], not [0,s+r]. -/
theorem secondFiltration_row_cycle_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p) :
    let K := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
      (ComplexShape.up ℤ)
    let R := fun s : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
    ∃ (e : ∀ (r : ℕ) (s : ℤ), filteredComplexPageObject K L 1 (s, (r : ℤ)) ≅
        (R s).homology r)
      (t : ∀ (r : ℕ) (s : ℤ), (R s).cycles r ⟶
        (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
      (x : ∀ (r : ℕ) (s : ℤ), (R s).cycles r ⟶
        (L.complexCycles s (s + (r : ℤ)) 1 : B)),
      (∀ r s, t r s ≫ (L.step s).arrow.f (s + (r : ℤ)) =
        (R s).iCycles r ≫ secondFiltrationRowι F I r s) ∧
      (∀ r s, x r s ≫ (L.complexCycles s (s + (r : ℤ)) 1).arrow =
        t r s ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ))) ∧
      (∀ r s, x r s ≫ filteredComplexPageπ K L 1 (s, (r : ℤ)) ≫ (e r s).hom =
        (R s).homologyπ r) := by
  classical
  dsimp only
  let K := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
    (ComplexShape.up ℤ)
  let R := fun s : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  choose t ht using fun r s ↦ row_cycle_lift F I L hL r s
  choose c hc using fun r s ↦ secondFiltration_row_graded_cycles F I L hL r s
    (t r s) (ht r s)
  have hquot (r : ℕ) (s : ℤ) : Epi (filteredComplexPageπ K L 1 (s, (r : ℤ))) := by
    unfold filteredComplexPageπ
    infer_instance
  have hk (r : ℕ) (s : ℤ) :
      kernelSubobject ((c r s).hom ≫ filteredComplexPageπ K L 1 (s, (r : ℤ))) =
        kernelSubobject ((R s).homologyπ r) := by
    rw [← pullback_kernelSubobject]
    have hp : kernelSubobject (filteredComplexPageπ K L 1 (s, (r : ℤ))) =
        imageSubobject (Subobject.ofLE _ _
          (filteredComplex_boundaries_le_cycles K L s (s + (r : ℤ)) 1)) := by
      exact kernelSubobject_of_cokernel _ _ (cokernel.condition _)
        (cokernelIsCokernel _)
    rw [hp, secondFiltration_row_boundary_subobject F I L hL r s
      (t r s) (ht r s) (c r s) (hc r s)]
    exact (kernelSubobject_of_cokernel _ _
      ((R s).toCycles_comp_homologyπ ((ComplexShape.up ℕ).prev r) r)
      ((R s).homologyIsCokernel ((ComplexShape.up ℕ).prev r) r rfl)).symm
  have hex (r : ℕ) (s : ℤ) :
      ∃ e : filteredComplexPageObject K L 1 (s, (r : ℤ)) ≅ (R s).homology r,
        (c r s).hom ≫ filteredComplexPageπ K L 1 (s, (r : ℤ)) ≫ e.hom =
          (R s).homologyπ r := by
    have := hquot r s
    obtain ⟨e, he⟩ := iso_of_kernelSubobject_eq
      ((c r s).hom ≫ filteredComplexPageπ K L 1 (s, (r : ℤ)))
      ((R s).homologyπ r) (hk r s)
    exact ⟨e, by simpa only [Category.assoc] using he⟩
  choose e he using hex
  exact ⟨e, t, fun r s ↦ (c r s).hom, ht, hc, he⟩

end CategoryTheory.Functor
