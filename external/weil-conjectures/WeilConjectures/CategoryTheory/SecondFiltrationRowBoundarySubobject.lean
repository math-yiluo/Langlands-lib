/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles
import WeilConjectures.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import WeilConjectures.CategoryTheory.SecondFiltrationIncomingRowCover
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Row boundaries in the second graded filtration

Source: Stacks Project, Homology, Tags 0130 and 012K.
(blueprint: lem-sp-second-filtration-row-boundary-subobject).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

private theorem map_image {C : Type*} [Category C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (m : Y ⟶ Z) [Mono m] :
    (Subobject.map m).obj (imageSubobject f) = imageSubobject (f ≫ m) := by
  rw [← Subobject.exists_iso_map, Subobject.exists_obj_eq_imageSubobject,
    ← imageSubobject_comp_of_epi (factorThruImageSubobject f),
    ← Category.assoc, imageSubobject_arrow_comp]

/-- Under the normalized cycle comparison the first-page boundary subobject is
exactly the image of the incoming row differential into row cycles.
Source: Stacks Project, Tag 0130, clauses 2 and 4; Tag 012K, boundary formula.
(blueprint: lem-sp-second-filtration-row-boundary-subobject).

Proof. The diagonal projection and lift identify the graded row term in each
resolution degree with the corresponding mapped row term. The total differential
has a resolution component and a component raising s; the latter lands in the
next filtration step. Therefore the incoming graded differential corresponds to
the incoming row differential. For r>0 its source is the mapped row term r-1,
and the extension isomorphism identifies its image in the kernel of the outgoing
differential with image(toCycles). The first-page boundary formula says that the
filtered boundary subobject in the graded term is this image of the incoming
graded differential. Factoring it through the cycle mono gives the inclusion
used below. The two normalization equations fix c by monicity, so pulling this
boundary subobject back along c.hom recovers the row boundary image.
For r=0 the incoming extended row term has resolution degree -1 and is zero;
the row differential from prev 0 = 0 to 0 is also zero, so both images are bottom.
The interval argument is [s,s+r] and includes negative s. If a row is zero the
cycle objects and both boundary subobjects are zero. No quotient or homology
isomorphism is asserted or used in this comparison.
-/
theorem secondFiltration_row_boundary_subobject
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
    (r : ℕ) (s : ℤ)
    (t : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
    (ht : t ≫ (L.step s).arrow.f (s + (r : ℤ)) =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).iCycles r ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
            change (r : ℤ) + s = s + (r : ℤ)
            omega)))
    (c : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ≅
      (L.complexCycles s (s + (r : ℤ)) 1 : B))
    (hc : c.hom ≫ (L.complexCycles s (s + (r : ℤ)) 1).arrow =
      t ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ))) :
    (Subobject.pullback c.hom).obj (imageSubobject (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles
        ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
          (ComplexShape.up ℤ)) L s (s + (r : ℤ)) 1))) =
      imageSubobject
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).toCycles
          ((ComplexShape.up ℕ).prev r) r) := by
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj I).flip
  let R := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  let n := s + (r : ℤ)
  let m := (L.step s).arrow.f n
  let z := (L.complexCycles s n 1).arrow
  let q : (L.step s : CochainComplex B ℤ).X n ⟶ (L.gradedPiece s).X n :=
    (L.complexQuotientπ s (s + 1) (by omega)).f n
  have : Mono m := by
    change Mono ((HomologicalComplex.eval B (ComplexShape.up ℤ) n).map (L.step s).arrow)
    infer_instance
  let j : R.X r ⟶ (J.total (ComplexShape.up ℤ)).X n :=
    (R.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv ≫
      J.ιTotal (ComplexShape.up ℤ) (r : ℤ) s n (by dsimp [n]; omega)
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
  have hj : imageSubobject j ≤ imageSubobject m :=
    le_trans (imageSubobject_comp_le _ _) hi
  have hfac : (Subobject.mk m).Factors j := by
    rw [← imageSubobject_mono m]
    apply Subobject.factors_of_le _ hj
    simpa using imageSubobject_factors_comp_self j (𝟙 _)
  obtain ⟨a, ha⟩ := (Subobject.mk_factors_iff m j).mp hfac
  change R.X r ⟶ (L.step s : CochainComplex B ℤ).X n at a
  change a ≫ m = j at ha
  have ht' : R.iCycles r ≫ a = t := by
    apply (cancel_mono m).1
    rw [Category.assoc, ha]
    exact ht.symm
  have hB : L.complexBoundaries s n 1 =
      imageSubobject (R.toCycles ((ComplexShape.up ℕ).prev r) r ≫ c.hom ≫ z) := by
    rw [(L.filteredComplex_firstPage_cycles_boundaries s n).2]
    by_cases hr : r = 0
    · subst r
      have hstep : L.complexStep s (s - 1) = ⊥ := by
        rw [hL]
        simp only [HomologicalComplex₂.secondFiltration,
          Finset.Icc_eq_empty_of_lt (by omega : s - 1 < s), Finset.sup_empty]
      let m₀ := (L.step s).arrow.f (s - 1)
      have : Mono m₀ := by
        change Mono ((HomologicalComplex.eval B (ComplexShape.up ℤ) (s - 1)).map
          (L.step s).arrow)
        infer_instance
      have hm₀ : m₀ = 0 := by
        apply (Subobject.bot_factors_iff_zero m₀).mp
        rw [← hstep]
        exact (Subobject.imageSubobject_le_iff m₀ _).mp le_rfl
      have hz₀ := IsZero.of_mono_eq_zero m₀ hm₀
      let q₀ : (L.step s : CochainComplex B ℤ).X (s - 1) ⟶
          (L.gradedPiece s).X (s - 1) :=
        (L.complexQuotientπ s (s + 1) (by omega)).f (s - 1)
      have : Epi q₀ := by
        change Epi ((HomologicalComplex.eval B (ComplexShape.up ℤ) (s - 1)).map
          (cokernel.π (Subobject.ofLE (L.step (s + 1)) (L.step s)
            (L.antitone_step (by omega)))))
        infer_instance
      have hgr := IsZero.of_epi q₀ hz₀
      have hd : (L.gradedPiece s).d (n - 1) n = 0 := by
        apply IsZero.eq_zero_of_src
        simpa only [n, Nat.cast_zero, add_zero] using hgr
      have htocycles : R.toCycles ((ComplexShape.up ℕ).prev 0) 0 = 0 := by
        apply (cancel_mono (R.iCycles 0)).1
        rw [HomologicalComplex.toCycles_i, zero_comp]
        apply R.shape
        simp
      simp only [hd, htocycles, zero_comp, imageSubobject_zero]
    obtain ⟨e, he, hδ⟩ :=
      secondFiltration_incoming_row_cover F I L hL r s (Nat.pos_of_ne_zero hr) a ha
    have : Epi e := he
    rw [← imageSubobject_comp_of_epi e, hδ]
    congr 1
    change R.d ((ComplexShape.up ℕ).prev r) r ≫ a ≫ q =
      R.toCycles ((ComplexShape.up ℕ).prev r) r ≫ c.hom ≫ z
    rw [← HomologicalComplex.toCycles_i R ((ComplexShape.up ℕ).prev r) r,
      Category.assoc, ← Category.assoc (R.iCycles r), ht']
    exact congrArg (R.toCycles ((ComplexShape.up ℕ).prev r) r ≫ ·) hc.symm
  have hmap : imageSubobject (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles (J.total (ComplexShape.up ℤ)) L s n 1)) =
      (Subobject.map c.hom).obj
        (imageSubobject (R.toCycles ((ComplexShape.up ℕ).prev r) r)) := by
    apply Subobject.map_obj_injective z
    rw [map_image, Subobject.ofLE_arrow, map_image, map_image, Category.assoc, ← hB]
    exact imageSubobject_mono (L.complexBoundaries s n 1).arrow |>.trans
      (Subobject.mk_arrow _)
  rw [hmap, Subobject.pullback_map_self]


end CategoryTheory.Functor
