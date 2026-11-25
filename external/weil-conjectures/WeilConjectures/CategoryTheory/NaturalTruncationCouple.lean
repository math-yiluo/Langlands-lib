/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.TruncationRawExact
import WeilConjectures.CategoryTheory.TruncationQuadrantVanishing
import WeilConjectures.CategoryTheory.TruncationAbutmentCocone
import WeilConjectures.CategoryTheory.TruncationCoupleNaturality

/-! # Individual natural truncation couples

Source: Stacks Project, Tags 015J, 05TC and 08J5; the individual construction and naturality
in steps 1, 3 and 4 of lem-pc-coproduct-truncation-couple.
(blueprint: lem-pc-natural-bounded-below-truncation-couples).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem zero_projection_square
    {C : Type*} [Category C] (D D' E E' : ℤ → ℤ → C)
    (tD : ∀ p q, D p q ⟶ D' p q) (tE : ∀ p q, E p q ⟶ E' p q)
    (g : ∀ p q, D p q ⟶ E p q) (g' : ∀ p q, D' p q ⟶ E' p q)
    (h : ∀ p q, tD p q ≫ g' p q = g p q ≫ tE p q) (p q : ℤ) :
    tD p q ≫ (g' p q ≫ eqToHom (by simp : E' p q = E' (p + (0 : ℕ)) (q - (0 : ℕ)))) =
      (g p q ≫ eqToHom (by simp : E p q = E (p + (0 : ℕ)) (q - (0 : ℕ)))) ≫
        tE (p + (0 : ℕ)) (q - (0 : ℕ)) := by
  have hc := eqToHom_naturality (fun i : ℤ × ℤ ↦ tE i.1 i.2)
    (by ext <;> simp : (p, q) = (p + (0 : ℕ), q - (0 : ℕ)))
  dsimp only at hc
  rw [Category.assoc, ← hc, ← Category.assoc, h, Category.assoc]

private noncomputable def rawCouple
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) : BigradedExactCouple B 0 := by
  let h := truncation_raw_exact F K
  exact
    { D := TruncationCouple.D F K
      E := TruncationCouple.E F K
      alpha := TruncationCouple.alpha F K
      f := TruncationCouple.f F K
      g := fun p q ↦ TruncationCouple.g F K p q ≫ eqToHom (by simp)
      alpha_f_zero := fun p q ↦ (h.1 p q).choose
      f_g_zero := fun p q ↦ (h.2.1 p q).choose
      g_alpha_zero := fun p q ↦ (h.2.2 p q).choose
      exact_alpha := fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (h.1 p q).choose_spec
      exact_f := fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (h.2.1 p q).choose_spec
      exact_g := fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (h.2.2 p q).choose_spec }

private theorem abutmentMap_isIso
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (n : ℤ) :
    IsIso (TruncationCouple.abutmentMap F K n) := by
  obtain ⟨H, hH, j, c, hj, hc, hiso, _, _⟩ :=
    truncation_abutment_cocone F K (rawCouple F K) rfl
      (by intro p q; simp [rawCouple])
  subst H
  have he : c n = TruncationCouple.abutmentMap F K n := by
    rw [hc, hj]
    simp [TruncationCouple.abutmentMap, rawCouple]
  rw [← he]
  exact hiso n

/-- Choose truncation couples for individual derived objects with a fixed lower bound.
The comparisons commute with every individual morphism. No coproduct is involved.

Source: Stacks Project, Tags 015J, 05TC and 08J5; steps 1, 3 and 4 of
lem-pc-coproduct-truncation-couple.
(blueprint: lem-pc-natural-bounded-below-truncation-couples).

Proof:
1. Use Mathlib's standard t-structure to choose a strictly bounded-below
representative of each object. The localization comparison identifies its
cohomology with that of the original object. Build its exact couple explicitly
from `truncation_raw_exact`, retaining the raw objects and three maps. Apply
`truncation_quadrant_vanishing` and transport the lower-bound hypothesis.
2. `truncation_abutment_cocone` proves the canonical degree-n inclusion is
invertible. Compose this map with RF and homology of the representative
isomorphism to obtain `eD`.
3. Construct `eE` from the inverse bridge and the single-functor, RF and homology
shift isomorphisms, followed by the cohomology comparison of the representative.
4. Conjugate a given derived morphism by the representative isomorphisms and
apply `TruncationCouple.raw_naturality`. Assemble the three raw squares into
`T`; equality-transport naturality handles the type-zero indexing of g.
Compose the raw comparison squares with the representative comparisons. In D,
functoriality and cancellation of the representative isomorphisms give the
claimed equation. In E, cancel the homologyFunctorFactors and representative
isomorphisms, then apply the single/RF/homology composite functor to the resulting
cohomology square. Zero objects and morphisms require no exception.
Choices witness only this existential proposition, and define no library object. -/
theorem exists_natural_boundedBelow_truncation_couples
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (a : ℤ) :
    let L := {M : DerivedCategory A // ∀ r : ℤ, r < a →
      IsZero ((DerivedCategory.homologyFunctor A r).obj M)}
    ∃ (Z : L → BigradedExactCouple B 0)
      (eD : ∀ (M : L) (n : ℤ), (Z M).D 0 n ≅
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj M.val)
      (eE : ∀ (M : L) (p : ℕ) (r : ℤ), (Z M).E p r ≅
        (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B (p : ℤ)).obj
            ((DerivedCategory.homologyFunctor A r).obj M.val)),
      (∀ (M : L) (p r : ℤ), r < a → IsZero ((Z M).D p r)) ∧
      (∀ (M : L) (p r : ℤ), p < 0 → IsZero ((Z M).E p r)) ∧
      ∀ (M N : L) (c : M.val ⟶ N.val),
        ∃ T : BigradedExactCouple.CoupleMorphism (Z M) (Z N),
          (∀ n : ℤ, T.tD 0 n ≫ (eD N n).hom = (eD M n).hom ≫
            (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map c) ∧
          (∀ (p : ℕ) (r : ℤ), T.tE p r ≫ (eE N p r).hom = (eE M p r).hom ≫
            (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
              DerivedCategory.homologyFunctor B (p : ℤ)).map
                ((DerivedCategory.homologyFunctor A r).map c)) := by
  classical
  dsimp only
  let L := {M : DerivedCategory A // ∀ r : ℤ, r < a →
    IsZero ((DerivedCategory.homologyFunctor A r).obj M)}
  have hrep (M : L) : ∃ K : CochainComplex.Plus A,
      Nonempty (DerivedCategory.Q.obj K.obj ≅ M.val) := by
    have : M.val.IsGE a := (DerivedCategory.isGE_iff M.val a).2 M.property
    obtain ⟨K, hK, ⟨e⟩⟩ := M.val.exists_iso_Q_obj_of_isGE a
    exact ⟨⟨K, ⟨a, hK⟩⟩, ⟨e.symm⟩⟩
  choose K he using hrep
  let e (M : L) : DerivedCategory.Q.obj (K M).obj ≅ M.val := Classical.choice (he M)
  let Z (M : L) := rawCouple F (K M)
  let HD (n : ℤ) := F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n
  let HE (p : ℤ) := DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor B p
  have hi (M : L) (n : ℤ) : IsIso (TruncationCouple.abutmentMap F (K M) n) :=
    abutmentMap_isIso F (K M) n
  let eD (M : L) (n : ℤ) : (Z M).D 0 n ≅ (HD n).obj M.val :=
    asIso (TruncationCouple.abutmentMap F (K M) n) ≪≫ (HD n).mapIso (e M)
  let h (M : L) (r : ℤ) : (K M).obj.homology r ≅
      (DerivedCategory.homologyFunctor A r).obj M.val :=
    ((DerivedCategory.homologyFunctorFactors A r).app (K M).obj).symm ≪≫
      (DerivedCategory.homologyFunctor A r).mapIso (e M)
  let eE (M : L) (p : ℕ) (r : ℤ) : (Z M).E p r ≅
      (HE p).obj ((DerivedCategory.homologyFunctor A r).obj M.val) :=
    TruncationCouple.singleIso F (K M) p r ≪≫ (HE p).mapIso (h M r)
  refine ⟨Z, eD, eE, ?_, ?_, ?_⟩
  · intro M p r hr
    exact (truncation_quadrant_vanishing F (K M) a
      (fun r hr ↦ (M.property r hr).of_iso (h M r))).2.1 p r hr
  · intro M p r hp
    have hz := truncation_quadrant_vanishing F (K M) a
      (fun r hr ↦ (M.property r hr).of_iso (h M r))
    exact hz.1 p r hp
  · intro M N c
    let c' := (e M).hom ≫ c ≫ (e N).inv
    obtain ⟨tD, tE, ha, hf, hg, hd, he'⟩ :=
      TruncationCouple.raw_naturality F (K M) (K N) c'
    let T : BigradedExactCouple.CoupleMorphism (Z M) (Z N) :=
      { tD := tD
        tE := tE
        alpha_comm := ha
        f_comm := hf
        g_comm := by
          intro p q
          exact zero_projection_square _ _ _ _ tD tE
            (TruncationCouple.g F (K M)) (TruncationCouple.g F (K N)) hg p q }
    refine ⟨T, ?_, ?_⟩
    · intro n
      dsimp only [T, eD, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
      rw [← Category.assoc, hd n, Category.assoc, ← Functor.map_comp]
      simp [c', HD, Functor.map_comp, Category.assoc]
    · intro p r
      dsimp only [T, eE, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, he' p r, Category.assoc, ← Functor.map_comp]
      have hh : TruncationCouple.homologyMap c' r ≫ (h N r).hom =
          (h M r).hom ≫ (DerivedCategory.homologyFunctor A r).map c := by
        simp [TruncationCouple.homologyMap, h, c', Functor.map_comp, Category.assoc]
      rw [hh, Functor.map_comp, Category.assoc]

end CategoryTheory
