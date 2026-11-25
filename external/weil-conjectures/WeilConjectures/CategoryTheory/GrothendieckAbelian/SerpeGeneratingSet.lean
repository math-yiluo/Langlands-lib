/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.Order.TransfiniteIteration
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeCardinal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeEnlargement
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeSmallObject
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian

/-!
# The Serpé generating set detects the monomorphic quasi-isomorphisms

Let `C` be a Grothendieck abelian category, `G : C` a separator and `κ` a regular cardinal
dominating `ℵ₀` and the cardinalities of the subobject lattices of the finite copowers of `G`.
In this file we show that every monomorphic quasi-isomorphism of cochain complexes in `C` is a
transfinite composition of pushouts of morphisms in the small family
`CochainComplex.generatingMonoQuasiIsos G κ`, and deduce that the two families have the same
right lifting property.

The argument is the one of
`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean`, transposed one
categorical level up: starting from a subobject `D` of `B` whose inclusion is a
quasi-isomorphism, the Serpé enlargement step
`CochainComplex.exists_larger_subobject_quasiIso` produces a strictly larger such subobject,
and the transfinite iteration of this step exhausts `B` for cardinality reasons. The property
"the inclusion of `D` in `B` is a quasi-isomorphism" is propagated along the iteration by
observing that the inclusion of the initial subobject in the stage `j` is a transfinite
composition of pushouts of monomorphic quasi-isomorphisms, hence a quasi-isomorphism by
`HomologicalComplex.monoQuasiIso.isStableUnderTransfiniteComposition`; the two-out-of-three
property then gives the invariant at the stage `j`. This handles the successor and the limit
stages uniformly.

Specialising at the canonical data `(Limits.separator C, CochainComplex.serpeCardinal C)` gives
the two statements about `CochainComplex.serpeGeneratingSet C` used to run the small object
argument in `CochainComplex C ℤ`.

## Main results

- `CochainComplex.exists_transfiniteCompositionOfShape_generatingMonoQuasiIsos`: every
  monomorphic quasi-isomorphism is a transfinite composition of pushouts of morphisms in
  `CochainComplex.generatingMonoQuasiIsos G κ`.
- `CochainComplex.generatingMonoQuasiIsos_rlp` and `CochainComplex.serpeGeneratingSet_rlp`: the
  morphisms with the right lifting property with respect to the generating family are exactly
  those with the right lifting property with respect to all monomorphic quasi-isomorphisms.
- `CochainComplex.hasSmallObjectArgument_serpeGeneratingSet`: the family
  `CochainComplex.serpeGeneratingSet C` permits the small object argument.

## References

* M. Hovey, *Cotorsion pairs, model category structures, and representation theory*, Lemma 6.7
* C. Serpé, *Resolution of unbounded complexes in Grothendieck categories*
-/

@[expose] public section

universe w v u

namespace CochainComplex

open CategoryTheory Category Limits MorphismProperty HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (κ : Cardinal.{w})

/-- Any isomorphism of cochain complexes is a pushout of a morphism of the family
`CochainComplex.generatingMonoQuasiIsos G κ`: the family contains the isomorphism
`(⊤ : Subobject Z).arrow` for a suitable `Z`. -/
lemma isomorphisms_le_pushouts_generatingMonoQuasiIsos :
    MorphismProperty.isomorphisms (CochainComplex C ℤ) ≤
      (generatingMonoQuasiIsos G κ).pushouts := by
  refine MorphismProperty.isomorphisms_le_pushouts _ (fun X ↦ ?_)
  have h : IsIso (⊤ : Subobject (cokernel (⊤ : Subobject
      ((⊤ : Subobject (diskCopower G κ)) : CochainComplex C ℤ)).arrow)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 rfl
  exact ⟨_, _, _, ⟨(⟨⊤, ⊤, ⊤, inferInstance⟩ : GeneratingMonoQuasiIsosIndex G κ)⟩, 0, h⟩

/-- Pushouts of morphisms of the family `CochainComplex.generatingMonoQuasiIsos G κ` are
monomorphic quasi-isomorphisms. -/
lemma pushouts_generatingMonoQuasiIsos_le :
    (generatingMonoQuasiIsos G κ).pushouts ≤
      HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ) := by
  rw [MorphismProperty.pushouts_le_iff]
  exact generatingMonoQuasiIsos_le G κ

namespace generatingMonoQuasiIsos

variable {B : CochainComplex C ℤ}

open scoped Classical in
/-- Given a subobject `D` of a cochain complex `B`, this is a subobject of `B` which is a
strict enlargement of `D` whose inclusion is a quasi-isomorphism and such that `D ⟶ D'` is a
pushout of a morphism of `CochainComplex.generatingMonoQuasiIsos G κ`, if such an enlargement
exists, and `⊤` otherwise. By `CochainComplex.exists_larger_subobject_quasiIso`, the second
case only occurs when `D = ⊤` or when the inclusion of `D` is not a quasi-isomorphism. -/
noncomputable def largerSubobject (D : Subobject B) : Subobject B :=
  if hD : ∃ (D' : Subobject B) (h : D < D'), QuasiIso D'.arrow ∧
    (generatingMonoQuasiIsos G κ).pushouts (Subobject.ofLE D D' h.le) then hD.choose else ⊤

/-- The subobject `D` is contained in its enlargement. -/
lemma le_largerSubobject (D : Subobject B) : D ≤ largerSubobject G κ D := by
  dsimp only [largerSubobject]
  split
  · next hD => exact hD.choose_spec.choose.le
  · exact le_top

/-- The enlargement of a subobject `D ≠ ⊤` strictly contains `D`. -/
lemma lt_largerSubobject (D : Subobject B) (hD : D ≠ ⊤) : D < largerSubobject G κ D := by
  dsimp only [largerSubobject]
  split
  · next hD' => exact hD'.choose_spec.choose
  · exact lt_top_iff_ne_top.2 hD

variable (B) in
/-- The enlargement of `⊤` is `⊤`. -/
@[simp]
lemma largerSubobject_top : largerSubobject G κ (⊤ : Subobject B) = ⊤ :=
  dite_eq_right (by rintro ⟨D', h, -⟩; exact absurd h not_top_lt)

/-- If the inclusion of `D` in `B` is a quasi-isomorphism, then the inclusion of `D` in its
enlargement is a pushout of a morphism of `CochainComplex.generatingMonoQuasiIsos G κ`. -/
lemma pushouts_ofLE_le_largerSubobject [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G) (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    (D : Subobject B) [QuasiIso D.arrow] :
    (generatingMonoQuasiIsos G κ).pushouts
      (Subobject.ofLE _ _ (le_largerSubobject G κ D)) := by
  have : Nonempty (Subobject B) := ⟨D⟩
  by_cases hD : ∃ (D' : Subobject B) (h : D < D'), QuasiIso D'.arrow ∧
      (generatingMonoQuasiIsos G κ).pushouts (Subobject.ofLE D D' h.le)
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1 hD.choose_spec.choose_spec.2
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ (by simp [largerSubobject, dite_eq_left hD]))
  · have hDtop : D = ⊤ := by
      by_contra hD'
      exact hD (exists_larger_subobject_quasiIso G κ hκ hG hsub D hD')
    subst hDtop
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject G κ (⊤ : Subobject B))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_pushouts_generatingMonoQuasiIsos G κ (𝟙 B)
          (MorphismProperty.isomorphisms.infer_property _))

/-- The transfinite iteration of the enlargement reaches `⊤` as soon as the shape `J` is too
large to embed in the lattice of subobjects of `B`. -/
lemma top_mem_range (D₀ : Subobject B) {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] (hJ : HasCardinalLT (Subobject B) (Cardinal.mk J)) :
    ∃ (j : J), transfiniteIterate (largerSubobject G κ) j D₀ = ⊤ :=
  top_mem_range_transfiniteIterate (largerSubobject G κ) D₀ (lt_largerSubobject G κ) (by simp)
    (fun h ↦ by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)

/-- The transfinite iteration of the enlargement reaches `⊤` for a suitable ordinal. -/
lemma exists_ordinal (D₀ : Subobject B) :
    ∃ (o : Ordinal.{w}) (j : o.ToType), transfiniteIterate (largerSubobject G κ) j D₀ = ⊤ := by
  have : Nonempty (Subobject B) := ⟨D₀⟩
  have : Nonempty (Shrink.{w} (Subobject B)) := ⟨equivShrink _ D₀⟩
  let c := Order.succ (Cardinal.mk (Shrink.{w} (Subobject B)))
  have : Nonempty c.ord.ToType := by simp [c]
  have := WellFoundedLT.toOrderBot c.ord.ToType
  exact ⟨c.ord, top_mem_range G κ D₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp [c]))⟩

section

variable (D₀ : Subobject B) (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- The functor `J ⥤ MonoOver B` given by the transfinite iteration of
`CochainComplex.generatingMonoQuasiIsos.largerSubobject`, evaluated at `D₀`. -/
@[simps]
noncomputable def functorToMonoOver : J ⥤ MonoOver B where
  obj j := MonoOver.mk (transfiniteIterate (largerSubobject G κ) j D₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject G κ) (leOfHom f)))

/-- The functor `J ⥤ CochainComplex C ℤ` induced by
`CochainComplex.generatingMonoQuasiIsos.functorToMonoOver`. -/
noncomputable abbrev functor : J ⥤ CochainComplex C ℤ :=
  functorToMonoOver G κ D₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

set_option backward.defeqAttrib.useBackward true in
instance : (functor G κ D₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver G κ D₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver G κ D₀ J) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject G κ) D₀ m hm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {J} in
/-- For any `j` such that the inclusions of all the earlier stages of the iteration are
quasi-isomorphisms, the map `(functor G κ D₀ J).map (homOfLE bot_le : ⊥ ⟶ j)` is a transfinite
composition of pushouts of morphisms in `CochainComplex.generatingMonoQuasiIsos G κ`. -/
noncomputable def transfiniteCompositionOfShapeMapFromBot [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ) (j : J)
    (hj : ∀ k : J, k < j → QuasiIso (transfiniteIterate (largerSubobject G κ) k D₀).arrow) :
    (generatingMonoQuasiIsos G κ).pushouts.TransfiniteCompositionOfShape (Set.Iic j)
    ((functor G κ D₀ J).map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ functor G κ D₀ J
  isoBot := Iso.refl _
  incl :=
    { app k := (functor G κ D₀ J).map (homOfLE k.2)
      naturality k k' h := by simp [MonoOver.forget] }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    have hkj : (k : J) < j := by
      refine lt_of_le_of_ne k.2 (fun h ↦ hk (fun b _ ↦ ?_))
      change (b : J) ≤ (k : J)
      rw [h]
      exact b.2
    have := hj k.1 hkj
    dsimp [MonoOver.forget]
    convert!
      pushouts_ofLE_le_largerSubobject G κ hκ hG hsub
        (transfiniteIterate (largerSubobject G κ) k.1 D₀) using 2
    all_goals
      rw [Set.Iic.succ_eq_of_not_isMax hk,
        transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]

end

section

variable {A' : CochainComplex C ℤ} (i : A' ⟶ B) [Mono i] [QuasiIso i]

omit [IsGrothendieckAbelian.{w} C] in
private lemma quasiIso_arrow_mk : QuasiIso (Subobject.mk i).arrow := by
  have : QuasiIso ((Subobject.underlyingIso i).inv ≫ (Subobject.mk i).arrow) := by
    rw [Subobject.underlyingIso_arrow]
    infer_instance
  exact quasiIso_of_comp_left (Subobject.underlyingIso i).inv _

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion of every stage of the transfinite iteration of
`CochainComplex.generatingMonoQuasiIsos.largerSubobject`, started at a monomorphic
quasi-isomorphism `i`, is again a quasi-isomorphism. -/
lemma quasiIso_arrow_transfiniteIterate [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] (j : J) :
    QuasiIso (transfiniteIterate (largerSubobject G κ) j (Subobject.mk i)).arrow := by
  induction j using WellFoundedLT.induction with
  | ind j IH =>
    have hbot : QuasiIso
        (transfiniteIterate (largerSubobject G κ) (⊥ : J) (Subobject.mk i)).arrow := by
      rw [transfiniteIterate_bot]
      exact quasiIso_arrow_mk i
    have hc := (transfiniteCompositionOfShapeMapFromBot G κ (Subobject.mk i) hκ hG hsub j
      IH).ofLE (pushouts_generatingMonoQuasiIsos_le G κ)
    have hmem := MorphismProperty.transfiniteCompositionsOfShape_le _ _ _ hc.mem
    have heq : (functor G κ (Subobject.mk i) J).map (homOfLE bot_le : ⊥ ⟶ j) ≫
        (transfiniteIterate (largerSubobject G κ) j (Subobject.mk i)).arrow =
          (transfiniteIterate (largerSubobject G κ) (⊥ : J) (Subobject.mk i)).arrow :=
      Subobject.ofLE_arrow _
    have h₁ : QuasiIso ((functor G κ (Subobject.mk i) J).map (homOfLE bot_le : ⊥ ⟶ j)) := hmem.2
    have h₂ : QuasiIso ((functor G κ (Subobject.mk i) J).map (homOfLE bot_le : ⊥ ⟶ j) ≫
        (transfiniteIterate (largerSubobject G κ) j (Subobject.mk i)).arrow) := by
      rw [heq]; exact hbot
    exact quasiIso_of_comp_left
      ((functor G κ (Subobject.mk i) J).map (homOfLE bot_le : ⊥ ⟶ j)) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If some stage of the transfinite iteration reaches `⊤`, then `i` is a transfinite
composition of pushouts of morphisms in `CochainComplex.generatingMonoQuasiIsos G κ`. -/
noncomputable def transfiniteCompositionOfShapeOfEqTop [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] {j : J}
    (hj : transfiniteIterate (largerSubobject G κ) j (Subobject.mk i) = ⊤) :
    (generatingMonoQuasiIsos G κ).pushouts.TransfiniteCompositionOfShape (Set.Iic j) i := by
  let t := transfiniteIterate (largerSubobject G κ) j (Subobject.mk i)
  have := (Subobject.isIso_arrow_iff_eq_top t).2 hj
  apply (transfiniteCompositionOfShapeMapFromBot G κ (Subobject.mk i) hκ hG hsub j
    (fun k _ ↦ quasiIso_arrow_transfiniteIterate G κ i hκ hG hsub k)).ofArrowIso
  refine Arrow.isoMk ((Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso i)) (asIso t.arrow) ?_
  dsimp [MonoOver.forget]
  rw [assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow]

end

end generatingMonoQuasiIsos

/-- Every monomorphic quasi-isomorphism of cochain complexes in a Grothendieck abelian
category is a transfinite composition of pushouts of morphisms in the small family
`CochainComplex.generatingMonoQuasiIsos G κ`. -/
lemma exists_transfiniteCompositionOfShape_generatingMonoQuasiIsos [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    {A' B : CochainComplex C ℤ} (i : A' ⟶ B) [Mono i] [QuasiIso i] :
    ∃ (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty ((generatingMonoQuasiIsos G κ).pushouts.TransfiniteCompositionOfShape J i) := by
  obtain ⟨o, j, hj⟩ := generatingMonoQuasiIsos.exists_ordinal G κ (Subobject.mk i)
  have : Nonempty o.ToType := ⟨j⟩
  have : OrderBot o.ToType := WellFoundedLT.toOrderBot _
  exact ⟨_, _, _, _, _,
    ⟨generatingMonoQuasiIsos.transfiniteCompositionOfShapeOfEqTop G κ i hκ hG hsub hj⟩⟩

/-- A morphism of cochain complexes has the right lifting property with respect to the family
`CochainComplex.generatingMonoQuasiIsos G κ` if and only if it has the right lifting property
with respect to all monomorphic quasi-isomorphisms. -/
lemma generatingMonoQuasiIsos_rlp [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ) :
    (generatingMonoQuasiIsos G κ).rlp =
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ)).rlp := by
  apply le_antisymm
  · intro X Y p hp A' B i hi
    have h₁ : Mono i := hi.1
    have h₂ : QuasiIso i := hi.2
    obtain ⟨J, _, _, _, _, ⟨h⟩⟩ :=
      exists_transfiniteCompositionOfShape_generatingMonoQuasiIsos G κ hκ hG hsub i
    exact MorphismProperty.transfiniteCompositionsOfShape_le_llp_rlp _ _ _ h.mem _ (by simpa)
  · exact MorphismProperty.antitone_rlp (generatingMonoQuasiIsos_le G κ)

attribute [local instance] fact_isRegular_serpeCardinal

variable (C) in
/-- A morphism of cochain complexes has the right lifting property with respect to the Serpé
generating set if and only if it has the right lifting property with respect to all
monomorphic quasi-isomorphisms. -/
lemma serpeGeneratingSet_rlp :
    (serpeGeneratingSet C).rlp =
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ)).rlp := by
  dsimp only [serpeGeneratingSet]
  exact generatingMonoQuasiIsos_rlp _ _ (aleph0_lt_serpeCardinal.{w} C)
    (isSeparator_separator C) (hasCardinalLT_subobject_serpeCardinal.{w} C)

variable (C) in
instance hasSmallObjectArgument_serpeGeneratingSet :
    MorphismProperty.HasSmallObjectArgument.{w} (serpeGeneratingSet C) := by
  dsimp only [serpeGeneratingSet]
  infer_instance

end CochainComplex
