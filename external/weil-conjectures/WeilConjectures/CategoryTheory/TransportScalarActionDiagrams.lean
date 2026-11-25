/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Transport of the two monoid action diagrams

Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-transport-scalar-action-diagrams). -/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def actionPair
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (L : C ⥤ D) [PreservesFiniteLimits L]
    {X Y : C} {X' Y' : D} (ex : X' ≅ L.obj X) (ey : Y' ≅ L.obj Y) :
    X' ⨯ Y' ⟶ L.obj (X ⨯ Y) :=
  prod.map ex.hom ey.hom ≫ inv (prodComparison L X Y)

private theorem actionPair_fst
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (L : C ⥤ D) [PreservesFiniteLimits L]
    {X Y : C} {X' Y' : D} (ex : X' ≅ L.obj X) (ey : Y' ≅ L.obj Y) :
    actionPair L ex ey ≫ L.map prod.fst = prod.fst ≫ ex.hom := by
  simp [actionPair, Category.assoc, inv_prodComparison_map_fst]

private theorem actionPair_snd
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (L : C ⥤ D) [PreservesFiniteLimits L]
    {X Y : C} {X' Y' : D} (ex : X' ≅ L.obj X) (ey : Y' ≅ L.obj Y) :
    actionPair L ex ey ≫ L.map prod.snd = prod.snd ≫ ey.hom := by
  simp [actionPair, Category.assoc, inv_prodComparison_map_snd]

private theorem actionPair_lift
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (L : C ⥤ D) [PreservesFiniteLimits L]
    {X Y T : C} {X' Y' Z : D} (ex : X' ≅ L.obj X) (ey : Y' ≅ L.obj Y)
    (t : Z ⟶ L.obj T) (f : T ⟶ X) (g : T ⟶ Y) (a : Z ⟶ X') (b : Z ⟶ Y')
    (ha : a ≫ ex.hom = t ≫ L.map f) (hb : b ≫ ey.hom = t ≫ L.map g) :
    prod.lift a b ≫ actionPair L ex ey = t ≫ L.map (prod.lift f g) := by
  apply (cancel_mono (prodComparison L X Y)).1
  apply prod.hom_ext
  · simpa [actionPair, Category.assoc, ← L.map_comp] using ha
  · simpa [actionPair, Category.assoc, ← L.map_comp] using hb

/-- Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-transport-scalar-action-diagrams).

Proof: Apply L to the two given source action equations. Compare the image of
(RV times RV) times AV with (RU times RU) times AU using the inverse binary
product comparisons and er and ea. Its projections identify the image of the
left associative composite with multiplication on RU followed by mu, using
hMul. The projections identify the right composite with the nested mu
composite. Cancel ea.hom to obtain the associative equation. For the unit
composite use the unique map to the terminal object, its preserved terminal
comparison and hOne; cancel ea.hom again. Only product and terminal universal
properties are used; there is no assumption about addition or commutativity. -/
theorem transportScalarActionDiagrams
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (L : C ⥤ D) [PreservesFiniteLimits L]
    (RV AV : C) (RU AU : D) (er : RU ≅ L.obj RV) (ea : AU ≅ L.obj AV)
    (mulV : RV ⨯ RV ⟶ RV) (mulU : RU ⨯ RU ⟶ RU)
    (oneV : ⊤_ C ⟶ RV) (oneU : ⊤_ D ⟶ RU) (muV : RV ⨯ AV ⟶ AV)
    (hMul : L.map mulV = prodComparison L RV RV ≫
      prod.map er.inv er.inv ≫ mulU ≫ er.hom)
    (hOne : L.map oneV = terminal.from _ ≫ oneU ≫ er.hom)
    (hAssoc : prod.map mulV (𝟙 AV) ≫ muV =
      prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ muV) ≫ muV)
    (hUnit : prod.lift (terminal.from AV ≫ oneV) (𝟙 AV) ≫ muV = 𝟙 AV) :
    let mu := prod.map er.hom ea.hom ≫ inv (prodComparison L RV AV) ≫
      L.map muV ≫ ea.inv
    (prod.map mulU (𝟙 AU) ≫ mu =
      prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ mu) ≫ mu) ∧
    (prod.lift (terminal.from AU ≫ oneU) (𝟙 AU) ≫ mu = 𝟙 AU)  := by
  dsimp only
  let k := actionPair L er ea
  let er2 : RU ⨯ RU ≅ L.obj (RV ⨯ RV) :=
    prod.mapIso er er ≪≫ (asIso (prodComparison L RV RV)).symm
  let t := actionPair L er2 ea
  let mu := prod.map er.hom ea.hom ≫ inv (prodComparison L RV AV) ≫ L.map muV ≫ ea.inv
  have hm : actionPair L er er ≫ L.map mulV = mulU ≫ er.hom := by
    simp only [hMul, actionPair, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, prod.map_map]
    simp
  have ha : mu ≫ ea.hom = k ≫ L.map muV := by simp [mu, k, actionPair, Category.assoc]
  have tf : t ≫ L.map prod.fst = prod.fst ≫ actionPair L er er :=
    actionPair_fst L er2 ea
  have ts : t ≫ L.map prod.snd = prod.snd ≫ ea.hom := actionPair_snd L er2 ea
  have tf1 : t ≫ L.map (prod.fst ≫ prod.fst) =
      (prod.fst ≫ prod.fst) ≫ er.hom := by
    rw [L.map_comp, ← Category.assoc, tf, Category.assoc, actionPair_fst]
    simp only [Category.assoc]
  have tf2 : t ≫ L.map (prod.fst ≫ prod.snd) =
      (prod.fst ≫ prod.snd) ≫ er.hom := by
    rw [L.map_comp, ← Category.assoc, tf, Category.assoc, actionPair_snd]
    simp only [Category.assoc]
  have hleft : prod.map mulU (𝟙 AU) ≫ k = t ≫ L.map (prod.map mulV (𝟙 AV)) := by
    have hh := actionPair_lift L er ea t (prod.fst ≫ mulV) prod.snd
      (prod.fst ≫ mulU) prod.snd
      (by rw [L.map_comp, ← Category.assoc, tf]
          simpa only [Category.assoc] using congrArg (fun z ↦ prod.fst ≫ z) hm.symm) ts.symm
    have hmV : prod.lift (prod.fst ≫ mulV) prod.snd = prod.map mulV (𝟙 AV) := by
      apply prod.hom_ext <;> simp
    have hmU : prod.lift (prod.fst ≫ mulU) prod.snd = prod.map mulU (𝟙 AU) := by
      apply prod.hom_ext <;> simp
    rw [hmV, hmU] at hh
    exact hh
  have hinner : prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ k =
      t ≫ L.map (prod.lift (prod.fst ≫ prod.snd) prod.snd) :=
    actionPair_lift L er ea t _ _ _ _ tf2.symm ts.symm
  have hright : prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ mu) ≫ k =
      t ≫ L.map (prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ muV)) := by
    apply actionPair_lift L er ea t _ _ _ _ tf1.symm
    rw [Category.assoc, ha, ← Category.assoc, hinner, Category.assoc, ← L.map_comp]
  constructor
  · apply (cancel_mono ea.hom).1
    change (prod.map mulU (𝟙 AU) ≫ mu) ≫ ea.hom =
      (prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ mu) ≫ mu) ≫ ea.hom
    rw [Category.assoc, ha, ← Category.assoc, hleft, Category.assoc, ← L.map_comp,
      hAssoc, L.map_comp, ← Category.assoc, ← hright, Category.assoc, ← ha]
    simp only [Category.assoc]
  · have hu : prod.lift (terminal.from AU ≫ oneU) (𝟙 AU) ≫ k =
        ea.hom ≫ L.map (prod.lift (terminal.from AV ≫ oneV) (𝟙 AV)) := by
      apply actionPair_lift L er ea ea.hom _ _ _ _
      · rw [L.map_comp, hOne]
        simp only [Category.assoc]
        have hh : terminal.from AU = ea.hom ≫ L.map (terminal.from AV) ≫
            terminal.from (L.obj (⊤_ C)) := Subsingleton.elim _ _
        rw [hh]
        simp only [Category.assoc]
      · simp
    apply (cancel_mono ea.hom).1
    change (prod.lift (terminal.from AU ≫ oneU) (𝟙 AU) ≫ mu) ≫ ea.hom =
      (𝟙 AU) ≫ ea.hom
    rw [Category.assoc, ha, ← Category.assoc, hu, Category.assoc,
      ← L.map_comp, hUnit, L.map_id]
    simp

end CategoryTheory
