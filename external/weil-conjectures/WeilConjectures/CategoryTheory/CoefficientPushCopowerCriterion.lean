/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # A coefficient push comparison detects copower continuity

Source: the finite-basis mate calculation in
`WeilConjectures/CategoryTheory/Adjunction/ProjectionMapMate.lean`, BaseChange section.
This version allows an arbitrary basis and makes its required copower comparison explicit.
-/

@[expose] public section

universe vA vB vA' vB' uA uB uA' uB' w

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

set_option backward.isDefEq.respectTransparency false

/-- A scalar-basis decomposition identifies invertibility of a coefficient push mate
with invertibility of the corresponding copower comparison.

Source: `ProjectionMapMate.lean`, `isIso_mateEquiv_app_of_isIso_biproductDesc`, with the
finite biproduct calculation replaced by a coproduct calculation.
(auxiliary; not a blueprint node)

Proof: write β' for the mate of β. The unit-mate identity and compatibility with each
basis scalar identify U_D(β_M), conjugated by the two basis decompositions, with the
copower comparison followed by G of the source basis decomposition and β' at N_C(M).
Check this equality on each coprojection. The latter two factors are isomorphisms, as
are both basis decompositions. Thus the copower comparison is invertible exactly when
U_D(β_M) is. Reflection of isomorphisms by U_D gives the stated equivalence. No
preservation of infinite coproducts by G is assumed or inferred without this comparison. -/
theorem isIso_iff_unitCoproductComparison
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {A' : Type uA'} [Category.{vA'} A'] {B' : Type uB'} [Category.{vB'} B']
    {N_C : A ⥤ B} {R_C : B ⥤ A} (adj_C : N_C ⊣ R_C)
    {N_D : A' ⥤ B'} {R_D : B' ⥤ A'} (adj_D : N_D ⊣ R_D)
    {G : A ⥤ A'} {G' : B ⥤ B'} [R_D.ReflectsIsomorphisms]
    (β : G ⋙ N_D ⟶ N_C ⋙ G')
    (hκ : IsIso (mateEquiv adj_C adj_D β)) (M : A) (I : Type w)
    [HasCoproduct (fun _ : I ↦ M)] [HasCoproduct (fun _ : I ↦ G.obj M)]
    (e : I → (N_C.obj M ⟶ N_C.obj M))
    (e' : I → (N_D.obj (G.obj M) ⟶ N_D.obj (G.obj M)))
    (he : ∀ i, e' i ≫ β.app M = β.app M ≫ G'.map (e i))
    [IsIso (Sigma.desc fun i ↦ (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i))]
    [IsIso (Sigma.desc fun i ↦ (show G.obj M ⟶ R_D.obj (N_D.obj (G.obj M)) from
          adj_D.unit.app (G.obj M)) ≫ R_D.map (e' i))] :
    IsIso (β.app M) ↔
      IsIso (Sigma.desc fun i ↦ G.map (Sigma.ι (fun _ : I ↦ M) i)) := by
  let β' := mateEquiv adj_C adj_D β
  have : IsIso β' := hκ
  have hu := unit_mateEquiv adj_C adj_D β M
  dsimp at hu
  have key : (Sigma.desc fun i ↦ (show G.obj M ⟶ R_D.obj (N_D.obj (G.obj M)) from
          adj_D.unit.app (G.obj M)) ≫ R_D.map (e' i)) ≫
      R_D.map (β.app M) =
      (Sigma.desc fun i ↦ G.map (Sigma.ι (fun _ : I ↦ M) i)) ≫
        G.map (Sigma.desc fun i ↦ (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i)) ≫
          β'.app (N_C.obj M) := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Category.assoc, ← G.map_comp_assoc, Sigma.ι_comp_desc]
    rw [← R_D.map_comp, he, R_D.map_comp, ← reassoc_of% hu,
      G.map_comp, Category.assoc]
    congr 1
    exact (β'.naturality (e i)).symm
  have hb : IsIso (β'.app (N_C.obj M)) :=
    NatIso.isIso_app_of_isIso (β' : NatTrans _ _) _
  have hs : IsIso (G.map (Sigma.desc fun i ↦
      (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i))) := Functor.map_isIso _ _
  have htail : IsIso (G.map (Sigma.desc fun i ↦
      (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i)) ≫ β'.app (N_C.obj M)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hs hb
  constructor
  · intro hβ
    have : IsIso (β.app M) := hβ
    have h : IsIso ((Sigma.desc fun i ↦ G.map (Sigma.ι (fun _ : I ↦ M) i)) ≫
        G.map (Sigma.desc fun i ↦ (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i)) ≫
          β'.app (N_C.obj M)) := by
      rw [← key]
      infer_instance
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ htail h
  · intro hc
    have : IsIso (Sigma.desc fun i ↦ G.map (Sigma.ι (fun _ : I ↦ M) i)) := hc
    have : IsIso ((Sigma.desc fun i ↦ (show G.obj M ⟶ R_D.obj (N_D.obj (G.obj M)) from
          adj_D.unit.app (G.obj M)) ≫ R_D.map (e' i)) ≫
        R_D.map (β.app M)) := by
      rw [key]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hc
        (@IsIso.comp_isIso _ _ _ _ _ _ _ hs hb)
    have : IsIso (R_D.map (β.app M)) := IsIso.of_isIso_comp_left
      (Sigma.desc fun i ↦ (show G.obj M ⟶ R_D.obj (N_D.obj (G.obj M)) from
          adj_D.unit.app (G.obj M)) ≫ R_D.map (e' i)) _
    exact isIso_of_reflects_iso _ R_D

end CategoryTheory.Adjunction
