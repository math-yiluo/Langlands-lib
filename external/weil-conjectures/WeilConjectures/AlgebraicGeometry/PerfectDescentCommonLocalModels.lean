/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.PerfectDescentOpenEventualModel

/-! # Two local perfect models at a common stage

Source: Stacks Project, Tag 09RF, the choice of E_{U,i} and E_{V,i}.
(blueprint: lem-pc-perfect-descent-common-local-models).
-/

@[expose] public section


universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Eliminate the common upper bound while the target is an abstract proposition.
private theorem of_common_upper_bound
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] (a b : I) {P : Prop}
    (h : ∀ k : I, a ≤ k → b ≤ k → P) : P := by
  obtain ⟨k, hak, hbk⟩ := exists_ge_ge a b
  exact h k hak hbk

/-- Descend the two restrictions separately and move them to a common stage.
This supplies no overlap isomorphism and no map into a derived direct image.
Source: Stacks Project, Tag 09RF, first sentence of the two-open induction.
(blueprint: lem-pc-perfect-descent-common-local-models).

Proof: Pull W and V back along f, and then along the projection of the limit
base change. Restriction of E is perfect by Tag 09UA and the derived open
restriction comparison. The presentations (f inverse W).toScheme → Xi and
(f inverse V).toScheme → Xi have images W and V because hf says their union
is the image of f. Apply dW and dV to these presentations and restricted objects.
Choose a common upper bound of the resulting indices. Pull the stage models
back to this stage; they remain perfect by Tag 09UA. The cartesian identifications
of each restricted base change with the corresponding stage open, and coherent
composition of derived pullbacks, give the two displayed comparison isomorphisms.
The opens cover since inverse image preserves joins and top. They are compact:
f has compact image W union V, hence has compact source; Xi is quasi-separated
since s is quasi-separated and its base is affine. Thus f is quasi-compact, and
its inverse images of W and V are compact. The stage projection to Z is affine
as a base change of a morphism of affine schemes, so these opens remain compact.
Empty or coincident opens cause no exception, and i ensures a nonempty index set.
-/
theorem perfect_descent_common_local_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (W V : Xi.Opens) (hW : IsCompact (W : Set Xi)) (hV : IsAffineOpen V)
    (dW : PerfectDescentOnOpen R c i Xi s W)
    (dV : PerfectDescentOnOpen R c i Xi s V)
    (Z : Scheme.{u}) (f : Z ⟶ Xi) [IsOpenImmersion f] (hf : f.opensRange = W ⊔ V)
    (E : schemeDerivedCategory (pullback (f ≫ s) (Spec.map (c.ι.app i))))
    (hE : (pullback (f ≫ s) (Spec.map (c.ι.app i))).IsPerfect E) :
    ∃ (j : I) (hij : i ≤ j),
      let Y := pullback (f ≫ s) (Spec.map (R.map (homOfLE hij)))
      let X := pullback (f ≫ s) (Spec.map (c.ι.app i))
      let g := baseChangeMap (f ≫ s)
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
      ∃ (U V : Y.Opens), U ⊔ V = ⊤ ∧
        IsCompact (U : Set Y) ∧ IsCompact (V : Set Y) ∧
      ∃ (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme),
        U.toScheme.IsPerfect A ∧ V.toScheme.IsPerfect B ∧
        Nonempty ((derivedPullback (g ∣_ U)).obj A ≅
          (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E) ∧
        Nonempty ((derivedPullback (g ∣_ V)).obj B ≅
          (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) := by
  have hrange : IsCompact (Set.range f) := by
    change IsCompact (f.opensRange : Set Xi)
    rw [hf]
    exact hW.union hV.isCompact
  let : CompactSpace Z := by
    rw [← isCompact_univ_iff]
    apply f.isOpenEmbedding.isEmbedding.isCompact_iff.mpr
    simpa only [Set.image_univ] using hrange
  let : QuasiSeparatedSpace Xi := quasiSeparatedSpace_of_quasiSeparated s
  let : QuasiCompact f := quasiCompact_of_compactSpace f
  have hWr : W ≤ f.opensRange := by rw [hf]; exact le_sup_left
  have hVr : V ≤ f.opensRange := by rw [hf]; exact le_sup_right
  have stepW := perfect_descent_open_eventual_model.{u, w}
    (R := R) (c := c) (i := i) (Xi := Xi) (s := s)
    (W := W) (dW := dW) (Z := Z) (f := f) (hW := hWr) (E := E) (hE := hE)
  have stepV := perfect_descent_open_eventual_model.{u, w}
    (R := R) (c := c) (i := i) (Xi := Xi) (s := s)
    (W := V) (dW := dV) (Z := Z) (f := f) (hW := hVr) (E := E) (hE := hE)
  obtain ⟨jW, hiW, mW⟩ := stepW
  obtain ⟨jV, hiV, mV⟩ := stepV
  refine of_common_upper_bound jW jV fun k hWk hVk ↦ ?_
  let hik := hiW.trans hWk
  let Y := pullback (f ≫ s) (Spec.map (R.map (homOfLE hik)))
  let p : Y ⟶ Z := pullback.fst (f ≫ s) (Spec.map (R.map (homOfLE hik)))
  let U := (p ≫ f) ⁻¹ᵁ W
  let V' := (p ≫ f) ⁻¹ᵁ V
  have hcover : U ⊔ V' = ⊤ := by
    dsimp only [U, V']
    rw [← Scheme.Hom.preimage_sup, hf.symm, Scheme.Hom.comp_preimage]
    simp only [Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]
  have hU : IsCompact (U : Set Y) := by
    exact (p ≫ f).isCompact_preimage hW
  have hV' : IsCompact (V' : Set Y) := by
    exact (p ≫ f).isCompact_preimage hV.isCompact
  refine ⟨k, hik, U, V', hcover, hU, hV', ?_⟩
  have dataW := mW k hWk
  have dataV := mV k hVk
  obtain ⟨A, hA, eA⟩ := dataW
  obtain ⟨B, hB, eB⟩ := dataV
  exact ⟨A, B, hA, hB, eA, eB⟩

end AlgebraicGeometry
