/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Strict representatives of derived squares -/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false

private theorem lift_to_complex
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) (Y : CochainComplex C ℤ)
    (f : X ⟶ DerivedCategory.Q.obj Y) :
    ∃ (K : CochainComplex C ℤ) (g : K ⟶ Y) (e : DerivedCategory.Q.obj K ≅ X),
      DerivedCategory.Q.map g = e.hom ≫ f := by
  let eX := DerivedCategory.Q.objObjPreimageIso X
  obtain ⟨K, t, ht, g, hg⟩ := DerivedCategory.right_fac (eX.hom ≫ f)
  have := ht
  refine ⟨K, g, asIso (DerivedCategory.Q.map t) ≪≫ eX, ?_⟩
  dsimp only [Iso.trans_hom, asIso_hom]
  rw [Category.assoc, hg, IsIso.hom_inv_id_assoc]

/-- A commuting derived square admits representatives commuting up to chain homotopy.

Source: Stacks Project, Derived Categories, Tag 05RR (localization of the homotopy
category at quasi-isomorphisms); Mathlib `DerivedCategory.right_fac` and the
right-fraction equality criterion.

Proof: Choose complexes for X,Y,X',Y'. Fix the complex for the sink Y'. Use right
fractions to replace the representatives of Y and X' so that b and f' are chain
maps into this fixed sink. Lift f into the new Y, and a into the new X', by right
fractions. Take a common right denominator of these two roofs out of X. Both
composites then have chain representatives from this common source to the fixed
sink. The equality f b = a f' in the localization gives a further right
denominator after which the two composites agree in the homotopy category.
Choose a chain representative of this denominator and precompose both arrows
out of X. The quotient functor's equality criterion supplies a chain homotopy
between the composites. Compose the denominator isomorphisms with the original
object comparisons to get eX,eY,eX',eY'. Each of the four map equations follows
from its roof factorization. This argument applies without bounds or enough
injectives, and includes zero objects. -/
private theorem derived_homotopy_square_lift
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y X' Y' : DerivedCategory C}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') :
    ∃ (K L K' L' : CochainComplex C ℤ)
      (g : K ⟶ L) (g' : K' ⟶ L') (s : K ⟶ K') (t : L ⟶ L')
      (_hc : Homotopy (g ≫ t) (s ≫ g'))
      (eX : DerivedCategory.Q.obj K ≅ X) (eY : DerivedCategory.Q.obj L ≅ Y)
      (eX' : DerivedCategory.Q.obj K' ≅ X') (eY' : DerivedCategory.Q.obj L' ≅ Y'),
      DerivedCategory.Q.map g ≫ eY.hom = eX.hom ≫ f ∧
      DerivedCategory.Q.map g' ≫ eY'.hom = eX'.hom ≫ f' ∧
      DerivedCategory.Q.map s ≫ eX'.hom = eX.hom ≫ a ∧
      DerivedCategory.Q.map t ≫ eY'.hom = eY.hom ≫ b := by
  let L₀ := DerivedCategory.Q.objPreimage Y'
  let e₀ := DerivedCategory.Q.objObjPreimageIso Y'
  obtain ⟨L, r, eY, hb₀⟩ := lift_to_complex Y L₀ (b ≫ e₀.inv)
  obtain ⟨K', g', eX', hg'₀⟩ := lift_to_complex X' L₀ (f' ≫ e₀.inv)
  have hb : DerivedCategory.Q.map r ≫ e₀.hom = eY.hom ≫ b := by
    rw [hb₀]
    simp
  have hg' : DerivedCategory.Q.map g' ≫ e₀.hom = eX'.hom ≫ f' := by
    rw [hg'₀]
    simp
  obtain ⟨K₁, s₁, e₁, ha₀⟩ := lift_to_complex X K' (a ≫ eX'.inv)
  have ha₁ : DerivedCategory.Q.map s₁ ≫ eX'.hom = e₁.hom ≫ a := by
    rw [ha₀]
    simp
  obtain ⟨K, d, hd, g, hg₀⟩ :=
    DerivedCategory.right_fac (e₁.hom ≫ f ≫ eY.inv)
  have := hd
  let eX : DerivedCategory.Q.obj K ≅ X := asIso (DerivedCategory.Q.map d) ≪≫ e₁
  let s := d ≫ s₁
  have hg : DerivedCategory.Q.map g ≫ eY.hom = eX.hom ≫ f := by
    change DerivedCategory.Q.map g ≫ eY.hom =
      (DerivedCategory.Q.map d ≫ e₁.hom) ≫ f
    calc
      DerivedCategory.Q.map g ≫ eY.hom =
          DerivedCategory.Q.map d ≫ (inv (DerivedCategory.Q.map d) ≫
            DerivedCategory.Q.map g) ≫ eY.hom := by simp
      _ = DerivedCategory.Q.map d ≫ (e₁.hom ≫ f ≫ eY.inv) ≫ eY.hom := by rw [← hg₀]
      _ = _ := by simp [Category.assoc]
  have ha : DerivedCategory.Q.map s ≫ eX'.hom = eX.hom ≫ a := by
    simp [s, eX, ha₁, Category.assoc]
  have heq : DerivedCategory.Q.map (g ≫ r) = DerivedCategory.Q.map (s ≫ g') := by
    apply (cancel_mono e₀.hom).mp
    simp only [Functor.map_comp, Category.assoc, hb, hg', reassoc_of% hg,
      reassoc_of% ha, h]
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have heqh : DerivedCategory.Qh.map (q.map (g ≫ r)) =
      DerivedCategory.Qh.map (q.map (s ≫ g')) := by
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L₀)).mp
    simpa only [q, DerivedCategory.quotientCompQhIso_hom_naturality] using
      congrArg (fun f ↦ (DerivedCategory.quotientCompQhIso C).hom.app K ≫ f) heq
  obtain ⟨P, d₀, hd₀, hcomp⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _).mp heqh
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  obtain ⟨d₀, rfl⟩ := q.map_surjective d₀
  have hd₀' : IsIso (DerivedCategory.Q.map d₀) := by
    apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) d₀).mp
    exact (DerivedCategory.isIso_Qh_map_iff _).mpr hd₀
  have := hd₀'
  have H : Homotopy ((d₀ ≫ g) ≫ r) ((d₀ ≫ s) ≫ g') :=
    HomotopyCategory.homotopyOfEq _ _ (by
      simpa only [Functor.map_comp, Category.assoc] using hcomp)
  refine ⟨P, L, K', L₀, d₀ ≫ g, g', d₀ ≫ s, r, H,
    asIso (DerivedCategory.Q.map d₀) ≪≫ eX, eY, eX', e₀, ?_, hg', ?_, hb⟩
  · simpa only [Functor.map_comp, Iso.trans_hom, asIso_hom, Category.assoc] using
      congrArg (fun k ↦ DerivedCategory.Q.map d₀ ≫ k) hg
  · simpa only [Functor.map_comp, Iso.trans_hom, asIso_hom, Category.assoc] using
      congrArg (fun k ↦ DerivedCategory.Q.map d₀ ≫ k) ha


/-- Any commuting square in a derived category has a strict square of complex
representatives, allowing all four representatives to vary.

Source: Stacks Project, Derived Categories, Tag 05RR (fractions) and Tag 014D,
Lemmas 13.9.5 and 13.9.6 (homotopy adjustment and cylinder factorization).
(blueprint: lem-pc-derived-commutative-square-lift).

Proof: Choose complexes for the four objects. Express the four derived maps by
roofs in the homotopy category. Common refinements first give representatives of
the two horizontal and two vertical arrows, and then witness the equality of the
composites. Lift the resulting maps to chain maps and the equality to a homotopy.
Replace its top-right complex L by L direct-sum Cone(id K). Replace the top
arrow g by the pair (g,inr(id K)). The homotopy gives a map z from Cone(id K)
to L' whose restriction to K is s g' - g r; take the right arrow to be (r,z).
The resulting square commutes strictly by addition. Cone(id K) is contractible,
so the projection onto L becomes an isomorphism in the derived category, and
z becomes zero. Thus the four localized maps agree with the original square.
No boundedness
or injective resolutions are required, and zero complexes cause no exception. -/
theorem derived_commutative_square_lift
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y X' Y' : DerivedCategory C}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') :
    ∃ (K L K' L' : CochainComplex C ℤ)
      (g : K ⟶ L) (g' : K' ⟶ L') (s : K ⟶ K') (t : L ⟶ L')
      (_hc : g ≫ t = s ≫ g')
      (eX : DerivedCategory.Q.obj K ≅ X) (eY : DerivedCategory.Q.obj L ≅ Y)
      (eX' : DerivedCategory.Q.obj K' ≅ X') (eY' : DerivedCategory.Q.obj L' ≅ Y'),
      DerivedCategory.Q.map g ≫ eY.hom = eX.hom ≫ f ∧
      DerivedCategory.Q.map g' ≫ eY'.hom = eX'.hom ≫ f' ∧
      DerivedCategory.Q.map s ≫ eX'.hom = eX.hom ≫ a ∧
      DerivedCategory.Q.map t ≫ eY'.hom = eY.hom ≫ b := by
  obtain ⟨K, L, K', L', g, g', s, r, H, eX, eY, eX', eY', hg, hg', ha, hb⟩ :=
    derived_homotopy_square_lift f f' a b h
  let z : CochainComplex.mappingCone (𝟙 K) ⟶ L' :=
    CochainComplex.mappingCone.desc (𝟙 K)
      (CochainComplex.HomComplex.Cochain.ofHomotopy H.symm) (s ≫ g' - g ≫ r)
      (by simp)
  let i : K ⟶ L ⊞ CochainComplex.mappingCone (𝟙 K) :=
    biprod.lift g (CochainComplex.mappingCone.inr (𝟙 K))
  let r' : L ⊞ CochainComplex.mappingCone (𝟙 K) ⟶ L' := biprod.desc r z
  have hi : i ≫ r' = s ≫ g' := by
    dsimp [i, r', z]
    simp
  have hz : DerivedCategory.Q.map z = 0 := by
    have hh := DerivedCategory.Q_map_eq_of_homotopy C
      (CochainComplex.mappingCone.homotopyToZeroOfId K)
    have hh' := congrArg (fun q ↦ q ≫ DerivedCategory.Q.map z) hh
    simpa using hh'
  let j : DerivedCategory.Q.obj (L ⊞ CochainComplex.mappingCone (𝟙 K)) ≅
      DerivedCategory.Q.obj L :=
    { hom := DerivedCategory.Q.map biprod.fst
      inv := DerivedCategory.Q.map biprod.inl
      hom_inv_id := by
        have hh := DerivedCategory.Q_map_eq_of_homotopy C
          (CochainComplex.mappingCone.homotopyToZeroOfId K)
        have hz' : DerivedCategory.Q.map
            (biprod.inr : CochainComplex.mappingCone (𝟙 K) ⟶
              L ⊞ CochainComplex.mappingCone (𝟙 K)) = 0 := by
          have hh' := congrArg (fun q ↦ q ≫ DerivedCategory.Q.map
            (biprod.inr : CochainComplex.mappingCone (𝟙 K) ⟶
              L ⊞ CochainComplex.mappingCone (𝟙 K))) hh
          simpa using hh'
        have ht := congrArg (fun q ↦ DerivedCategory.Q.map q)
          (biprod.total (X := L) (Y := CochainComplex.mappingCone (𝟙 K)))
        simpa only [Functor.map_add, Functor.map_comp, CategoryTheory.Functor.map_id, hz',
          comp_zero, add_zero] using ht
      inv_hom_id := by
        rw [← Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id] }
  refine ⟨K, _, K', L', i, g', s, r', hi, eX, j ≪≫ eY, eX', eY', ?_, hg', ha, ?_⟩
  · change DerivedCategory.Q.map i ≫ (DerivedCategory.Q.map biprod.fst ≫ eY.hom) = _
    rw [← Category.assoc, ← Functor.map_comp]
    simpa [i] using hg
  · change DerivedCategory.Q.map r' ≫ eY'.hom =
      (DerivedCategory.Q.map biprod.fst ≫ eY.hom) ≫ b
    have hr : DerivedCategory.Q.map r' =
        DerivedCategory.Q.map biprod.fst ≫ DerivedCategory.Q.map r := by
      simp [r', biprod.desc_eq, hz]
    rw [hr, Category.assoc, hb, Category.assoc]
