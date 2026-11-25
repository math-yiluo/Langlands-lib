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

import WeilConjectures.CategoryTheory.NaturalTruncationCouple
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-! # A coproduct comparison of truncation exact couples

Source: Stacks Project, Tags 015J, 05TC and 08DZ; the exact-couple construction and
coproduct glue of lem-pc-bounded-below-coproduct-filtration, Steps 1 and 2
(blueprint: lem-pc-coproduct-truncation-couple).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Exact coproducts preserve a family of exact pairs. -/
private theorem exact_sigma
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    {I : Type v} {U V W : I → B}
    (f : ∀ i, U i ⟶ V i) (g : ∀ i, V i ⟶ W i)
    (h : ∀ i, f i ≫ g i = 0)
    (he : ∀ i, (ShortComplex.mk (f i) (g i) (h i)).Exact) :
    ∃ w : Limits.Sigma.map f ≫ Limits.Sigma.map g = 0,
      (ShortComplex.mk (Limits.Sigma.map f) (Limits.Sigma.map g) w).Exact := by
  let f' : Discrete.functor U ⟶ Discrete.functor V :=
    Discrete.natTrans (fun i ↦ f i.as)
  let g' : Discrete.functor V ⟶ Discrete.functor W :=
    Discrete.natTrans (fun i ↦ g i.as)
  let S : ShortComplex (Discrete I ⥤ B) :=
    ShortComplex.mk f' g' (by ext i; simpa [f', g'] using h i.as)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    ext i
    have hi : (S.map ((evaluation (Discrete I) B).obj i)).Exact := he i.as
    exact (IsZero.of_iso
      (ShortComplex.exact_iff_isZero_homology _ |>.mp hi)
      (S.mapHomologyIso ((evaluation (Discrete I) B).obj i)).symm).eq_of_src _ _
  have w : Limits.Sigma.map f ≫ Limits.Sigma.map g = 0 := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_map_assoc, Sigma.ι_map, ← Category.assoc, h i, zero_comp, comp_zero]
  refine ⟨w, ?_⟩
  exact colim.exact_mapShortComplex (S := S) hS (colimit.isColimit _)
    (colimit.isColimit _) (colimit.isColimit _)
    (Limits.Sigma.map f)
    (Limits.Sigma.map g) (fun i ↦ Sigma.ι_map f i.as)
    (fun i ↦ Sigma.ι_map g i.as)

/-- A coproduct of zero objects is zero, including an empty coproduct. -/
private theorem isZero_sigma
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    {I : Type v} (U : I → B) (h : ∀ i, IsZero (U i)) : IsZero (∐ U) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro i
  exact (h i).eq_of_src _ _

/-- A family of bounded-below derived morphisms gives a morphism from the coproduct
of its truncation couples to the target truncation couple, with natural comparisons
on both the initial E terms and D at first index zero. This asserts construction and
naturality only; no initial-page or abutment isomorphism hypothesis is imposed.

Source: Stacks Project, Tag 015J (the natural hypercohomology second page and abutment),
Tag 05TC (derived lower bounds and truncation comparison), and Tag 08DZ (the direct-sum reduction).
(blueprint: lem-pc-coproduct-truncation-couple).

Proof:
1. Use canonical lower truncation and K-injective representatives for K_i and S,
with the common cohomological lower bound a. For each representative apply the
truncation hypercohomology theorem. Its D terms are H^{p+r}(RF(tau_le_r K_i));
its E terms are H^{p+r}(RF(H^r(K_i)[-r])). Apply the same construction to S.
The canonical truncation triangle is functorial in a derived morphism. Applying
RF and homology to its naturality squares gives maps of these exact couples for
u_i, including commutation with the connecting maps. Equivalently represent u_i
by maps between K-injectives and use naturality of the truncation triangles there.
2. Form X by taking the coproduct of the summands' D and E objects at every
bidegree, and the maps induced by their structure maps. Grothendieck exactness of
small coproducts preserves the three exact sequences defining an exact couple,
so these maps give an exact couple. Let Y be the target couple. The maps to Y are
the coproduct descents of the individual couple maps. Precomposing each required
square with every coproduct inclusion reduces it to the individual square; this
gives T. When r<a, each truncated complex is zero, hence each summand D term and
the target D term vanish. Their coproduct vanishes too. Left exactness of F makes
RF of an object in degree zero connective, so both E terms vanish when p<0.
3. At p=0 the truncation inclusion induces an isomorphism on H^n after RF:
the cone is cohomologically at least n+1, and RF preserves that lower bound.
These maps give the individual D-to-abutment isomorphisms. Their coproduct gives
eX; the target gives eY. Naturality of truncation inclusion gives the displayed
D square; check it after precomposing with each coproduct inclusion.
4. For p>=0, the single-functor shift, RF shift commutation, and homology shift
isomorphisms identify each E^{p,r} with H^p(RF(H^r(K_i)[0])). These isomorphisms
are natural, as are their counterparts for S. Taking their coproduct gives s;
the target comparison gives t. Naturality and the coproduct universal property
prove the displayed E equation. No comparison is asserted to be invertible.
For an empty family X is the zero exact couple and the same universal-property
proofs apply. Choices made here witness an existential theorem and define no
library data. -/
theorem exists_coproduct_truncation_couple
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : Type v) (K : I → DerivedCategory A) (S : DerivedCategory A)
    (u : ∀ i, K i ⟶ S) (a : ℤ)
    (hK : ∀ (i : I) (r : ℤ), r < a →
      IsZero ((DerivedCategory.homologyFunctor A r).obj (K i)))
    (hS : ∀ r : ℤ, r < a → IsZero ((DerivedCategory.homologyFunctor A r).obj S)) :
    ∃ (X Y : BigradedExactCouple B 0) (T : BigradedExactCouple.CoupleMorphism X Y),
      (∀ p r : ℤ, r < a → IsZero (X.D p r)) ∧
      (∀ p r : ℤ, r < a → IsZero (Y.D p r)) ∧
      (∀ p r : ℤ, p < 0 → IsZero (X.E p r)) ∧
      (∀ p r : ℤ, p < 0 → IsZero (Y.E p r)) ∧
      ∃ (eX : ∀ n : ℤ, X.D 0 n ≅
          ∐ (fun i ↦ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj
            (K i)))
        (eY : ∀ n : ℤ, Y.D 0 n ≅
          (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj S),
        (∀ n : ℤ, Sigma.desc (fun i ↦
          (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map (u i)) =
            (eX n).inv ≫ T.tD 0 n ≫ (eY n).hom) ∧
        ∀ (p : ℕ) (r : ℤ),
          ∃ (s : X.E p r ≅ ∐ (fun i ↦
              (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
                DerivedCategory.homologyFunctor B (p : ℤ)).obj
                  ((DerivedCategory.homologyFunctor A r).obj (K i))))
            (t : Y.E p r ≅
              (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
                DerivedCategory.homologyFunctor B (p : ℤ)).obj
                  ((DerivedCategory.homologyFunctor A r).obj S)),
            T.tE p r = s.hom ≫ Sigma.desc (fun i ↦
              (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
                DerivedCategory.homologyFunctor B (p : ℤ)).map
                  ((DerivedCategory.homologyFunctor A r).map (u i))) ≫ t.inv := by
  classical
  obtain ⟨Z, eD, eE, hD, hE, hm⟩ :=
    exists_natural_boundedBelow_truncation_couples F a
  let L := fun i ↦ (⟨K i, hK i⟩ : {M : DerivedCategory A //
    ∀ r : ℤ, r < a → IsZero ((DerivedCategory.homologyFunctor A r).obj M)})
  let N := (⟨S, hS⟩ : {M : DerivedCategory A //
    ∀ r : ℤ, r < a → IsZero ((DerivedCategory.homologyFunctor A r).obj M)})
  let V := fun i ↦ Z (L i)
  let Y := Z N
  choose t htD htE using fun i ↦ hm (L i) N (u i)
  have ha := fun p r ↦ exact_sigma (fun i ↦ (V i).f p r)
    (fun i ↦ (V i).alpha (p + 2) (r - 1))
    (fun i ↦ (V i).alpha_f_zero p r)
    (fun i ↦ (ShortComplex.exact_iff_image_eq_kernel _).mpr ((V i).exact_alpha p r))
  have hf := fun p r ↦ exact_sigma (fun i ↦ (V i).g p r)
    (fun i ↦ (V i).f (p + (0 : ℕ)) (r - (0 : ℕ)))
    (fun i ↦ (V i).f_g_zero p r)
    (fun i ↦ (ShortComplex.exact_iff_image_eq_kernel _).mpr ((V i).exact_f p r))
  have hg := fun p r ↦ exact_sigma (fun i ↦ (V i).alpha p r)
    (fun i ↦ (V i).g (p - 1) (r + 1))
    (fun i ↦ (V i).g_alpha_zero p r)
    (fun i ↦ (ShortComplex.exact_iff_image_eq_kernel _).mpr ((V i).exact_g p r))
  let X : BigradedExactCouple B 0 :=
    { D := fun p r ↦ ∐ (fun i ↦ (V i).D p r)
      E := fun p r ↦ ∐ (fun i ↦ (V i).E p r)
      alpha := fun p r ↦ Limits.Sigma.map (fun i ↦ (V i).alpha p r)
      f := fun p r ↦ Limits.Sigma.map (fun i ↦ (V i).f p r)
      g := fun p r ↦ Limits.Sigma.map (fun i ↦ (V i).g p r)
      alpha_f_zero := fun p r ↦ (ha p r).choose
      f_g_zero := fun p r ↦ (hf p r).choose
      g_alpha_zero := fun p r ↦ (hg p r).choose
      exact_alpha := fun p r ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (ha p r).choose_spec
      exact_f := fun p r ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (hf p r).choose_spec
      exact_g := fun p r ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp
        (hg p r).choose_spec }
  let T : BigradedExactCouple.CoupleMorphism X Y :=
    { tD := fun p r ↦ Sigma.desc (fun i ↦ (t i).tD p r)
      tE := fun p r ↦ Sigma.desc (fun i ↦ (t i).tE p r)
      alpha_comm := by
        intro p r
        apply Sigma.hom_ext
        intro i
        simpa [X, Category.assoc] using (t i).alpha_comm p r
      f_comm := by
        intro p r
        apply Sigma.hom_ext
        intro i
        simpa [X, Category.assoc] using (t i).f_comm p r
      g_comm := by
        intro p r
        apply Sigma.hom_ext
        intro i
        simpa [X, Category.assoc] using (t i).g_comm p r }
  refine ⟨X, Y, T, ?_, hD N, ?_, hE N, ?_⟩
  · intro p r hr
    exact isZero_sigma _ (fun i ↦ hD (L i) p r hr)
  · intro p r hp
    exact isZero_sigma _ (fun i ↦ hE (L i) p r hp)
  · refine ⟨fun n ↦ Sigma.mapIso (fun i ↦ eD (L i) n), eD N, ?_, ?_⟩
    · intro n
      apply Sigma.hom_ext
      intro i
      dsimp only [T]
      simp only [Sigma.ι_comp_desc, Sigma.ι_mapIso_inv_assoc, Sigma.ι_comp_desc_assoc]
      change _ = (eD (L i) n).inv ≫ (t i).tD 0 n ≫ (eD N n).hom
      rw [htD i n, Iso.inv_hom_id_assoc]
    · intro p r
      refine ⟨Sigma.mapIso (fun i ↦ eE (L i) p r), eE N p r, ?_⟩
      apply Sigma.hom_ext
      intro i
      dsimp only [T]
      simp only [Sigma.ι_comp_desc, Sigma.ι_mapIso_hom_assoc, Sigma.ι_comp_desc_assoc]
      change (t i).tE p r = (eE (L i) p r).hom ≫ _ ≫ (eE N p r).inv
      rw [← Category.assoc, ← htE i p r, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]

end CategoryTheory
