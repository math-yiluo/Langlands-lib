/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Local bounded constant models on a small site

Source: Stacks Project, Cohomology on Sites, Tag 094G, proof of
`lemma-locally-constant` (auxiliary; not a blueprint node).

Constant-coefficient module sheaves are encoded as `Sheaf J (ModuleCat B)`:
restriction is precomposition on the slice, and the constant complex is obtained
by applying the constant-sheaf functor to both terms and differentials.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem exists_constant_model_of_concentrated
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u} [SmallCategory D] (J : GrothendieckTopology D)
    (B : Type u) [CommRing B]
    [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{u} B))]
    (F : A ⥤ Sheaf J (ModuleCat.{u} B)) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory A) (a : ℤ)
    (hvan : ∀ q : ℤ, q ≠ a → IsZero ((DerivedCategory.homologyFunctor A q).obj K))
    (M : ModuleCat.{u} B) [Module.Finite B M]
    (e : F.obj ((DerivedCategory.homologyFunctor A a).obj K) ≅
      (constantSheaf J (ModuleCat.{u} B)).obj M) :
    ∃ N : CochainComplex (ModuleCat.{u} B) ℤ,
      (∀ q : ℤ, Module.Finite B (N.X q)) ∧
      (∀ q : ℤ, q < a ∨ a < q → IsZero (N.X q)) ∧
      Nonempty (F.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj
        (((constantSheaf J (ModuleCat.{u} B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) := by
  classical
  obtain ⟨eK⟩ := DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj K a hvan
  refine ⟨(CochainComplex.singleFunctor (ModuleCat.{u} B) a).obj M, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = a
    · subst q
      exact Module.Finite.equiv
        (Iso.toLinearEquiv
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M)).symm
    · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a M q hq
      have : Subsingleton
          (((CochainComplex.singleFunctor (ModuleCat.{u} B) a).obj M).X q) :=
        ModuleCat.subsingleton_of_isZero hz
      infer_instance
  · intro q hq
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a M q (by omega)
  · exact ⟨F.mapDerivedCategory.mapIso eK ≪≫
      (F.mapDerivedCategorySingleFunctor a).app _ ≪≫
      (DerivedCategory.singleFunctor _ a).mapIso e ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ a).app _ ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (constantSheaf J (ModuleCat.{u} B)) (ComplexShape.up ℤ) a).app M).symm⟩

/-- A bounded object with locally constant finite cohomology has local constant
finite-module complex models, with the same degree bounds.

Source: Stacks Project, Tag 094G, strengthened assertion in the induction in the
proof of `lemma-locally-constant`.
(auxiliary; not a blueprint node)

Proof: Induct on `b - a`. Exact slice restriction preserves cohomology and cones
(lem-pur-site-restriction-module-adjunction-exact); constant sheaves restrict to
constant sheaves (lem-weil-pbc-site-constant-restriction), and successive coverings
compose. On empty slices use the zero complex. If `a = b`, canonical truncation
(theorem-pbc-injective-acyclicity) identifies the object with its single nonzero
cohomology sheaf; trivialize that sheaf. Otherwise trivialize the top cohomology
as a finite module M and choose finitely many generators. Exact sheafification
(lem-weil-pbc-site-module-presheaf-sheafification-exact) and local representatives
(lem-weil-pbc-site-sheafification-sections-local) lift the generators locally to
cycles, giving a map from a constant finite free module in degree b. Its cone
has cohomology in [a,b-1]; the long exact sequence
(lem-sf-derived-homology-long-exact) and the Serre property
(lem-weil-pbc-locally-constant-derived-serre) give locally constant finite
cohomology. Apply induction. Represent the boundary to the free module shifted
by b-1 using a right fraction (lem-pc-right-fraction-representation and
lem-pc-quasi-isomorphisms-multiplicative-system). Upper truncate the roof;
its top component factors through top cohomology and hence yields an actual
chain map out of the constant model. Its top component locally comes from a
module map (lem-weil-pbc-site-constant-morphism-local). On a nonempty slice,
local equality in the constant presheaf makes the constant functor faithful,
so this module map annihilates the preceding differential. Append the free
module in degree b. The resulting constant complex is the shifted cone of the
boundary; rotation and the morphism-of-triangles axiom
(def-weil-triangulated-category), followed by the long exact cohomology
sequence, identify it with the original object. Compose the finitely many
covering refinements. No points or Tor-amplitude assumption is used. -/
theorem exists_site_bounded_constant_model
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (X : C) (hX : IsTerminal X)
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck (ModuleCat.{u} B))]
    [∀ U : C, HasDerivedCategory.{w}
      (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]
    (K : DerivedCategory (Sheaf J.toGrothendieck (ModuleCat.{u} B)))
    (a b : ℤ) (hab : a ≤ b)
    (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor (Sheaf J.toGrothendieck (ModuleCat.{u} B)) q).obj K))
    (hloc : ∀ (q : ℤ) (V : C),
      ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ V),
        Presieve.ofArrows U f ∈ J V ∧
        ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
          ((J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i)).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf J.toGrothendieck (ModuleCat.{u} B)) q).obj K) ≅
            (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)).obj M)) :
    ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ M : CochainComplex (ModuleCat.{u} B) ℤ,
        (∀ q : ℤ, Module.Finite B (M.X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (M.X q)) ∧
        Nonempty
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
              (J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i))
              (Functor.additive_of_preserves_binary_products _) _
              ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
                (self := Adjunction.leftAdjoint_preservesColimits
                  (Functor.sheafAdjunctionCocontinuous
                    (Over.forget (U i)) (ModuleCat.{u} B)
                    (J.toGrothendieck.over (U i)) J.toGrothendieck))⟩).obj K ≅
            DerivedCategory.Q.obj
              ((Functor.mapHomologicalComplex
                (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B))
                (ComplexShape.up ℤ)).obj M)) := by
  classical
  let Model (V : C) : Prop :=
    ∃ M : CochainComplex (ModuleCat.{u} B) ℤ,
      (∀ q : ℤ, Module.Finite B (M.X q)) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero (M.X q)) ∧
      Nonempty
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            (J.toGrothendieck.overPullback (ModuleCat.{u} B) V)
            (Functor.additive_of_preserves_binary_products _) _
            ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
              (self := Adjunction.leftAdjoint_preservesColimits
                (Functor.sheafAdjunctionCocontinuous
                  (Over.forget V) (ModuleCat.{u} B)
                  (J.toGrothendieck.over V) J.toGrothendieck))⟩).obj K ≅
          DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (constantSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B))
              (ComplexShape.up ℤ)).obj M))
  change ∃ (I : Type u) (U : I → C) (f : ∀ i, U i ⟶ X),
    Presieve.ofArrows U f ∈ J X ∧ ∀ i, Model (U i)
  by_cases h : a = b
  · subst b
    obtain ⟨I, U, f, hcover, hM⟩ := hloc a X
    refine ⟨I, U, f, hcover, fun i ↦ ?_⟩
    obtain ⟨M, hfinite, ⟨e⟩⟩ := hM i
    have := hfinite
    let F := J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i)
    have : F.Additive := Functor.additive_of_preserves_binary_products _
    have : PreservesFiniteColimits F :=
      ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
        (self := Adjunction.leftAdjoint_preservesColimits
          (Functor.sheafAdjunctionCocontinuous
            (Over.forget (U i)) (ModuleCat.{u} B)
            (J.toGrothendieck.over (U i)) J.toGrothendieck))⟩
    exact exists_constant_model_of_concentrated
      (J.toGrothendieck.over (U i)) B F K a
      (fun q hq ↦ hvan q (by omega)) M e
  · obtain ⟨I, U, f, hcover, hmodels⟩ :=
      exists_site_bounded_constant_graded_model J X hX B K a b (by omega) hvan hloc
    have hlocal (i : I) : ∃ S ∈ J.toGrothendieck (U i),
        ∀ ⦃V : C⦄ (g : V ⟶ U i), S g → Model V := by
      obtain ⟨P, M, hfinite, hzero, he, ⟨eK⟩⟩ := hmodels i
      obtain ⟨S, hS, hdescent⟩ := exists_local_constant_complex_of_constant_terms
        J.toGrothendieck B (U i) P a b M hfinite hzero (fun q ↦ (he q).some)
      refine ⟨S, hS, fun V g hg ↦ ?_⟩
      obtain ⟨N, hNfinite, hNzero, ⟨eN⟩⟩ := hdescent g hg
      let F := J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i)
      let R := J.toGrothendieck.overMapPullback (ModuleCat.{u} B) g
      have : F.Additive := Functor.additive_of_preserves_binary_products _
      have : R.Additive := Functor.additive_of_preserves_binary_products _
      have : PreservesFiniteColimits F :=
        ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
          (self := Adjunction.leftAdjoint_preservesColimits
            (Functor.sheafAdjunctionCocontinuous
              (Over.forget (U i)) (ModuleCat.{u} B)
              (J.toGrothendieck.over (U i)) J.toGrothendieck))⟩
      have : PreservesFiniteColimits R :=
        ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
          (self := Adjunction.leftAdjoint_preservesColimits
            (Functor.sheafAdjunctionCocontinuous
              (Over.map g) (ModuleCat.{u} B)
              (J.toGrothendieck.over V) (J.toGrothendieck.over (U i))))⟩
      refine ⟨N, hNfinite, hNzero, ⟨?_⟩⟩
      exact (Functor.mapDerivedCategoryCompIso F R).symm.app K ≪≫
        R.mapDerivedCategory.mapIso eK ≪≫ R.mapDerivedCategoryFactors.app P ≪≫
        DerivedCategory.Q.mapIso eN
    choose S hS hh using hlocal
    choose T hT hle using fun i ↦
      J.mem_toGrothendieck_iff_of_isStableUnderComposition.mp (hS i)
    choose A V g hg using fun i ↦ (T i).exists_eq_ofArrows
    have hV (i : I) : Presieve.ofArrows (V i) (g i) ∈ J (U i) := by
      rw [← hg i]
      exact hT i
    refine ⟨Σ i, A i, fun p ↦ V p.1 p.2, fun p ↦ g p.1 p.2 ≫ f p.1,
      Precoverage.comp_mem_coverings f hcover g hV, fun p ↦ ?_⟩
    apply hh p.1 (g p.1 p.2)
    apply hle p.1
    rw [hg p.1]
    exact Presieve.ofArrows.mk p.2

end CategoryTheory
