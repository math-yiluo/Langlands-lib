/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local finite constant extension towers

Source: Stacks Project, Cohomology on Sites, Tag 094G, the cohomological
induction before the boundary maps are realized by chain maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v z w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

open CategoryTheory.Pretriangulated

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem tower_of_iso
    {B : Type u} [CommRing B]
    {A : Type z} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (S : ModuleCat.{u} B ⥤ A) (a : ℤ)
    {n : ℕ} {K K' : DerivedCategory A} (e : K' ≅ K)
    (h : FiniteConstantExtensionTower S a n K) :
    FiniteConstantExtensionTower S a n K' := by
  cases h with
  | single M hM K eK =>
    exact .single M hM K' ⟨e ≪≫ eK.some⟩
  | step M hM hL i δ j hT =>
    refine .step M hM hL (e.hom ≫ i) δ
      (j ≫ (shiftFunctor _ (1 : ℤ)).map e.inv) ?_
    apply isomorphic_distinguished _ hT
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp
    · simp
    · simp [← Functor.map_comp, Category.assoc]

private theorem tower_single
    {B : Type u} [CommRing B]
    {A : Type z} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (S : ModuleCat.{u} B ⥤ A) (a : ℤ) (K : DerivedCategory A)
    (hvan : ∀ q : ℤ, q < a ∨ a < q →
      IsZero ((DerivedCategory.homologyFunctor A q).obj K))
    (M : ModuleCat.{u} B) (hM : Module.Finite B M)
    (eM : (DerivedCategory.homologyFunctor A a).obj K ≅ S.obj M) :
    FiniteConstantExtensionTower S a 0 K := by
  have : K.IsGE a := (DerivedCategory.isGE_iff K a).2
    (fun q hq ↦ hvan q (Or.inl hq))
  have : K.IsLE a := (DerivedCategory.isLE_iff K a).2
    (fun q hq ↦ hvan q (Or.inr hq))
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K a
  let eY : Y ≅ S.obj M :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso A a).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor A a).mapIso e.symm ≪≫ eM
  exact .single M hM K ⟨e ≪≫ (DerivedCategory.singleFunctor A a).mapIso eY ≪≫
    (DerivedCategory.singleFunctorIsoCompQ A a).app (S.obj M)⟩

section Slices

variable {C : Type u} [SmallCategory C] (J : Precoverage C)
  (B : Type u) [CommRing B]

private theorem map_colimits {U V : C} (f : V ⟶ U) :
    PreservesFiniteColimits (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f) :=
  ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
    (self := Adjunction.leftAdjoint_preservesColimits
      (Functor.sheafAdjunctionCocontinuous (Over.map f) (ModuleCat.{u} B)
        (J.toGrothendieck.over V) (J.toGrothendieck.over U)))⟩

private theorem map_additive {U V : C} (f : V ⟶ U) :
    (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] map_colimits map_additive

variable [∀ U : C, HasDerivedCategory.{w}
  (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]

private noncomputable abbrev sliceMap {U V : C} (f : V ⟶ U) :=
  (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f).mapDerivedCategory

private abbrev locallyFinite (U : C)
    (K : DerivedCategory (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))) : Prop :=
  ∀ (q : ℤ) (V : C) (g : V ⟶ U),
    ∃ (I : Type u) (W : I → C) (f : ∀ i : I, W i ⟶ V),
      Presieve.ofArrows W f ∈ J V ∧
      ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
        ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i ≫ g)).obj
          ((DerivedCategory.homologyFunctor
            (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) q).obj K) ≅
          (constantSheaf (J.toGrothendieck.over (W i)) (ModuleCat.{u} B)).obj M)

private noncomputable def mapConstants {U V : C} (f : V ⟶ U) :
    constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B) ⋙
        J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f ≅
      constantSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const (Over U)ᵒᵖ)
      ((Over.map f).pushforwardContinuousSheafificationCompatibility
        (ModuleCat.{u} B) (J.toGrothendieck.over V) (J.toGrothendieck.over U)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ (Over.map f).op)
      (presheafToSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B))

private theorem restrict_step {U V : C} (f : V ⟶ U) (a : ℤ) (n : ℕ)
    (K L : DerivedCategory (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)))
    (M : ModuleCat.{u} B) (hM : Module.Finite B M)
    (i : K ⟶ L)
    (δ : L ⟶ DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ (a + n)).obj
        ((constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj M)))
    (j : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ (a + n)).obj
        ((constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj M)) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk i δ j ∈ distTriang _)
    (hL : FiniteConstantExtensionTower
      (constantSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B)) a n
      ((sliceMap J B f).obj L)) :
    FiniteConstantExtensionTower
      (constantSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B)) a (n + 1)
      ((sliceMap J B f).obj K) := by
  let F := J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f
  let D := sliceMap J B f
  let e : D.obj (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ (a + n)).obj
        ((constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj M))) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ (a + n)).obj
        ((constantSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B)).obj M)) :=
    D.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ (a + n)).app _).symm ≪≫
      (F.mapDerivedCategorySingleFunctor (a + n)).app _ ≪≫
      (DerivedCategory.singleFunctor _ (a + n)).mapIso ((mapConstants J B f).app M) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ (a + n)).app _
  refine .step M hM hL (D.map i) (D.map δ ≫ e.hom)
    (e.inv ≫ D.map j ≫ (D.commShiftIso (1 : ℤ)).hom.app K) ?_
  apply isomorphic_distinguished _ (D.map_distinguished _ hT)
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_
  · change D.map i ≫ 𝟙 _ = 𝟙 _ ≫ D.map i
    simp
  · change (D.map δ ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ D.map δ
    simp
  · change (e.inv ≫ D.map j ≫ (D.commShiftIso (1 : ℤ)).hom.app K) ≫
        (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
      e.inv ≫ (D.map j ≫ (D.commShiftIso (1 : ℤ)).hom.app K)
    rw [Functor.map_id]
    exact Category.comp_id _

private theorem local_tower_on_slice
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [IsNoetherianRing B] (a : ℤ) (n : ℕ) :
    ∀ (U : C) (K : DerivedCategory (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)))
      (_hvan : ∀ q : ℤ, q < a ∨ a + n < q → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) q).obj K))
      (_hloc : locallyFinite J B U K),
      ∃ (I : Type u) (V : I → C) (f : ∀ i : I, V i ⟶ U),
        Presieve.ofArrows V f ∈ J U ∧
        ∀ i : I, FiniteConstantExtensionTower
          (constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)) a n
          ((sliceMap J B (f i)).obj K) := by
  induction n with
  | zero =>
    intro U K hvan hloc
    obtain ⟨I, V, f, hcover, hM⟩ := hloc a U (𝟙 U)
    refine ⟨I, V, f, hcover, fun i ↦ ?_⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := hM i
    let F := J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i)
    apply tower_single _ a _ (fun q hq ↦
      F.isZero_homologyFunctor_mapDerivedCategory_obj (hvan q (by simpa using hq))) M hM
    exact (F.mapDerivedCategoryHomologyFunctorIso a).symm.app K ≪≫
      (by simpa only [Category.comp_id, Functor.comp_obj, F] using eM)
  | succ n ih =>
    intro U K hvan hloc
    obtain ⟨I, V, f, hcover, hstep⟩ :=
      exists_site_finite_constant_cone_step J B U K a (a + (n + 1 : ℕ)) (by omega)
        hvan hloc
    have hwidth : a + (n + 1 : ℕ) - 1 = a + n := by omega
    rw [hwidth] at hstep
    choose M hM L hvanL hlocL iK δ j hT using hstep
    have hnext (i : I) := ih (V i) (L i) (hvanL i) (hlocL i)
    choose T W g hcoverW hLW using hnext
    refine ⟨Σ i, T i, fun p ↦ W p.1 p.2, fun p ↦ g p.1 p.2 ≫ f p.1,
      Precoverage.comp_mem_coverings f hcover g hcoverW, ?_⟩
    intro ⟨i, t⟩
    have ht := restrict_step J B (g i t) a n _ (L i) (M i) (hM i) (iK i)
      (δ i) (j i) (hT i) (hLW i t)
    let e := (Functor.mapDerivedCategoryNatIso
      (J.toGrothendieck.overMapPullbackComp (ModuleCat.{u} B) (g i t) (f i)).symm ≪≫
        (Functor.mapDerivedCategoryCompIso
          (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i))
          (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (g i t))).symm).app K
    exact tower_of_iso _ _ e ht

omit [∀ U : C, HasDerivedCategory.{w}
  (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))] in
private theorem pullback_colimits (U : C) :
    PreservesFiniteColimits (J.toGrothendieck.overPullback (ModuleCat.{u} B) U) :=
  ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
    (self := Adjunction.leftAdjoint_preservesColimits
      (Functor.sheafAdjunctionCocontinuous (Over.forget U) (ModuleCat.{u} B)
        (J.toGrothendieck.over U) J.toGrothendieck))⟩

omit [∀ U : C, HasDerivedCategory.{w}
  (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))] in
private theorem pullback_additive (U : C) :
    (J.toGrothendieck.overPullback (ModuleCat.{u} B) U).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] pullback_colimits pullback_additive

private noncomputable def restrictionMapIso
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck (ModuleCat.{u} B))]
    {U V : C} (f : V ⟶ U) :
    (J.toGrothendieck.overPullback (ModuleCat.{u} B) U).mapDerivedCategory ⋙ sliceMap J B f ≅
      (J.toGrothendieck.overPullback (ModuleCat.{u} B) V).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents (fun F ↦ F.pushforwardOverMapIso f) (by intros; ext; rfl))

end Slices

attribute [local instance] map_colimits map_additive pullback_colimits pullback_additive

/-- Locally, finite locally constant cohomology admits a finite tower of
triangles with constant finite attachments. This is only the cohomological
induction: it produces no complex and no chain representatives for boundaries.

Source: Stacks Project, Cohomology on Sites, Tag 094G, proof of
`lemma-locally-constant`, through the induction applied to the cone L.
(auxiliary; not a blueprint node)

Proof: Induct on the nonnegative width b-a, simultaneously on slices. In width
zero, the canonical t-structure identifies K with H^a(K) in degree a; locally
trivialize that finite locally constant sheaf. This is the single constructor.
For positive width, trivialize H^b(K) as the constant finite module M. Choose
finitely many generators, hence an epimorphism from the constant finite free
module F to H^b(K). Represent K by its good upper truncation at b. The quotient
from its cycles to H^b is epi. The finite-free local lifting theorem lifts the
chosen epimorphism through this quotient on a covering. Compose with the cycles
inclusion to obtain a chain map F[-b] to the representative and localize it.
Complete to the triangle F[-b] to K to L to F[-b+1]. Its long exact homology
sequence gives vanishing of L outside [a,b-1], unchanged homology below b-1,
and an extension of H^(b-1)(K) by the kernel of F to H^b(K) in degree b-1.
Noetherianity and the finite locally constant Serre property show that this
homology is finite locally constant. For the recorded ringed-module versions,
transport through site_moduleSheaf_restriction_equivalence; its constant and
slice comparisons identify the same local trivializations. Exact restriction and its comparison
with constants transport these assertions to every further slice. Apply the
induction hypothesis to L. Rotate the displayed triangle and identify
F[-b+1] with the single object in degree b-1; the step constructor appends this
triangle to the shorter tower. Flatten iterated slices via their canonical
slice equivalence, and compose all covering refinements. The zero ring, zero
top homology, and empty covers require no nonzero generator: choose rank zero
and the zero single object. This argument stops at triangles, before the
separate chain-representative and mapping-cocone realization argument. -/
theorem exists_site_finite_constant_extension_tower
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
      ∀ i : I, FiniteConstantExtensionTower
        (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)) a
        (b - a).toNat
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            (J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i))
            (Functor.additive_of_preserves_binary_products _) _
            ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
              (self := Adjunction.leftAdjoint_preservesColimits
                (Functor.sheafAdjunctionCocontinuous
                  (Over.forget (U i)) (ModuleCat.{u} B)
                  (J.toGrothendieck.over (U i)) J.toGrothendieck))⟩).obj K) := by
  classical
  have _hX := hX
  let F := J.toGrothendieck.overPullback (ModuleCat.{u} B) X
  let K' := F.mapDerivedCategory.obj K
  have hwidth : a + (b - a).toNat = b := by omega
  have hvan' (q : ℤ) (hq : q < a ∨ a + (b - a).toNat < q) : IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf (J.toGrothendieck.over X) (ModuleCat.{u} B)) q).obj K') := by
    exact F.isZero_homologyFunctor_mapDerivedCategory_obj
      (hvan q (by simpa only [hwidth] using hq))
  have hloc' : locallyFinite J B X K' := by
    intro q V g
    obtain ⟨I, W, f, hcover, hM⟩ := hloc q V
    refine ⟨I, W, f, hcover, fun i ↦ ?_⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := hM i
    refine ⟨M, hM, ⟨?_⟩⟩
    exact (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i ≫ g)).mapIso
        ((F.mapDerivedCategoryHomologyFunctorIso q).symm.app K) ≪≫
      ((DerivedCategory.homologyFunctor _ q).obj K).pushforwardOverMapIso (f i ≫ g) ≪≫ eM
  obtain ⟨I, U, f, hcover, htower⟩ :=
    local_tower_on_slice J B a (b - a).toNat X K' hvan' hloc'
  refine ⟨I, U, f, hcover, fun i ↦ ?_⟩
  exact tower_of_iso _ _ ((restrictionMapIso J B (f i)).app K).symm (htower i)

end CategoryTheory
