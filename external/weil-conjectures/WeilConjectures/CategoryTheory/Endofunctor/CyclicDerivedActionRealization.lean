/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Realization of a single invertible derived action

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
the agent-formulated native-derived foundation and its sequential-colimit proof
(blueprint: lem-sf-cyclic-derived-action-realization).

The action is the canonical composition comparison followed by localization of the
structure isomorphisms of fixed pairs. No functorial realization is chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private abbrev iterObj {A : Type*} [Category A] (R : A ⥤ A) (X : A) : ℕ → A
  | 0 => X
  | n + 1 => R.obj (iterObj R X n)

private abbrev iterMap {A : Type*} [Category A] (R : A ⥤ A) {X : A}
    (g : X ⟶ R.obj X) : ∀ n, iterObj R X n ⟶ iterObj R X (n + 1)
  | 0 => g
  | n + 1 => R.map (iterMap R g n)

private abbrev iterDiagram {A : Type*} [Category A] (R : A ⥤ A) {X : A}
    (g : X ⟶ R.obj X) : ℕ ⥤ A :=
  Functor.ofSequence (iterMap R g)

private theorem iter_colimit_iso {A : Type*} [Category A] (R : A ⥤ A) {X : A}
    (g : X ⟶ R.obj X) [HasColimitsOfShape ℕ A] [PreservesColimitsOfShape ℕ R] :
    ∃ σ : colimit (iterDiagram R g) ≅ R.obj (colimit (iterDiagram R g)),
      ∀ n, colimit.ι (iterDiagram R g) n ≫ σ.hom =
        iterMap R g n ≫ R.map (colimit.ι (iterDiagram R g) n) := by
  let D := iterDiagram R g
  have hj (n : ℕ) : iterMap R g n ≫ colimit.ι D (n + 1) = colimit.ι D n := by
    simpa [D, iterDiagram] using colimit.w D (homOfLE (n.le_add_right 1))
  let c : Cocone D :=
    { pt := R.obj (colimit D)
      ι := NatTrans.ofSequence
        (fun n ↦ iterMap R g n ≫ R.map (colimit.ι D n)) (fun n ↦ by
          dsimp
          simp only [D, iterDiagram, Functor.ofSequence_map_homOfLE_succ]
          change iterMap R g n ≫ R.map (iterMap R g n) ≫
            R.map (colimit.ι D (n + 1)) = _
          rw [← R.map_comp, hj]
          exact (Category.comp_id _).symm) }
  let c' : Cocone (D ⋙ R) :=
    { pt := colimit D
      ι := NatTrans.ofSequence (fun n ↦ colimit.ι D (n + 1)) (fun n ↦ by
        dsimp
        simp only [D, iterDiagram, Functor.ofSequence_map_homOfLE_succ]
        simpa only [iterMap, Category.comp_id] using hj (n + 1)) }
  let t := colimit.desc D c
  let hc := isColimitOfPreserves R (colimit.isColimit D)
  let s := hc.desc c'
  have ht (n : ℕ) : colimit.ι D n ≫ t =
      iterMap R g n ≫ R.map (colimit.ι D n) := colimit.ι_desc c n
  have hs (n : ℕ) : R.map (colimit.ι D n) ≫ s = colimit.ι D (n + 1) :=
    hc.fac c' n
  refine ⟨⟨t, s, ?_, ?_⟩, ht⟩
  · apply colimit.hom_ext
    intro n
    rw [← Category.assoc, ht, Category.assoc, hs, hj, Category.comp_id]
  · apply hc.hom_ext
    intro n
    change R.map (colimit.ι D n) ≫ (s ≫ t) = R.map (colimit.ι D n) ≫ 𝟙 _
    rw [← Category.assoc, hs, ht]
    change R.map (iterMap R g n) ≫ R.map (colimit.ι D (n + 1)) = _
    rw [← R.map_comp, hj, Category.comp_id]

private theorem sequence_map_isIso {A : Type*} [Category A] (D : ℕ ⥤ A)
    (h : ∀ n : ℕ, IsIso (D.map (homOfLE (n.le_add_right 1))))
    {i j : ℕ} (f : i ⟶ j) : IsIso (D.map f) := by
  have hj := leOfHom f
  obtain rfl := Subsingleton.elim f (homOfLE hj)
  induction j, hj using Nat.le_induction with
  | base => simpa using (inferInstance : IsIso (𝟙 (D.obj i)))
  | succ j hij ih =>
    have := h j
    have := ih
    have he : homOfLE (Nat.le_succ_of_le hij) =
        homOfLE hij ≫ homOfLE (j.le_add_right 1) := Subsingleton.elim _ _
    rw [he, D.map_comp]
    infer_instance

private theorem iter_colimit_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (hR : ∀ {K L} (f : K ⟶ L), QuasiIso f → QuasiIso (R.map f))
    {X : CochainComplex C ℤ} (g : X ⟶ R.obj X) [QuasiIso g] :
    QuasiIso (colimit.ι (iterDiagram R g) 0) := by
  have : HasFilteredColimitsOfSize.{0, 0} C := hasFilteredColimitsOfSize_shrink
  have : AB5OfSize.{0, 0} C := AB5OfSize_of_univLE.{0, 0, v, v} C
  have h (n : ℕ) : QuasiIso (iterMap R g n) := by
    induction n with
    | zero => exact inferInstanceAs (QuasiIso g)
    | succ n ih => exact hR _ ih
  constructor
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q
  let D := iterDiagram R g
  have : ∀ (i j : ℕ) (f : i ⟶ j), IsIso ((D ⋙ H).map f) := by
    intro i j f
    apply sequence_map_isIso (D ⋙ H) _ f
    intro n
    change IsIso (HomologicalComplex.homologyMap (D.map _) q)
    simp only [D, iterDiagram, Functor.ofSequence_map_homOfLE_succ]
    have := h n
    infer_instance
  have : IsIso (colimit.ι (D ⋙ H) 0) :=
    isIso_ι_of_isInitial (isInitialBot) (D ⋙ H)
  change IsIso (H.map (colimit.ι D 0))
  rw [← ι_preservesColimitIso_inv H D 0]
  infer_instance

private theorem strictify_chain_action
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (E : CochainComplex C ℤ ≌ CochainComplex C ℤ)
    (hR : ∀ {K L} (f : K ⟶ L), QuasiIso f → QuasiIso (E.inverse.map f))
    (X : CochainComplex C ℤ) (f : E.functor.obj X ⟶ X) [QuasiIso f] :
    ∃ (Y : CochainComplex C ℤ) (τ : E.functor.obj Y ≅ Y) (j : X ⟶ Y),
      QuasiIso j ∧ E.functor.map j ≫ τ.hom = f ≫ j := by
  let g : X ⟶ E.inverse.obj X := E.unitIso.hom.app X ≫ E.inverse.map f
  have : QuasiIso (E.inverse.map f) := hR f inferInstance
  have : QuasiIso g := inferInstance
  let D := iterDiagram E.inverse g
  obtain ⟨σ, hσ⟩ := iter_colimit_iso E.inverse g
  let τ : E.functor.obj (colimit D) ≅ colimit D :=
    E.functor.mapIso σ ≪≫ E.counitIso.app (colimit D)
  refine ⟨colimit D, τ, colimit.ι D 0, iter_colimit_quasiIso E.inverse hR g, ?_⟩
  let j : X ⟶ colimit D := colimit.ι D 0
  change E.functor.map j ≫ τ.hom = f ≫ j
  change E.functor.map j ≫ E.functor.map σ.hom ≫
    E.counitIso.hom.app (colimit D) = _
  rw [← E.functor.map_comp_assoc]
  have hj : j ≫ σ.hom = g ≫ E.inverse.map j := hσ 0
  rw [hj]
  calc
    _ = E.functor.map (E.unitIso.hom.app X) ≫
        E.functor.map (E.inverse.map (f ≫ j)) ≫ E.counitIso.hom.app (colimit D) := by
      simp only [g, Functor.map_comp, Category.assoc]
    _ = E.functor.map (E.unitIso.hom.app X) ≫
        E.counitIso.hom.app (E.functor.obj X) ≫ f ≫ j := by
      erw [E.counitIso.hom.naturality]
      rfl
    _ = f ≫ j := by
      erw [← Category.assoc, E.functor_unitIso_comp, Category.id_comp]

private abbrev complexOfAction
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    (Y : CochainComplex C ℤ) (τ : (F.mapHomologicalComplex (.up ℤ)).obj Y ≅ Y) :
    CochainComplex (IsoAlgebra F) ℤ where
  X i := IsoAlgebra.mk (Y.X i) (HomologicalComplex.eval C (.up ℤ) i |>.mapIso τ)
  d i j := ObjectProperty.homMk
    { f := Y.d i j
      h := (τ.hom.comm i j).symm }
  shape i j hij := by
    apply (forget F).map_injective
    exact Y.shape i j hij
  d_comp_d' i j k hij hjk := by
    apply (forget F).map_injective
    exact Y.d_comp_d i j k

private theorem lift_action
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [HasDerivedCategory.{w} C]
    (N : DerivedCategory C) (vN : F.mapDerivedCategory.obj N ≅ N) :
    ∃ (I : CochainComplex C ℤ) (a : DerivedCategory.Q.obj I ≅ N)
      (f : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ I),
      QuasiIso f ∧
      DerivedCategory.Q.map f ≫ a.hom = F.mapDerivedCategoryFactors.inv.app I ≫
        F.mapDerivedCategory.map a.hom ≫ vN.hom := by
  let K := DerivedCategory.Q.objPreimage N
  let b : DerivedCategory.Q.obj K ≅ N := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hI
  have := hs
  let a : DerivedCategory.Q.obj I ≅ N := (asIso (DerivedCategory.Q.map s)).symm ≪≫ b
  let P := (F.mapHomologicalComplex (.up ℤ)).obj I
  let m : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I :=
    F.mapDerivedCategoryFactors.inv.app I ≫ F.mapDerivedCategory.map a.hom ≫
      vN.hom ≫ a.inv
  obtain ⟨fh, hfh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) I).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ m ≫
        (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective fh
  have hf : DerivedCategory.Q.map f = m := by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality f
    rw [hfh] at h
    simpa using h.symm
  have : IsIso (DerivedCategory.Q.map f) := by rw [hf]; dsimp [m]; infer_instance
  refine ⟨I, a, f, (DerivedCategory.isIso_Q_map_iff_quasiIso C f).1 this, ?_⟩
  rw [hf]
  simp [m]

private theorem action_comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
    (Y : CochainComplex C ℤ) (τ : (F.mapHomologicalComplex (.up ℤ)).obj Y ≅ Y) :
    let B := complexOfAction F Y τ
    (Functor.mapDerivedCategoryCompIso (forget F) F ≪≫
      Functor.mapDerivedCategoryNatIso (strNatIso F)).hom.app (DerivedCategory.Q.obj B) ≫
        (forget F).mapDerivedCategoryFactors.hom.app B =
      F.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactors.hom.app B) ≫
        F.mapDerivedCategoryFactors.hom.app Y ≫ DerivedCategory.Q.map τ.hom := by
  dsimp only
  let B := complexOfAction F Y τ
  have h := Functor.mapDerivedCategoryNatIso_fac (strNatIso F) B
  have hc := Functor.mapDerivedCategoryCompIso_fac (forget F) F B
  have he : (NatTrans.mapHomologicalComplex (strNatIso F).hom (.up ℤ)).app B =
      τ.hom := by rfl
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (forget F ⋙ F))
      (.up ℤ)).hom.app B = 𝟙 _ := by rfl
  erw [hid, Functor.map_id, Category.comp_id] at hc
  change ((Functor.mapDerivedCategoryCompIso (forget F) F).inv.app
      (DerivedCategory.Q.obj B)) ≫
    F.mapDerivedCategory.map ((forget F).mapDerivedCategoryFactors.hom.app B) ≫
      F.mapDerivedCategoryFactors.hom.app Y = _ at hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [h, he, ← hc]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]

/-- Realize a bounded derived object with its prescribed invertible twisted action in
the ordinary derived category of fixed pairs, preserving its cohomology intervals
and every isomorphism-invariant class of underlying cohomology objects.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction
sentence; the agent construction in the DAG supplies the missing realization.
(blueprint: lem-sf-cyclic-derived-action-realization).

Proof plan, following the seven steps of the node:
1. The source IsoAlgebra library supplies exact, faithful forgetting. Represent N by
   a K-injective I with a : QI ≅ N (prose-03-02). By
   lem-weil-pbc-kinjective-hom-derived, the morphism a⁻¹ v D(P)(a) is represented
   by a chain map f : PI → I. Exact termwise derivation identifies its image
   (situation-conventions); f is a quasi-isomorphism.
   Only the target is required to be K-injective; no strict inverse is chosen.
2. Choose a quasi-inverse R of P, with unit η and counit ε satisfying the triangle
   identities. Put g = R(f)η_I, X_n = RⁿI, and g_n = Rⁿ(g). Equivalences preserve
   limits and colimits (lem-galois-equivalence-preserves-limits), so R is exact
   and all g_n are quasi-isomorphisms. Form the degreewise sequential colimit C
   with legs j_n (def-sp-grothendieck-abelian, def-weil-pbc-category-colimit).
   Its differential and its square are determined on these legs.
3. AB5 and src-weil-homology-preserves-exact-colimits identify H^q(C) with the
   colimit of H^q(X_n). The transition maps are isomorphisms. The inverses of
   their initial composites form a cocone inverse to H^q(j_0): check both
   composites on each colimit leg. Thus j_0 : I → C is a quasi-isomorphism.
4. The maps Rⁿ(g) followed by R(j_n) define a cocone to RC, inducing σ : C → RC.
   As R preserves colimits, the legs j_(n+1) induce s : RC → C. Checking on
   j_n and R(j_n) shows that these maps are inverse by colimit uniqueness.
5. Apply P to σ and compose with the counit to obtain τ : PC ≅ C. Counit
   naturality and the triangle identity give P(j_0) ≫ τ = f ≫ j_0. Its
   components and the differentials of C form a complex of fixed pairs.
6. Let M be this complex's derived image and e = a Q(j_0)⁻¹. Exact derivation
   identifies D(U)M with QC and its canonical structure with Q(τ). The equation
   τ P(j_0) = j_0 f implies e θ_M = v D(P)(e), by cancellation of the
   invertible D(P)(Q(j_0)); use situation-conventions.
7. Exact forgetting gives UH^q(M) ≅ H^q(D(U)M) ≅ H^q(N). Conservativity
   reflects zero objects, so every cohomology interval of N is one for M.
   Isomorphism invariance transports membership in any S along these same
   isomorphisms. No closure of S under colimits is required and no functorial
   choice or equivalence of derived categories with fixed pairs is asserted.
-/
theorem exists_cyclicDerivedActionRealization
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
    (N : DerivedCategory C) (hN : DerivedCategory.TStructure.t.bounded N)
    (vN : F.mapDerivedCategory.obj N ≅ N) :
    ∃ (M : DerivedCategory (IsoAlgebra F))
      (e : (forget F).mapDerivedCategory.obj M ≅ N),
      (Functor.mapDerivedCategoryCompIso (forget F) F ≪≫
        Functor.mapDerivedCategoryNatIso (F := forget F ⋙ F) (G := forget F)
          (NatIso.ofComponents (fun (K : IsoAlgebra F) ↦ K.str)
            (fun f ↦ f.hom.h))).hom.app M ≫ e.hom =
        F.mapDerivedCategory.map e.hom ≫ vN.hom ∧
      (∀ a b : ℤ,
        (∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj N)) →
        ∀ i : ℤ, i < a ∨ b < i →
          IsZero ((DerivedCategory.homologyFunctor (IsoAlgebra F) i).obj M)) ∧
      (∀ S : ObjectProperty C, S.IsClosedUnderIsomorphisms →
        (∀ i : ℤ, S ((DerivedCategory.homologyFunctor C i).obj N)) →
        ∀ i : ℤ,
          S ((forget F).obj ((DerivedCategory.homologyFunctor (IsoAlgebra F) i).obj M))) := by
  have _bounded := hN
  obtain ⟨I, a, f, hf, hfa⟩ := lift_action F N vN
  have := hf
  let E := F.asEquivalence.mapHomologicalComplex (ComplexShape.up ℤ)
  have hR : ∀ {K L} (g : K ⟶ L), QuasiIso g → QuasiIso (E.inverse.map g) := by
    intro K L g hg
    have := hg
    exact inferInstanceAs (QuasiIso ((F.inv.mapHomologicalComplex (.up ℤ)).map g))
  obtain ⟨Y, τ, j, hj, hτ⟩ := strictify_chain_action E hR I f
  have := hj
  let B := complexOfAction F Y τ
  let α : (forget F).mapDerivedCategory.obj (DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj Y := (forget F).mapDerivedCategoryFactors.app B
  let β : DerivedCategory.Q.obj Y ≅ N := (asIso (DerivedCategory.Q.map j)).symm ≪≫ a
  let e := α ≪≫ β
  refine ⟨DerivedCategory.Q.obj B, e, ?_, ?_, ?_⟩
  · change _ ≫ (α.hom ≫ β.hom) = _
    rw [← Category.assoc]
    change ((Functor.mapDerivedCategoryCompIso (forget F) F ≪≫
      Functor.mapDerivedCategoryNatIso (strNatIso F)).hom.app _ ≫ α.hom) ≫ β.hom = _
    have hcomp := action_comparison F Y τ
    change _ ≫ α.hom = F.mapDerivedCategory.map α.hom ≫
      F.mapDerivedCategoryFactors.hom.app Y ≫ DerivedCategory.Q.map τ.hom at hcomp
    rw [hcomp]
    have hb : DerivedCategory.Q.map j ≫ β.hom = a.hom := by simp [β]
    have hq : DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
        DerivedCategory.Q.map τ.hom = DerivedCategory.Q.map f ≫
          DerivedCategory.Q.map j := by
      change (F.mapHomologicalComplex (.up ℤ)).map j ≫ τ.hom = f ≫ j at hτ
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg (fun k ↦ DerivedCategory.Q.map k) hτ).trans
          (DerivedCategory.Q.map_comp _ _))
    have hh : F.mapDerivedCategoryFactors.hom.app Y ≫ DerivedCategory.Q.map τ.hom ≫
        β.hom = F.mapDerivedCategory.map β.hom ≫ vN.hom := by
      apply (cancel_epi (F.mapDerivedCategory.map (DerivedCategory.Q.map j))).1
      calc
        _ = F.mapDerivedCategoryFactors.hom.app I ≫
            DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
              DerivedCategory.Q.map τ.hom ≫ β.hom := by
          rw [← F.mapDerivedCategoryFactors_hom_naturality_assoc]
        _ = F.mapDerivedCategoryFactors.hom.app I ≫
            DerivedCategory.Q.map f ≫ a.hom := by
          rw [reassoc_of% hq, hb]
        _ = F.mapDerivedCategory.map a.hom ≫ vN.hom := by
          rw [hfa, Iso.hom_inv_id_app_assoc]
        _ = _ := by rw [← F.mapDerivedCategory.map_comp_assoc, hb]
    simp only [Category.assoc, e, Iso.trans_hom, Functor.map_comp]
    rw [hh]
  · intro l r h i hi
    apply (forget F).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (h i hi).of_iso ((DerivedCategory.homologyFunctor C i).mapIso e)
  · intro S hS h i
    let hS' : S.IsClosedUnderIsomorphisms := hS
    exact S.prop_of_iso
      ((((forget F).mapDerivedCategoryHomologyFunctorIso i).app _ ≪≫
        (DerivedCategory.homologyFunctor C i).mapIso e).symm) (h i)

end CategoryTheory.Endofunctor.IsoAlgebra
