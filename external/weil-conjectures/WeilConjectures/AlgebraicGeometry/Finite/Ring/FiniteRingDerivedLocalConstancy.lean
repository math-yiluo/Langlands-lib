/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSiteBoundedConstantModels
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Sites.Point.Over
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.FiniteRingDerivedHomFinite
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstantDerivedMappingSheaves
import WeilConjectures.AlgebraicGeometry.Derived.DerivedMappingPresheavesRestriction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Finite-ring derived local constancy

Source: Stacks Project, Tag 094G, lemma-locally-constant; the bounded finite-source
extension of Tag 09BE and connected constancy described in the DAG
(blueprint: lem-weil-pbc-finite-ring-derived-local-constancy).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

private instance : etalePrecoverage.{u}.IsStableUnderComposition :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderComposition

private instance : etalePrecoverage.{u}.IsStableUnderBaseChange :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderBaseChange

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))

private noncomputable def constantValuePullbackIso
    {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (U : X.Etale) (M : ModuleCat.{u + 1} B)
    (e : F.over U ≅
      (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} B)).obj M) :
    (upperStar (ModuleCat.{u + 1} B) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} B)).obj M :=
  (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} B) U F).symm ≪≫
    (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor.mapIso e ≪≫
    ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
      (X.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (ModuleCat.{u + 1} B) CategoryTheory.Over.mkIdTerminal).app M

private theorem local_finite_module_models
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hF : IsFiniteLocallyConstantSheaf F) (V : X.Etale) :
    ∃ (I : Type (u + 1)) (U : I → X.Etale) (f : ∀ i, U i ⟶ V),
      Sieve.ofArrows U f ∈ X.smallEtaleTopology V ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} B, Module.Finite B M ∧ Nonempty
          (F.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i))
              (ModuleCat.{u + 1} B)).obj M) := by
  classical
  have := hF
  let G := (upperStar (ModuleCat.{u + 1} B) V.hom).obj F
  have hG : IsFiniteLocallyConstantSheaf G :=
    IsFiniteLocallyConstantSheaf.upperStar V.hom F
  obtain ⟨d, hd⟩ := (finite_locally_constant_module_values_iff G).1.mpr hG
  let U (i : d.cover.I₀) : X.Etale := Scheme.Etale.mk (d.cover.f i ≫ V.hom)
  let f (i : d.cover.I₀) : U i ⟶ V := MorphismProperty.Over.homMk (d.cover.f i) rfl
  refine ⟨ULift.{u + 1} d.cover.I₀, fun i ↦ U i.down, fun i ↦ f i.down, ?_, ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := d.cover.exists_eq x
    exact ⟨⟨i⟩, y, hy⟩
  · intro i
    obtain ⟨M, hM, ⟨e⟩⟩ := hd i.down
    have : Finite M := hM
    refine ⟨M, Module.Finite.of_finite, ⟨?_⟩⟩
    let S := Scheme.Etale.overSheafEquiv (U i.down) (ModuleCat.{u + 1} B)
    apply S.fullyFaithfulFunctor.preimageIso
    exact overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} B) (U i.down) F ≪≫
      (upperStarComp (ModuleCat.{u + 1} B) (d.cover.f i.down) V.hom).app F ≪≫
      constantValuePullbackIso B G (d.cover.etalePrecoverageToEtale i.down) M e ≪≫
      (((Scheme.Etale.overEquiv (U i.down)).constantSheafSheafCongrIso
        (X.smallEtaleTopology.over (U i.down)) (U i.down).left.smallEtaleTopology
        (ModuleCat.{u + 1} B) CategoryTheory.Over.mkIdTerminal).app M).symm

set_option backward.isDefEq.respectTransparency false in
private theorem local_bounded_finite_models
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj K))
    (hlisse : ∀ n : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj K)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ E : CochainComplex (ModuleCat.{u + 1} B) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        (∀ n : ℤ, Finite (E.X n)) ∧ Nonempty
          ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) := by
  classical
  obtain ⟨a, b, hvan⟩ := hbounded
  have hvan' : ∀ q : ℤ, q < min a b ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K) := by
    intro q hq
    exact hvan q (hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _)) id)
  have hloc : ∀ (q : ℤ) (V : X.Etale),
      ∃ (I : Type (u + 1)) (U : I → X.Etale) (f : ∀ i, U i ⟶ V),
        Sieve.ofArrows U f ∈ X.smallEtaleTopology V ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} B, Module.Finite B M ∧ Nonempty
          (((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K).over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i))
              (ModuleCat.{u + 1} B)).obj M) := by
    intro q V
    obtain ⟨I, U, f, hf, hM⟩ := local_finite_module_models X B _ (hlisse q) V
    exact ⟨I, U, f, hf, hM⟩
  obtain ⟨𝒰, h𝒰⟩ := etale_site_bounded_constant_models X B K (min a b) b
    (min_le_right _ _) hvan' hloc
  exact ⟨𝒰, fun i ↦ by
    obtain ⟨E, hfinite, hsupport, e⟩ := h𝒰 i
    exact ⟨E, ⟨min a b, b, hsupport⟩, hfinite, e⟩⟩

private theorem finite_locally_constant_of_finite_values
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (S : 𝒰.I₀ → Type (u + 1)) (hS : ∀ i, Finite (S i))
    (e : ∀ i, F.over (𝒰.etalePrecoverageToEtale i) ≅
      (constantSheaf (X.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
        (Type (u + 1))).obj (S i)) : IsFiniteLocallyConstantSheafOfTypes F := by
  classical
  refine ⟨⟨𝒰, fun i ↦ Sheaf.isConstant_of_iso _ (e i)⟩, ⟨?_⟩⟩
  intro Ω _ _ s
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (s default)
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s y hy
  let U := 𝒰.etalePrecoverageToEtale i
  let Φ := pointSmallEtale s
  let lift : Φ.fiber.obj U := Over.homMk t ht
  let Ψ := Φ.over lift
  let neighbourhoods := FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber lift
  let forgetLift := neighbourhoods.functor ⋙ Over.forget (Φ.fiber.elementsMk U lift)
  have : forgetLift.Initial := inferInstance
  have eStalk : Ψ.sheafFiber.obj (F.over U) ≅ Φ.sheafFiber.obj F := by
    change colimit ((Functor.Elements.π Ψ.fiber).op ⋙ (F.over U).obj) ≅
      colimit ((Functor.Elements.π Φ.fiber).op ⋙ F.obj)
    have h : (Functor.Elements.π Ψ.fiber).op ⋙ (F.over U).obj =
        forgetLift.op ⋙ (Functor.Elements.π Φ.fiber).op ⋙ F.obj := rfl
    rw [h]
    exact Functor.Final.colimitIso forgetLift.op _
  let eValue : Φ.sheafFiber.obj F ≅ S i :=
    eStalk.symm ≪≫ Ψ.sheafFiber.mapIso (e i) ≪≫ Ψ.sheafFiberConstantSheafIso (S i)
  have := hS i
  have : Finite (Φ.sheafFiber.obj F) :=
    Finite.of_equiv _ eValue.toEquiv.symm
  exact (ConcreteCategory.isFinitelyGenerated_iff_finite _).mpr inferInstance

private noncomputable def constantDerivedFiberIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (E : DerivedCategory (ModuleCat.{u + 1} B)) :
    ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      (((pointSmallEtale x).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B))
      (Functor.additive_of_preserves_binary_products _) _ _).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E)) ≅
      E := by
  let F := ((pointSmallEtale x).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  have : F ⋙ 𝟭 (ModuleCat.{u + 1} B) = F := rfl
  have hc : c ⋙ F ≅ 𝟭 (ModuleCat.{u + 1} B) :=
    ((pointSmallEtale x).ulift.{u + 1}).constantSheafCompSheafFiberIso _ _
  exact (Functor.mapDerivedCategoryCompIso c F).app E ≪≫
    (Functor.mapDerivedCategoryNatIso hc).app E ≪≫
    (Functor.mapDerivedCategoryIdIso (ModuleCat.{u + 1} B)).app E

private noncomputable def localModelFiberIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : Scheme.{u}) (f : U ⟶ X)
    (E : DerivedCategory (ModuleCat.{u + 1} B))
    (e : (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj K ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ U) :
    ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      (((pointSmallEtale (x ≫ f)).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B))
      (Functor.additive_of_preserves_binary_products _) _ _).obj K) ≅ E := by
  let F := ((pointSmallEtale x).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let G := ((pointSmallEtale (x ≫ f)).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} B)
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  exact ((Functor.mapDerivedCategoryNatIso
    (upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} B) f x)).app K).symm ≪≫
    ((Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} B) f) F).app K).symm ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ constantDerivedFiberIso U B x E

private theorem models_iso_on_overlap
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (E : 𝒰.I₀ → DerivedCategory (ModuleCat.{u + 1} B))
    (e : ∀ i, (upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (E i))
    (i j : 𝒰.I₀) (y : 𝒰.X i) (z : 𝒰.X j) (h : 𝒰.f i y = 𝒰.f j z) :
    Nonempty (E i ≅ E j) := by
  let x := 𝒰.f i y
  let Ω := AlgebraicClosure (X.residueField x)
  let s : Spec (.of Ω) ⟶ X := X.algClosurePoint x
  have hx : s default = x := X.algClosurePoint_base x default
  obtain ⟨si, hsi, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s y hx.symm
  obtain ⟨sj, hsj, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f j) s z (hx.trans h).symm
  have ei := localModelFiberIso X B K (𝒰.X i) (𝒰.f i) (E i) (e i) si
  have ej := localModelFiberIso X B K (𝒰.X j) (𝒰.f j) (E j) (e j) sj
  rw [hsi] at ei
  rw [hsj] at ej
  exact ⟨ei.symm ≪≫ ej⟩
private theorem connected_models
    (X : Scheme.{u}) [ConnectedSpace X] (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (E : 𝒰.I₀ → DerivedCategory (ModuleCat.{u + 1} B))
    (e : ∀ i, (upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (E i))
    (E₀ : DerivedCategory (ModuleCat.{u + 1} B))
    (hne : ∃ i, Nonempty (𝒰.X i) ∧ Nonempty (E i ≅ E₀)) :
    ∀ i, Nonempty (𝒰.X i) → Nonempty (E i ≅ E₀) := by
  classical
  let O : Set X := ⋃ i, ⋃ (_ : Nonempty (E i ≅ E₀)), Set.range (𝒰.f i)
  have hopen : IsOpen O := isOpen_iUnion fun i ↦
    isOpen_iUnion fun _ ↦ (𝒰.f i).isOpenMap.isOpen_range
  have hc : Oᶜ = ⋃ i, ⋃ (_ : ¬ Nonempty (E i ≅ E₀)), Set.range (𝒰.f i) := by
    ext x
    simp only [Set.mem_compl_iff, O, Set.mem_iUnion, Set.mem_range]
    constructor
    · intro hx
      obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
      refine ⟨i, ?_, y, hy⟩
      intro hi
      exact hx ⟨i, hi, y, hy⟩
    · rintro ⟨i, hi, y, hy⟩ ⟨j, hj, z, hz⟩
      obtain ⟨eij⟩ := models_iso_on_overlap X B K 𝒰 E e i j y z (hy.trans hz.symm)
      exact hi ⟨eij ≪≫ hj.some⟩
  have hcompl : IsOpen Oᶜ := by
    rw [hc]
    exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ (𝒰.f i).isOpenMap.isOpen_range
  have hnonempty : O.Nonempty := by
    obtain ⟨i, ⟨y⟩, hi⟩ := hne
    exact ⟨𝒰.f i y, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ⟨y, rfl⟩⟩⟩⟩
  have hall : O = Set.univ :=
    (show IsClopen O from ⟨isOpen_compl_iff.mp hcompl, hopen⟩).eq_univ hnonempty
  intro i ⟨y⟩
  have hy : 𝒰.f i y ∈ O := hall.symm ▸ Set.mem_univ _
  have hy' : ∃ j, ∃ (_ : Nonempty (E j ≅ E₀)), ∃ z, 𝒰.f j z = 𝒰.f i y := by
    simpa only [O, Set.mem_iUnion, Set.mem_range] using hy
  obtain ⟨j, hj, z, hz⟩ := hy'
  obtain ⟨eij⟩ := models_iso_on_overlap X B K 𝒰 E e i j y z hz.symm
  exact ⟨eij ≪≫ hj.some⟩

private theorem connected_model_from_fiber
    (X : Scheme.{u}) [ConnectedSpace X] (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (E : 𝒰.I₀ → DerivedCategory (ModuleCat.{u + 1} B))
    (e : ∀ i, (upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (E i))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ 𝒱 : Cover.{u} etalePrecoverage X, ∀ i : 𝒱.I₀, Nonempty
      ((upperStar (ModuleCat.{u + 1} B) (𝒱.f i)).mapDerivedCategory.obj K ≅
        (constantSheaf (𝒱.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            (((pointSmallEtale x).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B))
            (Functor.additive_of_preserves_binary_products _) _ _).obj K)) := by
  classical
  let E₀ := (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    (((pointSmallEtale x).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B))
    (Functor.additive_of_preserves_binary_products _) _ _).obj K
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (x default)
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f j) x y hy
  have ej := localModelFiberIso X B K (𝒰.X j) (𝒰.f j) (E j) (e j) t
  rw [ht] at ej
  have hmodels : ∀ i, Nonempty (𝒰.X i) → Nonempty (E i ≅ E₀) :=
    connected_models X B K 𝒰 E e E₀ ⟨j, ⟨y⟩, ⟨ej.symm⟩⟩
  let 𝒱 : Cover.{u} etalePrecoverage X :=
    { I₀ := { i : 𝒰.I₀ // Nonempty (𝒰.X i) }
      X i := 𝒰.X i.1
      f i := 𝒰.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun z ↦ ?_, fun i ↦ 𝒰.map_prop i.1⟩
        obtain ⟨i, w, hw⟩ := 𝒰.exists_eq z
        exact ⟨⟨i, ⟨w⟩⟩, w, hw⟩ }
  refine ⟨𝒱, fun i ↦ ⟨?_⟩⟩
  exact e i.1 ≪≫
    (constantSheaf (𝒰.X i.1).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.mapIso
      (hmodels i.1 i.2).some

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictDerivedMap_comp
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (g : U ⟶ V)
    (a : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L)
    (b : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L ⟶
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj M) :
    restrictDerivedMap B g (a ≫ b) = restrictDerivedMap B g a ≫ restrictDerivedMap B g b := by
  simp only [restrictDerivedMap, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictDerivedMap_map
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (g : U ⟶ V) (a : K ⟶ L) :
    restrictDerivedMap B g ((upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.map a) =
      (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.map a := by
  let r := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) g.left V.hom U.hom g.w.symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  have hn := r.hom.naturality a
  change _ ≫ _ = _ ≫ _ at hn
  change (r.app K).hom ≫ _ ≫ (r.app L).inv = _
  have hh := congrArg (fun k ↦ k ≫ r.inv.app L) hn
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc, Functor.comp_map,
    Iso.hom_inv_id_app, Category.comp_id]
    using hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedHomPresheafIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L K' L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (e : K ≅ K') (f : L ≅ L') :
    derivedHomPresheaf B K L ≅ derivedHomPresheaf B K' L' :=
  NatIso.ofComponents (fun U ↦
    (Iso.homCongr ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso e)
      ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso f)).toIso)
    (by
      intro U V g
      ext a
      symm
      change restrictDerivedMap B g.unop
        ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map e.inv ≫ a ≫
          (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map f.hom) =
        (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map e.inv ≫
          restrictDerivedMap B g.unop a ≫
            (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map f.hom
      rw [restrictDerivedMap_comp, restrictDerivedMap_comp, restrictDerivedMap_map,
        restrictDerivedMap_map])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedIsoPresheafIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L K' L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (e : K ≅ K') (f : L ≅ L') :
    derivedIsoPresheaf B K L ≅ derivedIsoPresheaf B K' L' :=
  NatIso.ofComponents (fun U ↦
    (Iso.isoCongr ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso e)
      ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.mapIso f)).toIso)
    (by
      intro U V g
      ext a
      apply Iso.ext
      symm
      change restrictDerivedMap B g.unop
        ((upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map e.inv ≫ a.hom ≫
          (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.map f.hom) =
        (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map e.inv ≫
          restrictDerivedMap B g.unop a.hom ≫
            (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map f.hom
      rw [restrictDerivedMap_comp, restrictDerivedMap_comp, restrictDerivedMap_map,
        restrictDerivedMap_map])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def pullbackConstantModel
    (X U W : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (f : U ⟶ X) (g : W ⟶ U) (h : W ⟶ X) (hg : g ≫ f = h)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (E : DerivedCategory (ModuleCat.{u + 1} B))
    (e : (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj K ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E) :
    (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.obj K ≅
      (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E :=
  ((Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) g f h hg.symm)).app K) ≪≫
    ((Functor.mapDerivedCategoryCompIso _ _).app K).symm ≪≫
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.mapIso e ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app E ≪≫
    (Functor.mapDerivedCategoryNatIso
      (upperStarConstantSheafIso (ModuleCat.{u + 1} B) g)).app E

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def overSheafificationIso
    (X : Scheme.{u}) (U : X.Etale) (P : X.Etaleᵒᵖ ⥤ Type (u + 1)) :
    (Scheme.Etale.overSheafEquiv U (Type (u + 1))).functor.obj
      (((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj P).over U) ≅
        (presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).obj
          ((Scheme.Etale.etaleToOver U).op ⋙ (Over.forget U).op ⋙ P) := by
  let R := (Over.forget U).pushforwardContinuousSheafificationCompatibility
    (Type (u + 1)) (X.smallEtaleTopology.over U) X.smallEtaleTopology
  let T := (Scheme.Etale.etaleToOver U).pushforwardContinuousSheafificationCompatibility
    (Type (u + 1)) U.left.smallEtaleTopology (X.smallEtaleTopology.over U)
  exact (Scheme.Etale.overSheafEquiv U (Type (u + 1))).functor.mapIso (R.symm.app P) ≪≫
    T.symm.app ((Over.forget U).op ⋙ P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_mapping_sheaves_restriction
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.Etale) :
    Nonempty
      (((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
        (derivedHomPresheaf B K L)).over U ≅
        (Scheme.Etale.overSheafEquiv U (Type (u + 1))).inverse.obj
          ((presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).obj
            (derivedHomPresheaf B
              ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K)
              ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L)))) ∧
    Nonempty
      (((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
        (derivedIsoPresheaf B K L)).over U ≅
        (Scheme.Etale.overSheafEquiv U (Type (u + 1))).inverse.obj
          ((presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).obj
            (derivedIsoPresheaf B
              ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K)
              ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L))))  := by
  let S := Scheme.Etale.overSheafEquiv U (Type (u + 1))
  obtain ⟨hH, hI⟩ := derived_mapping_presheaves_restriction X B K L U
  constructor
  · refine ⟨?_⟩
    exact S.unitIso.app _ ≪≫ S.inverse.mapIso
      (overSheafificationIso X U (derivedHomPresheaf B K L) ≪≫
        (presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).mapIso hH.some)
  · refine ⟨?_⟩
    exact S.unitIso.app _ ≪≫ S.inverse.mapIso
      (overSheafificationIso X U (derivedIsoPresheaf B K L) ≪≫
        (presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).mapIso hI.some)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Bounded finite lisse complexes have finite constant local models, finite lisse
Hom and isomorphism sheaves, and on a connected scheme the model is any geometric fibre.
Source: Stacks, Tag 094G and the finite-source extension of Tag 09BE
(blueprint: lem-weil-pbc-finite-ring-derived-local-constancy).

Proof:
1. Use finite_locally_constant_module_values_iff to obtain finite module values for
   every cohomology sheaf on every localized site. Apply the general-site bounded
   constant-model theorem. Identify localized etale sheaves with sheaves on the cover
   schemes, and reduce the covering index to the universe of X using joint surjectivity.
2. For a second complex L, refine its model cover and K's model cover by fiber products.
   Pullback composition and the constant-sheaf comparison transport both local models
   to this common cover.
3. The constant-complex mapping comparison identifies local Hom and Isom with the
   corresponding algebraic sets. Restriction of mapping presheaves, followed by
   Mathlib's sheafification compatibility, identifies their sheaves with the restrictions
   of the global mapping sheaves. Algebraic Hom is finite by a bounded-above finite
   free resolution; Isom injects into Hom. Constant finite local values give local
   constancy and finite geometric stalks, hence finite local constancy for both sheaves.
4. On a connected X, choose the derived stalk at the given geometric point. The union
   of images of cover members with that model class is open. Its complement is the
   union of the other images: a common geometric point on an overlap identifies the
   two models. Thus the union is also closed and is all X by connectedness. Discard
   empty members and compose the model isomorphisms with their identifications with
   the chosen derived stalk. No finite Tor bound is used. -/
theorem finiteRing_derived_local_constancy
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj K))
    (hlisse : ∀ n : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj K)) :
    (∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ E : CochainComplex (ModuleCat.{u + 1} B) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        (∀ n : ℤ, Finite (E.X n)) ∧ Nonempty
          ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))) ∧
    (∀ L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj L)) →
      (∀ n : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj L)) →
      IsFiniteLocallyConstantSheafOfTypes
        ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
          (derivedHomPresheaf B K L)) ∧
      IsFiniteLocallyConstantSheafOfTypes
        ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
          (derivedIsoPresheaf B K L))) ∧
    (∀ (U : Scheme.{u}) (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) →
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n)) →
      (∀ n : ℤ, Finite (E.X n)) → (∀ n : ℤ, Finite (G.X n)) →
      Nonempty
        (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (derivedHomPresheaf B
            (DerivedCategory.Q.obj
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E))
            (DerivedCategory.Q.obj
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj G)))) ≅
          (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
            (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G))) ∧
    (ConnectedSpace X → ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ X),
      ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀, Nonempty
        ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
            ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
              (((pointSmallEtale x).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B))
              (Functor.additive_of_preserves_binary_products _) _ _).obj K))) := by
  obtain ⟨𝒰, hmodels⟩ := local_bounded_finite_models X B K hbounded hlisse
  refine ⟨⟨𝒰, hmodels⟩, ?_, ?_, ?_⟩
  · intro L hLbounded hLlisse
    classical
    obtain ⟨𝒱, hLmodels⟩ := local_bounded_finite_models X B L hLbounded hLlisse
    choose E hE hEfin e using hmodels
    choose G hG hGfin g using hLmodels
    let 𝒲 : Cover.{u} etalePrecoverage X := 𝒰.inter 𝒱
    have ek (i : 𝒲.I₀) :
        (upperStar (ModuleCat.{u + 1} B) (𝒲.f i)).mapDerivedCategory.obj K ≅
          DerivedCategory.Q.obj
            (((constantSheaf (𝒲.X i).smallEtaleTopology
              (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (E i.1)) := by
      exact pullbackConstantModel X (𝒰.X i.1) (𝒲.X i) B (𝒰.f i.1)
        (pullback.fst (𝒰.f i.1) (𝒱.f i.2)) (𝒲.f i) rfl K
        (DerivedCategory.Q.obj (E i.1))
        ((e i.1).some ≪≫ ((constantSheaf (𝒰.X i.1).smallEtaleTopology
          (ModuleCat.{u + 1} B)).mapDerivedCategoryFactors.app (E i.1)).symm) ≪≫
        (constantSheaf (𝒲.X i).smallEtaleTopology
          (ModuleCat.{u + 1} B)).mapDerivedCategoryFactors.app (E i.1)
    have el (i : 𝒲.I₀) :
        (upperStar (ModuleCat.{u + 1} B) (𝒲.f i)).mapDerivedCategory.obj L ≅
          DerivedCategory.Q.obj
            (((constantSheaf (𝒲.X i).smallEtaleTopology
              (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (G i.2)) := by
      exact pullbackConstantModel X (𝒱.X i.2) (𝒲.X i) B (𝒱.f i.2)
        (pullback.snd (𝒰.f i.1) (𝒱.f i.2)) (𝒲.f i) pullback.condition.symm L
        (DerivedCategory.Q.obj (G i.2))
        ((g i.2).some ≪≫ ((constantSheaf (𝒱.X i.2).smallEtaleTopology
          (ModuleCat.{u + 1} B)).mapDerivedCategoryFactors.app (G i.2)).symm) ≪≫
        (constantSheaf (𝒲.X i).smallEtaleTopology
          (ModuleCat.{u + 1} B)).mapDerivedCategoryFactors.app (G i.2)
    have hf (i : 𝒲.I₀) : Finite (DerivedCategory.Q.obj (E i.1) ⟶
        DerivedCategory.Q.obj (G i.2)) :=
      DerivedCategory.finite_derived_hom_of_bounded_finite B (E i.1) (G i.2)
        (hE i.1) (hG i.2) (hEfin i.1) (hGfin i.2)
    have hi (i : 𝒲.I₀) : Finite (DerivedCategory.Q.obj (E i.1) ≅
        DerivedCategory.Q.obj (G i.2)) := by
      have := hf i
      exact Finite.of_injective Iso.hom (fun _ _ h ↦ Iso.ext h)
    have evalues (i : 𝒲.I₀) :=
      finiteRing_constant_derived_mapping_sheaves (𝒲.X i) B (E i.1) (G i.2)
        (hE i.1) (hG i.2) (hEfin i.1) (hGfin i.2)
    constructor
    · apply finite_locally_constant_of_finite_values X _ 𝒲
        (fun i ↦ DerivedCategory.Q.obj (E i.1) ⟶ DerivedCategory.Q.obj (G i.2)) hf
      intro i
      let U := 𝒲.etalePrecoverageToEtale i
      let S := Scheme.Etale.overSheafEquiv U (Type (u + 1))
      let M := DerivedCategory.Q.obj (E i.1) ⟶ DerivedCategory.Q.obj (G i.2)
      let c := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
        (X.smallEtaleTopology.over U) U.left.smallEtaleTopology (Type (u + 1))
        CategoryTheory.Over.mkIdTerminal
      exact (derived_mapping_sheaves_restriction X B K L U).1.some ≪≫
        S.inverse.mapIso
          ((presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).mapIso
            (derivedHomPresheafIso U.left B (ek i) (el i)) ≪≫ (evalues i).1.some) ≪≫
        S.inverse.mapIso ((c.app M).symm) ≪≫ S.unitIso.symm.app _
    · apply finite_locally_constant_of_finite_values X _ 𝒲
        (fun i ↦ DerivedCategory.Q.obj (E i.1) ≅ DerivedCategory.Q.obj (G i.2)) hi
      intro i
      let U := 𝒲.etalePrecoverageToEtale i
      let S := Scheme.Etale.overSheafEquiv U (Type (u + 1))
      let M := DerivedCategory.Q.obj (E i.1) ≅ DerivedCategory.Q.obj (G i.2)
      let c := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
        (X.smallEtaleTopology.over U) U.left.smallEtaleTopology (Type (u + 1))
        CategoryTheory.Over.mkIdTerminal
      exact (derived_mapping_sheaves_restriction X B K L U).2.some ≪≫
        S.inverse.mapIso
          ((presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).mapIso
            (derivedIsoPresheafIso U.left B (ek i) (el i)) ≪≫ (evalues i).2.some) ≪≫
        S.inverse.mapIso ((c.app M).symm) ≪≫ S.unitIso.symm.app _
  · intro U E G hE hG hEfin hGfin
    exact (finiteRing_constant_derived_mapping_sheaves U B E G hE hG hEfin hGfin).1
  · intro hconn Ω _ _ x
    have := hconn
    choose E hboundedE hfiniteE e using hmodels
    apply connected_model_from_fiber X B K 𝒰 (fun i ↦ DerivedCategory.Q.obj (E i)) _ Ω x
    intro i
    exact (e i).some ≪≫
      ((constantSheaf (𝒰.X i).smallEtaleTopology
        (ModuleCat.{u + 1} B)).mapDerivedCategoryFactors.app (E i)).symm

end AlgebraicGeometry.Etale
