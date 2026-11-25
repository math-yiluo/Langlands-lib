/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

import WeilConjectures.CategoryTheory.ProperBaseChange.BoundedConstantModuleChainMapLocal
import WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleLocalActual
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Algebraic local representatives of derived maps of finite constant complexes -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  AlgebraicGeometry.Scheme Opposite
namespace AlgebraicGeometry.Etale

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def overRestrictionIso
    {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B] (U : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅
        upperStar (ModuleCat.{u + 1} B) U.hom :=
  let R := GrothendieckTopology.localizationRestriction (ModuleCat.{u + 1} B)
    @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl U.hom U.prop
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅ R :=
    ((fullyFaithfulSheafToPresheaf U.left.smallEtaleTopology
      (ModuleCat.{u + 1} B)).whiskeringRight _).preimageIso
        (NatIso.ofComponents
          (fun F ↦ by
            change ((Scheme.Etale.etaleToOver U).op ⋙
              (Over.forget U).op ⋙ F.obj) ≅ _
            exact Functor.isoWhiskerRight
              (NatIso.op (Scheme.Etale.etaleToOverCompForgetIso U).symm) F.obj)
          (by
            intro F G φ
            apply NatTrans.ext
            funext T
            dsimp
            exact (φ.hom.naturality _).symm))
  e ≪≫ (GrothendieckTopology.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale
    le_rfl U.hom U.prop).symm

private theorem map_conjugate_eq
    {A D H : Type*} [Category A] [Category D] [Category H]
    {F G : A ⥤ D} (e : F ≅ G) (L : D ⥤ H)
    {P Q : A} (a : F.obj P ⟶ F.obj Q) (b : P ⟶ Q)
    (h : L.map ((e.app P).inv ≫ a ≫ (e.app Q).hom) = L.map (G.map b)) :
    L.map a = L.map (F.map b) := by
  apply (cancel_epi (L.map (e.app P).inv)).mp
  apply (cancel_mono (L.map (e.app Q).hom)).mp
  rw [← L.map_comp, ← L.map_comp, Category.assoc, h]
  rw [← L.map_comp, ← L.map_comp, Category.assoc]
  change L.map (G.map b) = L.map (e.inv.app P ≫ F.map b ≫ e.hom.app Q)
  rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]

private theorem chain_map_local
    (X Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (f : Y ⟶ X)
    (P G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hP : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    [∀ n : ℤ, Module.Finite B (P.X n)]
    (α : ((upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      ((upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (.up ℤ)).obj G)) :
    ∃ S ∈ Y.smallEtaleTopology (Scheme.Etale.mk (𝟙 Y)),
      ∀ (V : Y.Etale) (g : V ⟶ Scheme.Etale.mk (𝟙 Y)), S g → ∃ b : P ⟶ G,
        ((upperStar (ModuleCat.{u + 1} B) V.hom).mapHomologicalComplex (.up ℤ)).map α =
          ((upperStar (ModuleCat.{u + 1} B) V.hom).mapHomologicalComplex (.up ℤ)).map
            (((upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).map
              (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (.up ℤ)).map b)) := by
  let cX := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let cY := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)
  let R := upperStar (ModuleCat.{u + 1} B) f
  let e := Functor.mapHomologicalComplexCompIso
    (upperStarConstantSheafIso (ModuleCat.{u + 1} B) f) (.up ℤ)
  let a := (e.app P).inv ≫ α ≫ (e.app G).hom
  have (V : Y.Etale) :
      (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨S, hS, h⟩ := exists_bounded_constant_module_chain_map_local
    Y.smallEtaleTopology B P G hP (Scheme.Etale.mk (𝟙 Y)) a
  refine ⟨S, hS, fun V g hg ↦ ?_⟩
  obtain ⟨b, hb⟩ := h V g hg
  let Z := (Scheme.Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor
  have : Z.Additive := Functor.additive_of_preserves_binary_products _
  let p := Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V
  let L := upperStar (ModuleCat.{u + 1} B) V.hom
  let ep := Functor.mapHomologicalComplexCompIso (overRestrictionIso B V) (.up ℤ)
  have heq : (L.mapHomologicalComplex (.up ℤ)).map a =
      (L.mapHomologicalComplex (.up ℤ)).map
        ((cY.mapHomologicalComplex (.up ℤ)).map b) := by
    apply (cancel_epi (ep.hom.app _)).mp
    rw [← ep.hom.naturality, ← ep.hom.naturality]
    exact congrArg (fun t ↦ (Z.mapHomologicalComplex (.up ℤ)).map t ≫ ep.hom.app _) hb
  exact ⟨b, map_conjugate_eq e (L.mapHomologicalComplex (.up ℤ)) α b heq⟩

private theorem map_eq_of_iso
    {A D : Type*} [Category A] [Category D] {F G : A ⥤ D} (e : F ≅ G)
    {P Q : A} {a b : P ⟶ Q} (h : G.map a = G.map b) : F.map a = F.map b := by
  apply (cancel_mono (e.hom.app Q)).mp
  rw [e.hom.naturality, e.hom.naturality, h]

private theorem local_free_point
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (P G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hP : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hfree : ∀ n : ℤ, ∃ r : ℕ, Nonempty (P.X n ≅ ModuleCat.of B (Fin r → B)))
    (φ : DerivedCategory.Q.obj
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶ DerivedCategory.Q.obj
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (.up ℤ)).obj G)) (x : X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : AlgebraicGeometry.Etale f) (y : Y)
      (b : P ⟶ G), f y = x ∧
      (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map φ =
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map
          (DerivedCategory.Q.map
            (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
              (.up ℤ)).map b)) := by
  classical
  let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let cP := (c.mapHomologicalComplex (.up ℤ)).obj P
  let cG := (c.mapHomologicalComplex (.up ℤ)).obj G
  have (n : ℤ) : Module.Finite B (P.X n) := by
    obtain ⟨r, ⟨e⟩⟩ := hfree n
    exact Module.Finite.equiv e.toLinearEquiv.symm
  obtain ⟨𝒰, h𝒰⟩ := (AlgebraicGeometry.finiteFree_etale_local_actual X B P hP hfree cG).1 φ
  obtain ⟨i, t, ht⟩ := 𝒰.exists_eq x
  let R := upperStar (ModuleCat.{u + 1} B) (𝒰.f i)
  obtain ⟨a, ha⟩ := h𝒰 i
  obtain ⟨S, hS, h⟩ := chain_map_local X (𝒰.X i) B (𝒰.f i) P G hP a
  obtain ⟨V, g, hg, z, hz⟩ := (Scheme.mem_smallEtaleTopology_iff S).1 hS t
  obtain ⟨b, hb⟩ := h V g hg
  let L := upperStar (ModuleCat.{u + 1} B) V.hom
  let a' := (R.mapHomologicalComplex (.up ℤ)).map
    ((c.mapHomologicalComplex (.up ℤ)).map b)
  have hh : L.mapDerivedCategory.map (DerivedCategory.Q.map a) =
      L.mapDerivedCategory.map (DerivedCategory.Q.map a') := by
    apply (cancel_mono (L.mapDerivedCategoryFactors.hom.app _)).mp
    rw [L.mapDerivedCategoryFactors_hom_naturality,
      L.mapDerivedCategoryFactors_hom_naturality]
    rw [hb]
  have ha' : DerivedCategory.Q.map a' =
      R.mapDerivedCategoryFactors.inv.app cP ≫
        R.mapDerivedCategory.map (DerivedCategory.Q.map
          ((c.mapHomologicalComplex (.up ℤ)).map b)) ≫
        R.mapDerivedCategoryFactors.hom.app cG := by
    rw [R.mapDerivedCategoryFactors_hom_naturality]
    simp only [Iso.inv_hom_id_app_assoc]
    rfl
  rw [ha, ha', L.mapDerivedCategory.map_comp, L.mapDerivedCategory.map_comp,
    L.mapDerivedCategory.map_comp, L.mapDerivedCategory.map_comp] at hh
  have heq : (R.mapDerivedCategory ⋙ L.mapDerivedCategory).map φ =
      (R.mapDerivedCategory ⋙ L.mapDerivedCategory).map
        (DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).map b)) := by
    apply (cancel_epi (L.mapDerivedCategory.map
      (R.mapDerivedCategoryFactors.inv.app cP))).mp
    apply (cancel_mono (L.mapDerivedCategory.map
      (R.mapDerivedCategoryFactors.hom.app cG))).mp
    simpa only [Functor.comp_map, Category.assoc] using hh
  let e := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) V.hom (𝒰.f i) (V.hom ≫ 𝒰.f i) rfl) ≪≫
      (Functor.mapDerivedCategoryCompIso R L).symm
  refine ⟨V.left, V.hom ≫ 𝒰.f i, inferInstance, z, b, ?_, map_eq_of_iso e heq⟩
  have hw : g.left = V.hom := by
    have hw := g.w
    change g.left ≫ 𝟙 _ = V.hom at hw
    simpa only [Category.comp_id] using hw
  change (𝒰.f i) (V.hom z) = x
  exact (congrArg (fun q : V.left ⟶ 𝒰.X i ↦ (𝒰.f i) (q z)) hw).symm.trans
    ((congrArg (fun t : 𝒰.X i ↦ (𝒰.f i) t) hz).trans ht)

private theorem finite_approximation
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (E : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (m : ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u + 1} B) ℤ) (a b : ℤ)
      (Z : DerivedCategory (ModuleCat.{u + 1} B))
      (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj E)
      (g : DerivedCategory.Q.obj E ⟶ Z) (h : Z ⟶ (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, ∃ n : ℕ, Nonempty (P.X i ≅ ModuleCat.of B (Fin n → B))) ∧
      Triangle.mk f g h ∈ distTriang _ ∧ Z.IsLE m := by
  classical
  have hpc : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj E) := by
    apply (DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology.{u + 1, u + 1, u + 1}
      B (DerivedCategory.Q.obj E)).2
    obtain ⟨a, b, hzero⟩ := hE
    refine ⟨⟨b, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
    · exact ((E.sc i).isZero_homology_of_isZero_X₂ (hzero i (Or.inr hi))).of_iso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} B) i).app E)
    · have := hEfin i
      have : Finite (E.cycles i) := Finite.of_injective (E.iCycles i)
        ((ModuleCat.mono_iff_injective _).mp inferInstance)
      have : Finite (E.homology i) := Finite.of_surjective (E.homologyπ i)
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      have : Finite ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} B)
          (.up ℤ) i).obj E) := ‹Finite (E.homology i)›
      have : Finite ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} B) i).obj
          (DerivedCategory.Q.obj E)) := Finite.of_surjective
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} B) i).inv.app E)
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      exact Module.Finite.of_finite
  obtain ⟨P, a, b, ha, hb, hfree, f, hf, _⟩ :=
    (DerivedCategory.isPseudoCoherent_iff_forall_isMPseudoCoherent B E).1 hpc m
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  refine ⟨P, a, b, Z, f, g, h, ha, hb, ?_, hT, ?_⟩
  · intro i
    have := (hfree i).1
    have := (hfree i).2
    by_cases hB : Nontrivial B
    · have := hB
      exact ⟨Module.finrank B (P.X i),
        ⟨(Module.finBasis B (P.X i)).equivFun.toModuleIso⟩⟩
    · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp hB
      have : Subsingleton (P.X i) := Module.subsingleton B (P.X i)
      exact ⟨0, ⟨(LinearEquiv.ofSubsingleton (R := B) (P.X i) (Fin 0 → B)).toModuleIso⟩⟩
  · apply (DerivedCategory.isLE_iff _ m).2
    intro i hi
    let T := Triangle.mk f g h
    have hfi : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} B) i).map
      T.mor₁) := hf i hi
    have hfi' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} B) (i + 1)).map
      T.mor₁) := hf (i + 1) (by omega)
    apply (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂
    · exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 inferInstance
    · exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT i (i + 1)).1 inferInstance

private theorem precomp_triangle_bijective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (G : DerivedCategory A) (m n : ℤ) [T.obj₃.IsLE m] [G.IsGE n] (hmn : m + 1 < n) :
    Function.Bijective (fun b : T.obj₂ ⟶ G ↦ T.mor₁ ≫ b) := by
  constructor
  · intro b c hbc
    change T.mor₁ ≫ b = T.mor₁ ≫ c at hbc
    have hz : T.mor₁ ≫ (b - c) = 0 := by rw [Preadditive.comp_sub, hbc, sub_self]
    obtain ⟨a, ha⟩ := T.yoneda_exact₂ hT (b - c) hz
    have hzero : a = 0 := DerivedCategory.TStructure.t.zero a m n (by omega)
    rw [hzero, comp_zero] at ha
    exact sub_eq_zero.mp ha
  · intro b
    have : DerivedCategory.TStructure.t.IsLE T.invRotate.obj₁ (m + 1) :=
      DerivedCategory.TStructure.t.isLE_shift T.obj₃ m (-1) (m + 1) (by omega)
    have hz : T.invRotate.mor₁ ≫ b = 0 :=
      DerivedCategory.TStructure.t.zero _ (m + 1) n hmn
    obtain ⟨a, ha⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) b hz
    exact ⟨a, ha.symm⟩

private theorem restrict_map
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {V W : X.Etale} (f : W ⟶ V) (a : K ⟶ L) :
    restrictDerivedMap B f
        ((upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.map a) =
      (upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory.map a := by
  let r := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) f.left V.hom W.hom f.w.symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  have hn := r.hom.naturality a
  change _ ≫ _ = _ ≫ _ at hn
  change (r.app K).hom ≫ _ ≫ (r.app L).inv = _
  have hh := congrArg (fun k ↦ k ≫ r.inv.app L) hn
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc, Functor.comp_map,
    Iso.hom_inv_id_app, Category.comp_id] using hh.symm

private noncomputable def constantHomMap
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (E G : DerivedCategory (ModuleCat.{u + 1} B)) :
    (Functor.const X.Etaleᵒᵖ).obj (E ⟶ G) ⟶
      derivedHomPresheaf B
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj G)
    where
  app V := ↾fun a ↦ (upperStar (ModuleCat.{u + 1} B) V.unop.hom).mapDerivedCategory.map
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.map a)
  naturality V W f := by
    ext a
    exact (restrict_map X B f.unop _).symm

private theorem local_finite_point
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n))
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj E) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj G)) (x : X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : AlgebraicGeometry.Etale f) (y : Y)
      (b : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G), f y = x ∧
      (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map α =
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.map
            b) := by
  classical
  obtain ⟨lo, hi, hzero⟩ := hG
  have hGge : (DerivedCategory.Q.obj G).IsGE lo := by
    apply (DerivedCategory.isGE_iff _ lo).2
    intro i hi
    exact ((G.sc i).isZero_homology_of_isZero_X₂ (hzero i (Or.inl hi))).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} B) i).app G)
  obtain ⟨P, a, b, Z, f, g, h, hPa, hPb, hfree, hT, hZ⟩ :=
    finite_approximation B E hE hEfin (lo - 2)
  let T := Triangle.mk f g h
  have hT' : T ∈ distTriang _ := hT
  have hP : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n) :=
    ⟨a, b, fun n hn ↦ hn.elim (fun hn ↦ P.isZero_of_isStrictlyGE a n hn)
      (fun hn ↦ P.isZero_of_isStrictlyLE b n hn)⟩
  let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let φ := c.mapDerivedCategoryFactors.inv.app P ≫ c.mapDerivedCategory.map f ≫ α ≫
    c.mapDerivedCategoryFactors.hom.app G
  obtain ⟨Y, k, hk, y, b', hy, heq⟩ := local_free_point X B P G hP hfree φ x
  have hb' : DerivedCategory.Q.map
      ((c.mapHomologicalComplex (.up ℤ)).map b') =
      c.mapDerivedCategoryFactors.inv.app P ≫
        c.mapDerivedCategory.map (DerivedCategory.Q.map b') ≫
        c.mapDerivedCategoryFactors.hom.app G := by
    rw [c.mapDerivedCategoryFactors_hom_naturality]
    simp only [Iso.inv_hom_id_app_assoc]
  let : T.obj₃.IsLE (lo - 2) := hZ
  have hfbij := precomp_triangle_bijective T hT' (DerivedCategory.Q.obj G)
    (lo - 2) lo (by omega)
  obtain ⟨b'', hb''⟩ := hfbij.surjective (DerivedCategory.Q.map b')
  let R := upperStar (ModuleCat.{u + 1} B) k
  have hcZ := c.isLE_mapDerivedCategory_obj Z (lo - 2)
  have hcG := c.isGE_mapDerivedCategory_obj (DerivedCategory.Q.obj G) lo
  have hRZ := R.isLE_mapDerivedCategory_obj (c.mapDerivedCategory.obj Z) (lo - 2)
  have hRG := R.isGE_mapDerivedCategory_obj
    (c.mapDerivedCategory.obj (DerivedCategory.Q.obj G)) lo
  let T' := R.mapDerivedCategory.mapTriangle.obj (c.mapDerivedCategory.mapTriangle.obj T)
  let : T'.obj₃.IsLE (lo - 2) := hRZ
  have hT'' : T' ∈ distTriang _ := R.mapDerivedCategory.map_distinguished _
    (c.mapDerivedCategory.map_distinguished _ hT')
  have hbij := precomp_triangle_bijective T' hT''
    (R.mapDerivedCategory.obj (c.mapDerivedCategory.obj (DerivedCategory.Q.obj G)))
      (lo - 2) lo (by omega)
  refine ⟨Y, k, hk, y, b'', hy, hbij.injective ?_⟩
  change R.mapDerivedCategory.map (c.mapDerivedCategory.map f) ≫
      R.mapDerivedCategory.map α =
    R.mapDerivedCategory.map (c.mapDerivedCategory.map f) ≫
      R.mapDerivedCategory.map (c.mapDerivedCategory.map b'')
  change f ≫ b'' = DerivedCategory.Q.map b' at hb''
  rw [← R.mapDerivedCategory.map_comp, ← R.mapDerivedCategory.map_comp,
    ← c.mapDerivedCategory.map_comp, hb'']
  rw [hb'] at heq
  dsimp only [φ] at heq
  apply (cancel_epi (R.mapDerivedCategory.map
    (c.mapDerivedCategoryFactors.inv.app P))).mp
  apply (cancel_mono (R.mapDerivedCategory.map
    (c.mapDerivedCategoryFactors.hom.app G))).mp
  simpa only [Functor.map_comp, Category.assoc] using heq

/-- A derived morphism between restrictions of bounded finite constant complexes is
locally the restriction of an algebraic derived morphism.

Source: Stacks Project, sites-cohomology.tex, Tags 09BE and 08FR, with the finite-source
truncation argument of the constant derived mapping sheaf lemma.
(blueprint: lem-weil-pbc-finite-ring-constant-derived-map-local)

Proof: Finite terms give finite homology. Since a finite ring is Noetherian, the
cohomology criterion makes E pseudo-coherent. An m-pseudo-coherent approximation,
for m two below a lower bound of G, gives a bounded finite free complex P -> E.
The homology sequence puts its cone in degrees at most m. Orthogonality applied
to the cone and its negative shift, and the exact Hom sequences of the triangle
and its inverse rotation, identify maps from E to G with maps from P to G.
Exact constant realization and inverse image preserve this comparison. Local-actual
represents the map from constant P by a chain map on an etale cover. Descending its
finitely many components gives an algebraic chain map on a further covering sieve;
injectivity of the constant-section units reflects the chain equations. On objects
covered by the empty sieve all sheaves are zero. Lift the algebraic derived class
through the approximation bijection and use the localized bijection for equality.
Finally apply this argument over V and use the constant inverse-image comparison.
The image sieve of the constant algebraic Hom presheaf comparison is covering,
because the local lifts cover every point of V. Zero rings, empty schemes, and
zero complexes are included. -/
theorem finiteRing_constant_derived_map_local
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (hG : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hEfin : ∀ n : ℤ, Finite (E.X n)) (_hGfin : ∀ n : ℤ, Finite (G.X n))
    (V : X.Etale)
    (α : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj E)) ⟶
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj G))) :
    ∃ S ∈ X.smallEtaleTopology V, ∀ (W : X.Etale) (f : W ⟶ V), S f →
      ∃ a : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G,
        restrictDerivedMap B f α =
          (upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory.map
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.map
              a) := by
  classical
  let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let R := upperStar (ModuleCat.{u + 1} B) V.hom
  let cV := constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} B)
  let e := Functor.mapDerivedCategoryCompIso c R ≪≫
    Functor.mapDerivedCategoryNatIso
      (upperStarConstantSheafIso (ModuleCat.{u + 1} B) V.hom)
  let β := (e.app (DerivedCategory.Q.obj E)).inv ≫ α ≫
    (e.app (DerivedCategory.Q.obj G)).hom
  let H := constantHomMap X B (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G)
  refine ⟨Presheaf.imageSieve H α, ?_, fun W f hf ↦ ?_⟩
  · apply (Scheme.mem_smallEtaleTopology_iff _).2
    intro x
    obtain ⟨Y, k, hk, y, a, hy, heq⟩ :=
      local_finite_point V.left B E G hE hG hEfin β x
    have := hk
    let W : X.Etale := Scheme.Etale.mk (k ≫ V.hom)
    let f : W ⟶ V := MorphismProperty.Over.homMk k
    let L := upperStar (ModuleCat.{u + 1} B) k
    have heq' : L.mapDerivedCategory.map α =
        L.mapDerivedCategory.map (R.mapDerivedCategory.map (c.mapDerivedCategory.map a)) :=
      map_conjugate_eq e L.mapDerivedCategory α a heq
    have hres : restrictDerivedMap B f α =
        (upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory.map
          (c.mapDerivedCategory.map a) := by
      rw [← restrict_map X B f (c.mapDerivedCategory.map a)]
      unfold restrictDerivedMap
      exact congrArg (fun t ↦
        (derivedMapRestrictionIso B f (c.mapDerivedCategory.obj
          (DerivedCategory.Q.obj E))).hom ≫ t ≫
          (derivedMapRestrictionIso B f (c.mapDerivedCategory.obj
            (DerivedCategory.Q.obj G))).inv) heq'
    exact ⟨W, f, ⟨a, hres.symm⟩, y, hy⟩
  · obtain ⟨a, ha⟩ := hf
    exact ⟨a, ha.symm⟩

end AlgebraicGeometry.Etale
