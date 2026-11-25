/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.StructureSheafHomotopyGlobalSections
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Derived global sections and maps from the structure sheaf
Source: Stacks Project, Tag 09M1, proof, first paragraph.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem descendHomEquiv
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive B]
    (L : C ⥤ D) [L.Additive] (R : D ⥤ B) (P : C) (A : B)
    (S : D) (s : S ≅ L.obj P) (T : C → Prop)
    (rep : ∀ E : D, ∃ J : C, T J ∧ Nonempty (E ≅ L.obj J))
    (full : ∀ (J J' : C), T J' → Function.Bijective
      (L.map : (J ⟶ J') → (L.obj J ⟶ L.obj J')))
    (b : ∀ (J : C), T J → (P ⟶ J) ≃+ (A ⟶ R.obj (L.obj J)))
    (nat : ∀ (J J' : C) (hJ : T J) (hJ' : T J') (f : J ⟶ J') (g : P ⟶ J),
      b J' hJ' (g ≫ f) = b J hJ g ≫ R.map (L.map f)) :
    ∃ e : ∀ E : D, (S ⟶ E) ≃+ (A ⟶ R.obj E),
      ∀ (E E' : D) (f : E ⟶ E') (g : S ⟶ E),
        e E' (g ≫ f) = e E g ≫ R.map f := by
  classical
  choose J hJ i using rep
  let i (E : D) : E ≅ L.obj (J E) := Classical.choice (i E)
  let l (E : D) := AddEquiv.ofBijective
    (L.mapAddHom (X := P) (Y := J E)) (full P (J E) (hJ E))
  let c (E : D) : (S ⟶ E) ≃+ (L.obj P ⟶ L.obj (J E)) :=
    { toEquiv := Iso.homCongr s (i E)
      map_add' := by intro f g; simp [Iso.homCongr] }
  let d (E : D) : (A ⟶ R.obj (L.obj (J E))) ≃+ (A ⟶ R.obj E) :=
    { toEquiv := Iso.homCongr (Iso.refl A) (R.mapIso (i E)).symm
      map_add' := by intro f g; simp [Iso.homCongr] }
  let e (E : D) := (c E).trans ((l E).symm.trans ((b (J E) (hJ E)).trans (d E)))
  refine ⟨e, ?_⟩
  intro E E' f g
  obtain ⟨h, hh⟩ := (full (J E) (J E') (hJ E')).2
    ((i E).inv ≫ f ≫ (i E').hom)
  let k := (l E).symm (c E g)
  have hk : L.map k = s.inv ≫ g ≫ (i E).hom := by
    exact (l E).apply_symm_apply (c E g)
  have hk' : (l E').symm (c E' (g ≫ f)) = k ≫ h := by
    apply (l E').injective
    rw [AddEquiv.apply_symm_apply]
    change s.inv ≫ (g ≫ f) ≫ (i E').hom = L.map (k ≫ h)
    rw [L.map_comp, hk, hh]
    simp
  dsimp only [e, AddEquiv.trans_apply, d, Iso.homCongr, Equiv.coe_fn_mk,
    Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_inv]
  simp only [Category.id_comp]
  change b (J E') (hJ E') ((l E').symm (c E' (g ≫ f))) ≫ R.map (i E').inv =
    (b (J E) (hJ E) k ≫ R.map (i E).inv) ≫ R.map f
  rw [hk', nat (J E) (J E') (hJ E) (hJ E') h k, hh]
  simp only [Functor.map_comp, Category.assoc]
  simp

/-- The structure-sheaf case of the derived global-sections adjunction.
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph; Tag 0B6A for the K-injective computation of derived global sections.
(blueprint: lem-pc-derived-structure-sheaf-global-sections-hom).
Proof: Represent E by a K-injective complex J of module sheaves. Localization identifies
maps from O_X[0] to E with homotopy classes of chain maps O_X[0] to J. Evaluation at 1
identifies such chain maps with chain maps A[0] to Γ(X,J): in degree zero both are global
cycles, and in degree -1 their homotopies are global sections whose differentials are
the differences of these cycles. These identifications respect addition. Since A is
free of rank one, A[0] is K-projective, so its homotopy classes of maps to Γ(X,J) are
its derived maps to QΓ(X,J). The K-injective computation identifies the latter target
with RΓ(E). For a morphism E to E', take K-injective representatives and lift it to a
chain map using the full faithfulness of localization on K-injectives. Evaluation at 1
commutes with postcomposition and with Γ of that chain map. Homotopic lifts give the
same class. Comparison homotopy equivalences between resolutions give the same maps,
so the resulting equivalences are natural for all derived morphisms. No acyclicity of
Γ(X,J) is required: K-projectivity of A[0] suffices on the module side. -/
theorem derivedStructureSheaf_globalSections_hom (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let RΓ := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
    let A₀ := (DerivedCategory.singleFunctor
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0).obj
        (ModuleCat.of ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
          ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    ∃ e : ∀ E : schemeDerivedCategory X,
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))) ⟶ E) ≃+
        (A₀ ⟶ RΓ.obj E),
      ∀ (E E' : schemeDerivedCategory X) (f : E ⟶ E') (g :
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings X.toRingedSpace)) ⟶ E),
        e E' (g ≫ f) = e E g ≫ RΓ.map f := by
  classical
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let A := (moduleRings X.toRingedSpace).obj.obj (op ⊤)
  let D := ModuleCat.{u} A
  let := HasDerivedCategory.standard D
  let F := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let G := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let L := DerivedCategory.Qh (C := C)
  let M := DerivedCategory.Qh (C := D)
  let R := F.rightDerivedFunctor
  let U := (CochainComplex.singleFunctor C 0).obj
    (SheafOfModules.unit (moduleRings X.toRingedSpace))
  let V := (CochainComplex.singleFunctor D 0).obj (ModuleCat.of A A)
  let P := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj U
  let B := (HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj V
  have hV (n : ℤ) : Projective (V.X n) := by
    by_cases hn : n = 0
    · subst n
      change Projective (ModuleCat.of A A)
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
        0 (ModuleCat.of A A) n hn).projective
  let _ := hV
  have : V.IsKProjective := CochainComplex.isKProjective_of_projective V 0
  obtain ⟨a, ha⟩ := structureSheaf_homotopy_globalSections X.toRingedSpace
  let S := (DerivedCategory.singleFunctor C 0).obj
    (SheafOfModules.unit (moduleRings X.toRingedSpace))
  let A₀ := (DerivedCategory.singleFunctor D 0).obj (ModuleCat.of A A)
  let s : S ≅ L.obj P := (DerivedCategory.quotientCompQhIso C).symm.app U
  let t : A₀ ≅ M.obj B := (DerivedCategory.quotientCompQhIso D).symm.app V
  let T (J : HomotopyCategory C (ComplexShape.up ℤ)) : Prop :=
    ∃ I : CochainComplex C ℤ, I.IsKInjective ∧
      J = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I
  have rep (E : DerivedCategory C) : ∃ J, T J ∧ Nonempty (E ≅ L.obj J) := by
    obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective E
    exact ⟨_, ⟨I, hI, rfl⟩, ⟨i ≪≫ (DerivedCategory.quotientCompQhIso C).symm.app I⟩⟩
  have full (J J' : HomotopyCategory C (ComplexShape.up ℤ)) (hJ' : T J') :
      Function.Bijective (L.map : (J ⟶ J') → (L.obj J ⟶ L.obj J')) := by
    obtain ⟨I, hI, rfl⟩ := hJ'
    let _ := hI
    exact CochainComplex.IsKInjective.Qh_map_bijective J I
  have unitIso (J : HomotopyCategory C (ComplexShape.up ℤ)) (hJ : T J) :
      IsIso (F.rightDerivedFunctorUnit.app J) := by
    obtain ⟨I, hI, rfl⟩ := hJ
    let _ := hI
    infer_instance
  let q (J : HomotopyCategory C (ComplexShape.up ℤ)) := AddEquiv.ofBijective
    (M.mapAddHom (X := B) (Y := G.obj J))
    (CochainComplex.IsKProjective.Qh_map_bijective V (G.obj J))
  let c (J : HomotopyCategory C (ComplexShape.up ℤ)) (hJ : T J) :
      (M.obj B ⟶ M.obj (G.obj J)) ≃+ (A₀ ⟶ R.obj (L.obj J)) :=
    let _ := unitIso J hJ
    { toEquiv := Iso.homCongr t.symm (asIso (F.rightDerivedFunctorUnit.app J))
      map_add' := by intro f g; simp [Iso.homCongr] }
  let b (J : HomotopyCategory C (ComplexShape.up ℤ)) (hJ : T J) :=
    (a J).trans ((q J).trans (c J hJ))
  have nat (J J' : HomotopyCategory C (ComplexShape.up ℤ)) (hJ : T J) (hJ' : T J')
      (f : J ⟶ J') (g : P ⟶ J) :
      b J' hJ' (g ≫ f) = b J hJ g ≫ R.map (L.map f) := by
    change t.hom ≫ M.map (a J' (g ≫ f)) ≫ F.rightDerivedFunctorUnit.app J' =
      (t.hom ≫ M.map (a J g) ≫ F.rightDerivedFunctorUnit.app J) ≫ R.map (L.map f)
    rw [ha, M.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun z ↦ t.hom ≫ M.map (a J g) ≫ z)
      (F.rightDerivedFunctorUnit.naturality f)
  exact descendHomEquiv L R P A₀ S s T rep full b nat

end AlgebraicGeometry
