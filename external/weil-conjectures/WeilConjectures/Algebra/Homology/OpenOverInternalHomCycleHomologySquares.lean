/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology

/-! # Internal Hom transport squares for cycles and homology

Source: Stacks Project, Tags 0A8X and 08DL.
(blueprint: new-t4-open-over-internal-hom-cycle-homology-squares). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

local instance (priority := 2000) openOverInternalHomCycleHomologySquaresCategory
    (X : Scheme.{u}) : Category X.Modules :=
  SheafOfModules.instCategory (R := X.ringCatSheaf)
local instance (priority := 2000) openOverInternalHomCycleHomologySquaresPreadditive
    (X : Scheme.{u}) : Preadditive X.Modules :=
  SheafOfModules.instPreadditive X.ringCatSheaf
noncomputable local instance (priority := 2000) openOverInternalHomCycleHomologySquaresAbelian
    (X : Scheme.{u}) : Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf

attribute [local irreducible] Scheme.Modules.restrictFunctor SheafOfModules.overFunctor
attribute [local irreducible] homComplexFunctor

/-- Postcompose a commuting square without rewriting its object expressions. -/
private theorem openOver_comp_naturality
    {C : Type*} [Category C] {A B D E G : C}
    {f : A ⟶ B} {g : B ⟶ E} {h : A ⟶ D} {i : D ⟶ E}
    (sq : f ≫ g = h ≫ i) (j : E ⟶ G) : f ≫ g ≫ j = h ≫ i ≫ j := by
  rw [← Category.assoc, sq, Category.assoc]

/- Transport of source and target cycles and homology through internal Hom.
Source: Stacks Project, Tag 08DL; step 2 of the parent restriction-diagram plan.
(blueprint: new-t4-open-over-internal-hom-cycle-homology-squares).

Proof: Restriction is exact by the localization finite-limit and finite-colimit
 comparisons, the open-site equivalence and overFunctorEquiv. For L=T,J, take
 z_L:F(Z(L)) ≅ Z(F(L)) and d_L:F(H(L)) ≅ H(F(L)), the inverses of the
 ShortComplex mapCyclesIso and mapHomologyIso comparisons. They commute with cycle
 inclusions and homology quotients by their kernel and cokernel universal properties.
 Compose e with Hom(z_T inverse,z_J) to define s, with Hom(z_T inverse,identity)
 to define t, with Hom(z_T inverse,d_J) to define v, and with Hom(d_T inverse,d_J)
 to define b. Apply the naturality equation he to (T.iCycles,identity),
 (identity,J.iCycles), (identity,J.homologyπ), and (T.homologyπ,identity).
 Cancel the cycle and homology isomorphisms using their inclusion and quotient
 squares to obtain the four equations. This uses neither the Hom complex nor its
 products or differential. No finiteness or nonempty-open assumption is needed;
 zero and identity maps satisfy the same naturality equations. -/
/-- (blueprint: new-t4-open-over-internal-hom-cycle-homology-squares) -/
theorem openOver_internalHom_cycle_homology_squares (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens)
    (e : ∀ M N : X.Modules,
      (Scheme.Modules.restrictFunctor V.ι ⋙
        SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj
          (SheafOfModules.homObj (R := X.sheaf) M N) ≅
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        ((Scheme.Modules.restrictFunctor V.ι ⋙
          SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj M)
        ((Scheme.Modules.restrictFunctor V.ι ⋙
          SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj N))
    (he : ∀ (M M' N N' : X.Modules) (f : M' ⟶ M) (g : N ⟶ N'),
      (Scheme.Modules.restrictFunctor V.ι ⋙
        SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map
          (SheafOfModules.homObjMap (R := X.sheaf) f g) ≫ (e M' N').hom =
        (e M N).hom ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
          ((Scheme.Modules.restrictFunctor V.ι ⋙
            SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map f)
          ((Scheme.Modules.restrictFunctor V.ι ⋙
            SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map g))
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    let F := Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    ∃ b : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.homology (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
      ∃ s : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.cycles 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.cycles 0),
      ∃ t : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.X 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.X 0),
      ∃ v : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.homology 0),
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 _)) ≫
            t.hom = (e (T.X (-n)) (J.X 0)).hom ≫
          SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
            (A.iCycles (-n)) (𝟙 _) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.iCycles 0)) ≫ t.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.iCycles 0) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.homologyπ 0)) ≫ v.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.homologyπ 0) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (T.homologyπ (-n)) (𝟙 _)) ≫
            v.hom = b.hom ≫ SheafOfModules.homObjMap
              (R := V.toScheme.sheaf.over W) (A.homologyπ (-n)) (𝟙 _) := by
  classical
  let : Category (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) :=
    SheafOfModules.instCategory
  let : Preadditive (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) :=
    SheafOfModules.instPreadditive _
  let : Abelian (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) :=
    SheafOfModules.instAbelian _
  let O := SheafOfModules.overFunctor.{u} X.ringCatSheaf V
  let E := (Scheme.Modules.overEquiv V).functor
  let R := Scheme.Modules.restrictFunctor V.ι
  let B := SheafOfModules.overFunctor.{u} V.toScheme.ringCatSheaf W
  let F := R ⋙ B
  let : PreservesFiniteLimits O := moduleOverFunctor_limits X.toRingedSpace V
  let : PreservesFiniteColimits O := moduleOverFunctor_colimits X.toRingedSpace V
  let : PreservesFiniteLimits (O ⋙ E) := comp_preservesFiniteLimits O E
  let : PreservesFiniteColimits (O ⋙ E) := comp_preservesFiniteColimits O E
  let : PreservesFiniteLimits R :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.overFunctorEquiv V)
  let : PreservesFiniteColimits R :=
    preservesFiniteColimits_of_natIso (Scheme.Modules.overFunctorEquiv V)
  let : PreservesFiniteLimits B := moduleOverFunctor_limits V.toScheme.toRingedSpace W
  let : PreservesFiniteColimits B := moduleOverFunctor_colimits V.toScheme.toRingedSpace W
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits R B
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits R B
  let : F.PreservesZeroMorphisms := moduleOpenOver_preservesZeroMorphisms X V W
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  have : F.PreservesHomology := inferInstance
  let A := (moduleOpenOverComplexFunctor X V W).obj T
  let K := (moduleOpenOverComplexFunctor X V W).obj J
  let z (L : CochainComplex X.Modules ℤ) (i : ℤ) :
      F.obj (L.cycles i) ≅ ((moduleOpenOverComplexFunctor X V W).obj L).cycles i :=
    ((L.sc i).mapCyclesIso F).symm
  let d (L : CochainComplex X.Modules ℤ) (i : ℤ) :
      F.obj (L.homology i) ≅ ((moduleOpenOverComplexFunctor X V W).obj L).homology i :=
    ((L.sc i).mapHomologyIso F).symm
  have zi (L : CochainComplex X.Modules ℤ) (i : ℤ) :
      (z L i).inv ≫ F.map (L.iCycles i) =
        ((moduleOpenOverComplexFunctor X V W).obj L).iCycles i :=
    (L.sc i).mapCyclesIso_hom_iCycles F
  have zp (L : CochainComplex X.Modules ℤ) (i : ℤ) :
      (z L i).inv ≫ F.map (L.homologyπ i) ≫ (d L i).hom =
        ((moduleOpenOverComplexFunctor X V W).obj L).homologyπ i :=
    (Category.assoc _ _ _).symm.trans
      (((L.sc i).mapHomologyIso F).comp_inv_eq.mpr
        ((L.sc i).homologyπ_mapHomologyIso_hom F).symm)
  let H {M M' N N' : SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)}
      (a : M ≅ M') (b : N ≅ N') :
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W) M N ≅
        SheafOfModules.homObj (R := V.toScheme.sheaf.over W) M' N' :=
    { hom := SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) a.inv b.hom
      inv := SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) a.hom b.inv
      hom_inv_id := by
        simp only [SheafOfModules.homObjMap_comp_homObjMap,
          Iso.hom_inv_id, SheafOfModules.homObjMap_id]
      inv_hom_id := by
        simp only [SheafOfModules.homObjMap_comp_homObjMap,
          Iso.inv_hom_id, SheafOfModules.homObjMap_id] }
  have hc {M M' M'' N N' N'' : SheafOfModules.{u}
      (V.toScheme.ringCatSheaf.over W)} (f : M' ⟶ M) (f' : M'' ⟶ M')
      (g : N ⟶ N') (g' : N' ⟶ N'') :
      SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) f g ≫
          SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) f' g' =
        SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (f' ≫ f) (g ≫ g') :=
    SheafOfModules.homObjMap_comp_homObjMap (R := V.toScheme.sheaf.over W) f f' g g'
  let b := e (T.homology (-n)) (J.homology 0) ≪≫ H (d T (-n)) (d J 0)
  let s := e (T.cycles (-n)) (J.cycles 0) ≪≫ H (z T (-n)) (z J 0)
  let t := e (T.cycles (-n)) (J.X 0) ≪≫ H (z T (-n)) (Iso.refl (K.X 0))
  let v := e (T.cycles (-n)) (J.homology 0) ≪≫ H (z T (-n)) (d J 0)
  refine ⟨b, s, t, v, ?_, ?_, ?_, ?_⟩
  · dsimp only [t, H, Iso.trans_hom, Iso.refl_hom]
    refine (openOver_comp_naturality
      (he _ _ _ _ (T.iCycles (-n)) (𝟙 (J.X 0))) _).trans ?_
    simp only [hc,
      Functor.map_id, Category.id_comp]
    congr 2
    exact zi T (-n)
  · dsimp only [t, s, H, Iso.trans_hom, Iso.refl_hom]
    refine (openOver_comp_naturality
      (he _ _ _ _ (𝟙 (T.cycles (-n))) (J.iCycles 0)) _).trans ?_
    simp only [Category.assoc, hc,
      Functor.map_id, Category.id_comp, Category.comp_id]
    congr 2
    apply (cancel_epi (z J 0).inv).1
    simp only [Iso.inv_hom_id_assoc]
    erw [Category.comp_id]
    exact zi J 0
  · dsimp only [v, s, H, Iso.trans_hom]
    refine (openOver_comp_naturality
      (he _ _ _ _ (𝟙 (T.cycles (-n))) (J.homologyπ 0)) _).trans ?_
    simp only [Category.assoc, hc,
      Functor.map_id, Category.id_comp, Category.comp_id]
    congr 2
    apply (cancel_epi (z J 0).inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using zp J 0
  · dsimp only [v, b, H, Iso.trans_hom]
    refine (openOver_comp_naturality
      (he _ _ _ _ (T.homologyπ (-n)) (𝟙 (J.homology 0))) _).trans ?_
    simp only [Category.assoc, hc,
      Functor.map_id, Category.id_comp, Category.comp_id]
    congr 2
    apply (cancel_mono (d T (-n)).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using zp T (-n)

end CategoryTheory
