/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
/-! # Derived base change for proper flat morphisms

Source: Stacks Project, Tag 0A1D, specialized to the structure sheaf in degree zero.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Naturality of the canonical mate in its derived input, from the naturality
of the pullback composition comparisons and the adjunction Hom equivalence.
Source: Stacks Project, Tag 08HY, the canonical derived base-change construction. -/
private theorem baseChange_naturality
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : g' ≫ f = f' ≫ g)
    {E F : schemeDerivedCategory X} (s : E ⟶ F) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map s) ≫
        schemeDerivedBaseChangeMap f f' g g' h F =
      schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map s) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    set_option synthInstance.maxSize 2048 in
    open MonoidalCategory in by
  classical
  let ε : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings B.toRingedSpace)) ⋙
        derivedPullback k ⟶
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings A.toRingedSpace)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k
  have hε : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      (derivedPullback k).IsLeftDerivedFunctor (ε k)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (.up ℤ)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) k
  let c : ∀ {A B D : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ D),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let adj := Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f) (ε f) (hε f))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f') (ε f') (hε f'))
  let γ : (schemeDerivedDirectImage f ⋙ derivedPullback g) ⋙ derivedPullback f' ⟶
      derivedPullback g' :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (c f' g).hom ≫
      Functor.whiskerLeft _ (eqToHom (congrArg (fun k ↦ derivedPullback k) h.symm)) ≫
      Functor.whiskerLeft _ (c g' f).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight adj.counit (derivedPullback g') ≫
      (Functor.leftUnitor _).hom
  have hγ (K : schemeDerivedCategory X) :
      γ.app K = (c f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
        (c g' f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
        (derivedPullback g').map (adj.counit.app K) := by
    simp only [γ, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToHom_app, Category.id_comp]
    change _ ≫ _ ≫ _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  have hbc (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g g' h K = adj'.homEquiv _ _ (γ.app K) := by
    rw [hγ]
    rfl
  rw [hbc E, hbc F]
  exact adj'.homEquiv_naturality_left_square
    ((schemeDerivedDirectImage f ⋙ derivedPullback g).map s)
    (γ.app F) (γ.app E) ((derivedPullback g').map s) (γ.naturality s)

/-- Flat proper finite-presentation morphisms satisfy derived base change after arbitrary pullback.
Source: Stacks Project, Derived Categories of Schemes, Tag 0A1D (Lemma 36.26.4).
(blueprint: lem-sc-proper-flat-right-adjoint-basechange-hbeta)
Proof: Properness implies that f is quasi-compact and quasi-separated.
Apply relatively flat complex base change (Tag 0A1D) with G = O_X[0].
This complex is bounded above and quasi-coherent; flatness of f makes its only
nonzero term flat over Y. For each E, choose a K-flat representative and use
the tensor unit isomorphism to identify E ⊗^L O_X[0] with E.
Pullback of the structure sheaf is the structure sheaf, and O_X is intrinsically
flat, so the derived-to-ordinary pullback comparison for G is an isomorphism.
The theorem therefore says that the canonical map β_E, composed with the
unit identifications and this invertible comparison, is invertible.
Cancel these isomorphisms to obtain IsIso β_E. This holds for arbitrary,
including unbounded, quasi-coherent E. No right adjoint is used.
Equivalently, flatness gives Tor independence and Stacks Tag 08IB applies.
-/
theorem proper_flat_rightAdjoint_baseChange_hβ
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    ∀ E : schemeDerivedQCohCategory X,
        IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition E.obj) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    set_option synthInstance.maxSize 2048 in
    open MonoidalCategory in by
  classical
  intro E
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u, u} C
  have := schemeModule_hasFunctorialFlatResolution X
  let : Zero C := HasZeroObject.zero' C
  -- The structure sheaf in degree zero is bounded above and relatively flat.
  let G := (HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C)
  have hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (G.X i) := by
    exact ⟨0, fun i hi ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  have hqc : ∀ i : ℤ, (G.X i).IsQuasicoherent := by
    intro i
    dsimp [G, HomologicalComplex.single]
    split_ifs
    · exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    · let M := SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}
      have hz : IsZero M := (IsZero.iff_id_eq_zero M).mpr (by
        apply Sigma.hom_ext
        intro i
        exact i.elim)
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (hz.iso (isZero_zero C))
        (SheafOfModules.isQuasicoherent_free (R := X.ringCatSheaf) PEmpty.{u + 1})
  have hf : ∀ i : ℤ, Scheme.Modules.IsFlatOver (G.X i) f := by
    intro i
    dsimp [G, HomologicalComplex.single]
    split_ifs
    · have : SheafOfModules.IsInvertible.{u, u, u} (tensorUnit C) :=
        inferInstanceAs (SheafOfModules.IsInvertible.{u, u, u}
          (SheafOfModules.unit (moduleRings X.toRingedSpace)))
      exact Scheme.Modules.isFlatOver_of_isInvertible f _
    · intro V U e
      let F := SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation _ (Opposite.op U.1)
      have hz := Functor.map_isZero F (isZero_zero C)
      have : Subsingleton (F.obj (0 : C)) := ModuleCat.subsingleton_of_isZero hz
      let : Module Γ(Y, V.1) (F.obj (0 : C)) := Module.compHom _ (f.appLE V.1 U.1 e).hom
      change Module.Flat Γ(Y, V.1) (F.obj (0 : C))
      infer_instance
  -- Coordinates supply a K-flat representative and its invertible pullback counit.
  obtain ⟨c⟩ := SingleComplexBaseChange.nonempty_coordinates (pullback.fst f g)
    E.obj ((derivedPullback (pullback.fst f g)).obj E.obj) (𝟙 _)
  let P := c.P
  let H := CochainComplex.mapBifunctor P G
    (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))
  -- Both ordinary and derived tensor unit identifications are actual isomorphisms.
  let d : H ≅ P := MonoidalCategory.rightUnitor P
  let v : DerivedCategory.Q.obj G ≅ MonoidalCategory.tensorUnit (schemeDerivedCategory X) :=
    (DerivedCategory.singleFunctorIsoCompQ C 0).symm.app _ ≪≫
      DerivedCategory.singleFunctorObjUnitIso C
  let α : MonoidalCategory.tensorObj E.obj (DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj H :=
    MonoidalCategory.whiskerLeftIso E.obj v ≪≫ MonoidalCategory.rightUnitor E.obj ≪≫
      c.e.symm ≪≫ DerivedCategory.Q.mapIso d.symm
  have hi := relativelyFlat_derivedBaseChange_complex f g E.obj E.property
    G hb hqc hf P c.isKFlat c.e α
  simp only [cast_eq] at hi
  -- Naturality transports counit invertibility from P to its tensor with the unit.
  have hc : IsIso ((SingleComplexBaseChange.counit (pullback.fst f g)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj H)) := by
    have := c.counit_isIso
    let t := (HomotopyCategory.quotient C (.up ℤ)).mapIso d
    have hn := (SingleComplexBaseChange.counit (pullback.fst f g)).naturality t.hom
    have hh : IsIso (((DerivedCategory.Qh ⋙ derivedPullback (pullback.fst f g)).map
        t.hom) ≫ (SingleComplexBaseChange.counit (pullback.fst f g)).app
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := by infer_instance
    rw [hn] at hh
    exact (isIso_comp_right_iff _ _).mp hh
  have : IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition (DerivedCategory.Q.obj H)) := by
    have := hc
    have := hi
    exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)
  -- Cancel the two outside factors, then transport beta along H ≅ E.
  let t := DerivedCategory.Q.mapIso d ≪≫ c.e
  have hn := baseChange_naturality f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition t.hom
  have hh : IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition (DerivedCategory.Q.obj H) ≫
        (schemeDerivedDirectImage (pullback.snd f g)).map
          ((derivedPullback (pullback.fst f g)).map t.hom)) := by infer_instance
  rw [← hn] at hh
  exact (isIso_comp_left_iff _ _).mp hh
end AlgebraicGeometry
