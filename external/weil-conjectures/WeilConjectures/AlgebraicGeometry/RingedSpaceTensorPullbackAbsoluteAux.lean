/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.InverseImageTensorPullbackComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

@[expose] public section

universe u wX wY
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.RingedSpace

set_option synthInstance.maxSize 256 in
private theorem inverseImage_isKFlat
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hK : K.IsKFlatTensor) :
    CochainComplex.IsKFlatTensor
      (((TopCat.Sheaf.inverseImageModuleFunctor f R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨e⟩ := TopCat.Sheaf.exists_inverseImage_tensorPullback_iso f R K
  have hk := CochainComplex.isKFlat_pullback f
    (TopCat.Sheaf.inverseImageRing f R) R
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (TopologicalSpace.Opens.map f) CommRingCat.{u} _ _).unit.app R) K hK
  let := SheafOfModules.monoidalCategory (TopCat.Sheaf.inverseImageRing f R)
  intro F hF i
  exact (hk F hF i).of_iso
    (HomologicalComplex₂.total.mapIso
      ((((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj F).mapIso e) (.up ℤ))

private theorem exists_leftDerived_of_resolving
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    [W.HasTwoOutOfThreeProperty] (Q : C ⥤ D) [Q.IsLocalization W]
    (F : C ⥤ E) (S : Set C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), X' ∈ S ∧ W s)
    (hinv : ∀ (X X' : C) (s : X ⟶ X'),
      X ∈ S → X' ∈ S → W s → IsIso (F.map s)) :
    ∃ (LF : D ⥤ E) (ε : Q ⋙ LF ⟶ F), LF.IsLeftDerivedFunctor ε W ∧
      ∀ X : C, X ∈ S → IsIso (ε.app X) := by
  classical
  have hwitness := Functor.resolvingClass_essentialConstancy W F S hres hinv
  have hpw : F.HasPointwiseLeftDerivedFunctor W := by
    intro X
    obtain ⟨Y, u, hc, hr, _⟩ := hwitness X
    have hb := leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
    exact (F.hasPointwiseLeftDerivedFunctorAt_iff Q W X).2 hb.1
  let : F.HasPointwiseLeftDerivedFunctor W := hpw
  let LF := F.totalLeftDerived Q W
  let ε := F.totalLeftDerivedCounit Q W
  refine ⟨LF, ε, inferInstance, ?_⟩
  intro X hX
  obtain ⟨Y, u, hc, hr, hu⟩ := hwitness X
  obtain ⟨_, π, ⟨hπ⟩, _, hidentity⟩ :=
    leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
  let hcanonical :=
    Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF ε W (Q.obj X)
  let e := hcanonical.conePointUniqueUpToIso hπ
  have hid : W (𝟙 X) := W.id_mem X
  have : IsIso (u.app (⟨Over.mk (𝟙 X), hid⟩ : W.Over ⊤ X)) := hu hid hX
  have : IsIso (π.app (StructuredArrow.mk (𝟙 (Q.obj X)))) := by
    rw [hidentity hid]
    infer_instance
  have he := hcanonical.conePointUniqueUpToIso_hom_comp hπ
    (StructuredArrow.mk (𝟙 (Q.obj X)))
  have he' : e.hom ≫ π.app (StructuredArrow.mk (𝟙 (Q.obj X))) = ε.app X := by
    simpa [Functor.RightExtension.coneAt] using he
  rw [← he']
  infer_instance

private theorem leftDerived_absolute_of_resolving
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {B : Type*} [Category* B]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    [W.HasTwoOutOfThreeProperty] (Q : C ⥤ D) [Q.IsLocalization W]
    (F : C ⥤ E) (S : Set C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), X' ∈ S ∧ W s)
    (LF : D ⥤ E) (ε : Q ⋙ LF ⟶ F)
    (hε : ∀ X : C, X ∈ S → IsIso (ε.app X)) (H : E ⥤ B) :
    (LF ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H) W := by
  have hinv : ∀ (X X' : C) (s : X ⟶ X'),
      X ∈ S → X' ∈ S → W s → IsIso ((F ⋙ H).map s) := by
    intro X X' s hX hX' hs
    have := hε X hX
    have := hε X' hX'
    have := Localization.inverts Q W s hs
    have heq : F.map s = inv (ε.app X) ≫ LF.map (Q.map s) ≫ ε.app X' := by
      apply (cancel_epi (ε.app X)).1
      simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      exact (ε.naturality s).symm
    dsimp only [Functor.comp_map]
    rw [heq]
    infer_instance
  obtain ⟨R, α, hR, hα⟩ := exists_leftDerived_of_resolving W Q (F ⋙ H) S hres hinv
  let := hR
  let β := (Functor.associator Q LF H).inv ≫ Functor.whiskerRight ε H
  let φ := R.leftDerivedLift α W (LF ⋙ H) β
  have hφS (X : C) (hX : X ∈ S) : IsIso (φ.app (Q.obj X)) := by
    have := hε X hX
    have := hα X hX
    have hfac : φ.app (Q.obj X) ≫ α.app X = β.app X :=
      R.leftDerived_fac_app α W (LF ⋙ H) β X
    have : IsIso (β.app X) := by dsimp [β]; infer_instance
    have : IsIso (φ.app (Q.obj X) ≫ α.app X) := by rw [hfac]; infer_instance
    exact IsIso.of_isIso_comp_right _ (α.app X)
  have hφQ (X : C) : IsIso (φ.app (Q.obj X)) := by
    obtain ⟨X', s, hX', hs⟩ := hres X
    have := hφS X' hX'
    have := Localization.inverts Q W s hs
    have heq : φ.app (Q.obj X) =
        inv ((LF ⋙ H).map (Q.map s)) ≫ φ.app (Q.obj X') ≫ R.map (Q.map s) := by
      rw [← φ.naturality (Q.map s)]
      simp
    rw [heq]
    infer_instance
  have := Localization.essSurj Q W
  have hφ (Z : D) : IsIso (φ.app Z) := by
    have := hφQ (Q.objPreimage Z)
    have heq : φ.app Z =
        inv ((LF ⋙ H).map (Q.objObjPreimageIso Z).hom) ≫
          φ.app (Q.obj (Q.objPreimage Z)) ≫ R.map (Q.objObjPreimageIso Z).hom := by
      rw [← φ.naturality (Q.objObjPreimageIso Z).hom]
      simp
    rw [heq]
    infer_instance
  have : IsIso φ := NatIso.isIso_of_isIso_app φ
  exact (R.isLeftDerivedFunctor_iff_isIso_leftDerivedLift α W (LF ⋙ H) β).2 this

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The K-flat resolving-class construction supplies the derived comparison for the
concrete tensor pullback.  The proof follows Tags 06YJ, 079W and 06XN: resolve by
K-flat complexes, use preservation of quasi-isomorphisms under inverse image and
change of rings, and apply `leftDerived_from_resolvingClass` to the resulting
functor. (blueprint: q3-ringed-space-tensor-pullback-left-derived)

Proof: choose a K-flat resolution of every complex. Inverse image preserves these
resolutions, and derived change of rings preserves quasi-isomorphisms between the
resulting K-flat complexes. Applying the resolving-class construction to the concrete
tensor pullback gives the displayed derived functor and its K-flat comparison. -/
theorem exists_tensorPullback_leftDerived
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ)) ∧
      (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
        K.IsKFlatTensor → IsIso
          (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := by
  let I := TopCat.Sheaf.inverseImageModuleFunctor g.hom.base Y.sheaf
  let φ := CochainComplex.tensorPullbackRingMap
    g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩
  let E₀ : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing g.hom.base Y.sheaf)) ⥤
      PresheafOfModules.{u} (moduleRings X).obj :=
    { obj := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
      map := fun a ↦
        { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
          naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u, u} φ _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro U
        simp
        rfl
      map_comp := by
        intro M N P a b
        apply PresheafOfModules.hom_ext
        intro U
        simp }
  let E := E₀ ⋙ PresheafOfModules.sheafification (𝟙 (moduleRings X).obj)
  have hscalar (U) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification (𝟙 (moduleRings X).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (moduleRings X).obj)).left_adjoint_additive
  have hE₀ : E₀.Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro U
    simpa only [E₀, SheafOfModules.add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (φ.hom.app U).hom).map_add (f := a.val.app U) (g := b.val.app U)
  have hEa : E.Additive := by infer_instance
  have hE (M) : E.obj M = SheafOfModules.changeOfRings.{u, u, u} φ M := rfl
  have hEmap {M N} (a : M ⟶ N) : E.map a =
      eqToHom (hE M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u} φ M a ≫
        eqToHom (hE N).symm := by simp [E, E₀, SheafOfModules.changeOfRingsHom]
  have hobj (M) : (I ⋙ E).obj M = P.obj M := (hE (I.obj M)).trans (h M).symm
  let e : I ⋙ E ≅ P :=
    NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) (by
      intro M N a
      dsimp
      rw [hEmap, hm]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      dsimp [hobj, I, TopCat.Sheaf.inverseImageModuleFunctor])
  have hinv : ∀ {K K' : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ}
      (a : K ⟶ K'), K.IsKFlatTensor → K'.IsKFlatTensor → QuasiIso a →
        QuasiIso ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
    intro K K' a hK hK' ha
    have : QuasiIso a := ha
    have hq := SheafOfModules.changeOfRings_kFlat_quasiIso φ E hE hEmap
      ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
      (inverseImage_isKFlat _ _ K hK) (inverseImage_isKFlat _ _ K' hK') inferInstance
    let ec := Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (ec.app K) (ec.app K') (ec.hom.naturality a).symm)).mp hq
  let F := P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let S : Set (HomotopyCategory (SheafOfModules.{u} (moduleRings Y))
      (ComplexShape.up ℤ)) :=
    { Z | ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
        K.IsKFlatTensor ∧ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K = Z }
  have hres : ∀ Z : HomotopyCategory (SheafOfModules.{u} (moduleRings Y))
      (ComplexShape.up ℤ), ∃ (Z' : HomotopyCategory (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ)) (s : Z' ⟶ Z),
        Z' ∈ S ∧ HomotopyCategory.quasiIso _ _ s := by
    intro Z
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    obtain ⟨K', s, hK', _, hs, _⟩ := CochainComplex.exists_isKFlatResolution K
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨K', hK', rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinvS : ∀ Z Z' : HomotopyCategory (SheafOfModules.{u} (moduleRings Y))
      (ComplexShape.up ℤ), ∀ s : Z ⟶ Z', Z ∈ S → Z' ∈ S →
        HomotopyCategory.quasiIso _ _ s → IsIso (F.map s) := by
    intro Z Z' s hZ hZ' hs
    obtain ⟨K, hK, rfl⟩ := hZ
    obtain ⟨K', hK', rfl⟩ := hZ'
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hPa := hinv a hK hK' ha
    dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hPa
  obtain ⟨_, hright, _, _, htwo, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated (SheafOfModules.{u} (moduleRings Y))
  let := hright
  let := htwo
  obtain ⟨LF, ε, hLF, hε⟩ :=
    exists_leftDerived_of_resolving (HomotopyCategory.quasiIso _ _)
      DerivedCategory.Qh F S hres hinvS
  exact ⟨LF, ε, hLF, fun K hK ↦ hε _ ⟨K, hK, rfl⟩⟩

/-- Absoluteness of a K-flat derived comparison: the right Kan extension over the
cofinal K-flat resolution category is essentially constant, hence every postcomposition
functor preserves its comparison.  This is the absolute-resolution argument of
Stacks Tags 06XN and 05SE. (blueprint: q3-ringed-space-tensor-pullback-absolute-postcomposition)

Proof: the K-flat resolution category is cofinal and all transition maps are sent to
isomorphisms by the comparison. Its right Kan extension is therefore essentially
constant, so the limiting cone is absolute and remains a left derived comparison after
postcomposition by any functor. -/
theorem leftDerived_tensorPullback_absolute
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive]
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
        (ComplexShape.up ℤ)))
    (hK : ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
      K.IsKFlatTensor → IsIso
        (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :
    ∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings Y)),
      (L ⋙ H).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H)
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ)) := by
  have := @hm
  have := hL
  let S : Set (HomotopyCategory (SheafOfModules.{u} (moduleRings Y))
      (ComplexShape.up ℤ)) :=
    { Z | ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
        K.IsKFlatTensor ∧ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K = Z }
  have hres : ∀ Z : HomotopyCategory (SheafOfModules.{u} (moduleRings Y))
      (ComplexShape.up ℤ), ∃ (Z' : HomotopyCategory (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ)) (s : Z' ⟶ Z),
        Z' ∈ S ∧ HomotopyCategory.quasiIso _ _ s := by
    intro Z
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    obtain ⟨K', s, hK', _, hs, _⟩ := CochainComplex.exists_isKFlatResolution K
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨K', hK', rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨_, hright, _, _, htwo, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated (SheafOfModules.{u} (moduleRings Y))
  let := hright
  let := htwo
  intro H
  apply leftDerived_absolute_of_resolving
    (HomotopyCategory.quasiIso _ _) DerivedCategory.Qh
    (P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) S hres L ε
    (fun Z hZ ↦ ?_) H
  obtain ⟨K, hk, rfl⟩ := hZ
  exact hK K hk

end AlgebraicGeometry.RingedSpace
