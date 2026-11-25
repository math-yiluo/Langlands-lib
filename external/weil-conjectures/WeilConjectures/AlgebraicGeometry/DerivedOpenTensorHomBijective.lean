/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.OpenExtensionCounitStalk
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedTensorStalkVanishing

/-! # Tensor stability of derived open test objects
Source: Stacks Project, Tags 00A7, 08BT and 06YB.
(blueprint: lem-sc-derived-open-tensor-hom-bijective).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048

private theorem hom_bijective_iff_counit
    {C D : Type*} [Category C] [Category D] {J : D ⥤ C} {R : C ⥤ D}
    (a : J ⊣ R) (B : C) :
    (∀ E : C, Function.Bijective (fun f : B ⟶ E ↦ R.map f)) ↔
      IsIso (a.counit.app B) := by
  have he (E : C) :
      (fun f : B ⟶ E ↦ R.map f) =
        (a.homEquiv (R.obj B) E) ∘ (fun f : B ⟶ E ↦ a.counit.app B ≫ f) := by
    funext f
    simp [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, a.right_triangle_components]
  rw [isIso_iff_coyoneda_map_bijective]
  apply forall_congr'
  intro E
  rw [he]
  exact (a.homEquiv (R.obj B) E).bijective.of_comp_iff' _

private theorem hom_bijective_natIso
    {C D : Type*} [Category C] [Category D] {R S : C ⥤ D}
    (e : R ≅ S) (B E : C) :
    Function.Bijective (fun f : B ⟶ E ↦ R.map f) ↔
      Function.Bijective (fun f : B ⟶ E ↦ S.map f) := by
  have he : (fun f : B ⟶ E ↦ S.map f) =
      (Iso.homCongr (e.app B) (e.app E)) ∘ (fun f : B ⟶ E ↦ R.map f) := by
    funext f
    dsimp [Iso.homCongr]
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [he]
  exact ((Iso.homCongr (e.app B) (e.app E)).bijective.of_comp_iff' _).symm

private theorem sheaf_counit_support
    (X : RingedSpace.{uX}) (U : TopologicalSpace.Opens X)
    (J : SheafOfModules.{uX} ((moduleRings X).over U) ⥤
      SheafOfModules.{uX} (moduleRings X))
    (a : J ⊣ SheafOfModules.overFunctor.{uX} (moduleRings X) U)
    (F : SheafOfModules.{uX} (moduleRings X)) :
    IsIso (a.counit.app F) ↔ ∀ x : X, x ∉ U →
      Subsingleton (↑(TopCat.Presheaf.stalk F.val.presheaf x)) := by
  classical
  let T (x : X) := SheafOfModules.toSheaf (moduleRings X) ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x
  have hs (x : X) := SheafOfModules.open_extension_counit_stalk X
    (moduleRings X) rfl U J a F x
  constructor
  · intro h x hx
    let := h
    have hz : IsZero ((T x).obj (J.obj
        ((SheafOfModules.overFunctor.{uX} (moduleRings X) U).obj F))) := (hs x).2 hx
    exact AddCommGrpCat.isZero_iff_subsingleton.mp
      (hz.of_iso (asIso ((T x).map (a.counit.app F))).symm)
  · intro h
    have ht (x : X) : IsIso ((T x).map (a.counit.app F)) := by
      by_cases hx : x ∈ U
      · exact (hs x).1 hx
      · have hz := (hs x).2 hx
        have hw : IsZero ((T x).obj F) :=
          AddCommGrpCat.isZero_iff_subsingleton.mpr (h x hx)
        rw [hz.eq_of_src ((T x).map (a.counit.app F)) 0]
        exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hz, hw⟩
    have (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x).map
        ((SheafOfModules.toSheaf (moduleRings X)).map (a.counit.app F)).hom) := ht x
    have h' : IsIso ((SheafOfModules.toSheaf (moduleRings X)).map
        (a.counit.app F)) := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (moduleRings X))

private theorem complex_counit_support
    (X : RingedSpace.{uX}) (U : TopologicalSpace.Opens X)
    (J : SheafOfModules.{uX} ((moduleRings X).over U) ⥤
      SheafOfModules.{uX} (moduleRings X))
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (a : J ⊣ SheafOfModules.overFunctor.{uX} (moduleRings X) U)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X)) ℤ) :
    QuasiIso ((a.mapHomologicalComplex (.up ℤ)).counit.app P) ↔
      ∀ x : X, x ∉ U → ∀ n : ℤ,
        Subsingleton (↑(TopCat.Presheaf.stalk (P.homology n).val.presheaf x)) := by
  have hn (n : ℤ) :
      QuasiIsoAt ((a.mapHomologicalComplex (.up ℤ)).counit.app P) n ↔
        IsIso (a.counit.app (P.homology n)) := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (ShortComplex.homologyMap ((P.sc n).mapNatTrans a.counit)) ↔ _
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [isIso_comp_left_iff, isIso_comp_right_iff]
    rfl
  rw [quasiIso_iff]
  simp only [hn, sheaf_counit_support X U J a]
  exact forall_comm.trans (forall_congr' (fun x ↦ forall_comm))

private theorem raw_derived_hom_support
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX}
      ((moduleRings X.toRingedSpace).over U))]
    (B : schemeDerivedCategory X) :
    (∀ E : schemeDerivedCategory X, Function.Bijective
      (fun f : B ⟶ E ↦ (SheafOfModules.overFunctor.{uX}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.map f)) ↔
      ∀ x : X, x ∉ U → ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj B).val.presheaf x)) := by
  classical
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U)
  let R := SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U
  let J := SheafOfModules.extensionByZeroPresheaf.{uX}
    (moduleRings X.toRingedSpace) U ⋙
      PresheafOfModules.sheafification.{uX} (𝟙 (moduleRings X.toRingedSpace).obj)
  obtain ⟨hRlim, hRcolim, hJlim, hJcolim, ha⟩ :=
    open_restriction_adjunction_exact X.toRingedSpace U
  have : PreservesFiniteLimits R := hRlim
  have : PreservesFiniteColimits R := hRcolim
  have : PreservesFiniteLimits J := hJlim
  have : PreservesFiniteColimits J := hJcolim
  let a := Classical.choice ha
  let ac := a.mapHomologicalComplex (.up ℤ)
  let Q := DerivedCategory.Q (C := C)
  let QO := DerivedCategory.Q (C := D)
  let : CatCommSq (J.mapHomologicalComplex (.up ℤ)) QO Q J.mapDerivedCategory :=
    ⟨J.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R.mapHomologicalComplex (.up ℤ)) Q QO R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  let ad := ac.localization QO (HomologicalComplex.quasiIso D (.up ℤ))
    Q (HomologicalComplex.quasiIso C (.up ℤ)) J.mapDerivedCategory R.mapDerivedCategory
  have hq (P : CochainComplex C ℤ) :
      IsIso (ad.counit.app (Q.obj P)) ↔ QuasiIso (ac.counit.app P) := by
    dsimp [ad]
    rw [Adjunction.localization_counit_app]
    simp only [isIso_comp_left_iff]
    exact DerivedCategory.isIso_Q_map_iff_quasiIso C (ac.counit.app P)
  let P := Q.objPreimage B
  let e := Q.objObjPreimageIso B
  rw [hom_bijective_iff_counit ad B, ← NatTrans.isIso_app_iff_of_iso ad.counit e,
    hq, complex_counit_support X.toRingedSpace U J a P]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  apply forall_congr'
  intro n
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x
  let eh : T.obj ((DerivedCategory.homologyFunctor C n).obj B) ≅
      T.obj (P.homology n) := T.mapIso
        ((DerivedCategory.homologyFunctor C n).mapIso e.symm ≪≫
          (DerivedCategory.homologyFunctorFactors C n).app P)
  change Subsingleton (↑(T.obj (P.homology n))) ↔
    Subsingleton (↑(T.obj ((DerivedCategory.homologyFunctor C n).obj B)))
  rw [← AddCommGrpCat.isZero_iff_subsingleton, ← AddCommGrpCat.isZero_iff_subsingleton]
  exact ⟨fun h ↦ h.of_iso eh, fun h ↦ h.of_iso eh.symm⟩

private theorem tensor_stalk_vanishing
    (X : Scheme.{uX})
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (B L : schemeDerivedCategory X) (x : X)
    (hB : ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj B).val.presheaf x))) :
    ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj
        (B ⊗ L)).val.presheaf x)) := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let Q := DerivedCategory.Q (C := C)
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := X.sheaf) (Q.objPreimage B)
  obtain ⟨J, g, hJ, _, hg, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := X.sheaf) (Q.objPreimage L)
  have : QuasiIso f := hf
  have : QuasiIso g := hg
  let eP : Q.obj P ≅ B := asIso (Q.map f) ≪≫ Q.objObjPreimageIso B
  let eJ : Q.obj J ≅ L := asIso (Q.map g) ≪≫ Q.objObjPreimageIso L
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj J) (fun _ ↦ hP)
  let eTensor : B ⊗ L ≅
      Q.obj (CochainComplex.mapBifunctor P J (curriedTensor C)) :=
    (tensorIso eP eJ).symm ≪≫ (e.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  have h := derived_tensor_stalk_vanishing X B P J eP hJ x hB
  intro n
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x
  have hz : IsZero (T.obj ((DerivedCategory.homologyFunctor C n).obj
      (Q.obj (CochainComplex.mapBifunctor P J (curriedTensor C))))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (h n)
  have hz' : IsZero (T.obj ((DerivedCategory.homologyFunctor C n).obj (B ⊗ L))) :=
    hz.of_iso (T.mapIso ((DerivedCategory.homologyFunctor C n).mapIso eTensor))
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hz'

/-- Tensoring an extension object preserves the restriction Hom bijection.
Source: Stacks Project, Tags 00A7, 08BT, 06YB and 06YH.
(blueprint: lem-sc-derived-open-tensor-hom-bijective).

Proof: Write J for exact extension by zero, transported through Modules.overEquiv,
and R for derived restriction. The unit of J ⊣ R is invertible. For any C, the
restricted counit R(J(R(C))) → R(C) is invertible by the triangle identity. Thus
precomposition with the counit J(R(B)) → B is a bijection on Hom(-,E): identify
Hom(J(R(B)),E) with Hom(R(B),R(E)) by adjunction and cancellation of the unit,
and use the assumed bijectivity of R.map on Hom(B,E). Yoneda then makes this
counit invertible. In particular B is an extension object, whose cohomology
stalks vanish outside U, by exactness and the exterior stalk computation.
Choose a complex P representing B and a K-flat resolution Q representing L.
The stalk vanishing theorem shows that Tot(P tensor Q) has zero cohomology
stalks outside U. The K-flat tensor comparison, using symmetry to place Q
first, identifies its derived image with B tensor L.
For any C with this vanishing, represent C by a complex and take the termwise
extension/restriction counit. Inside U its stalk maps are invertible. Outside U
its source stalk complex is zero and its target stalk complex is acyclic.
Hence the counit is a stalkwise quasi-isomorphism, and thus a quasi-isomorphism
of sheaf complexes. Its image J(R(C)) → C in the derived category is invertible.
Apply this to C = B tensor L. The adjunction and its invertible unit identify
restriction on Hom(J(R(C)),E) with a bijection. Precompose with the invertible
counit and cancel its invertible restriction to obtain precisely R.map on
Hom(C,E). No bound, flatness of L itself, or finiteness is assumed. -/
theorem derivedOpen_tensorHom_bijective
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (B : schemeDerivedCategory X) :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    (∀ E : schemeDerivedCategory X,
      Function.Bijective (fun f : B ⟶ E ↦ R.map f)) →
    ∀ L E : schemeDerivedCategory X,
      Function.Bijective (fun f : B ⊗ L ⟶ E ↦ R.map f) := by
  classical
  dsimp only
  let R₀ := SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U
  let eU := Modules.overEquiv U
  let H := Equivalence.functor
    (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace)) eU
  have he (A E : schemeDerivedCategory X) :
      Function.Bijective (fun f : A ⟶ E ↦ (R₀ ⋙ H).mapDerivedCategory.map f) ↔
        Function.Bijective (fun f : A ⟶ E ↦ R₀.mapDerivedCategory.map f) := by
    rw [← hom_bijective_natIso (Functor.mapDerivedCategoryCompIso R₀ H)]
    exact (Functor.FullyFaithful.ofFullyFaithful H.mapDerivedCategory).homEquiv.bijective
      |>.of_comp_iff' (fun f : A ⟶ E ↦ R₀.mapDerivedCategory.map f)
  intro hB L E
  have hB' := (raw_derived_hom_support X U B).mp (fun E ↦ (he B E).mp (hB E))
  have hBL := (raw_derived_hom_support X U (B ⊗ L)).mpr
    (fun x hx ↦ tensor_stalk_vanishing X B L x (hB' x hx))
  exact (he (B ⊗ L) E).mpr (hBL E)

end AlgebraicGeometry.Scheme
