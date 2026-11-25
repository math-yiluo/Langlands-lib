/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import all WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import all WeilConjectures.AlgebraicGeometry.PerfectCommonAffineModels
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian

/-! # Supported local perfect models after open restriction

Source: Stacks Project, Tags 08CM and 09IM.
(blueprint: lem-sc-local-perfect-supported-stabilization).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance moduleToSheaf_additive (Y : Scheme.{u}) :
    (SheafOfModules.toSheaf.{u} (moduleRings Y.toRingedSpace)).Additive where
  map_add := by intros; rfl

-- Exact restriction comparisons involve several nested localized module categories.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Restrict local perfect models and their support, also after stabilization.
Source: Stacks Project, Tag 08CM and the stabilization in Tag 09IM.
(blueprint: lem-sc-local-perfect-supported-stabilization).

Proof: At x in W, intersect its given neighbourhood O with W. Restrict the bounded
complex K to this intersection and transport it through the equivalence between the
localized site and the open scheme. Restriction and this equivalence carry finite free
modules to finite free modules, preserve their retract equations, and preserve zero
terms. The exact restriction composition comparison therefore gives a strictly perfect
model for the restriction of R near x. Shift its local model by one; the new degree
bounds are a-1 and b-1, and the finite free retracts are merely reindexed. The split
biproduct triangle with first term F, middle term F plus F[1], and last term F[1]
is distinguished. Apply perfect two-out-of-three to obtain perfectness of the middle term.
Exactness identifies homology of the restriction with
restriction of homology. The stalk comparison identifies its stalk at x with the ambient
stalk at x.val, which is zero off T by hRT. Homology of a biproduct is the biproduct of
homologies, and homology of a shift is the shifted homology; both summands thus have zero
stalks off T. This proves both support clauses. The construction is pointwise and includes
empty W and empty support without any choice of a point. -/
theorem local_perfect_supported_stabilization (X : Scheme.{u}) (W : X.Opens)
    (T : Set X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ O : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    (R : schemeDerivedCategory X)
    (hR : ∀ x : X, x ∈ W → ∃ O : X.Opens, x ∈ O ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
        IsStrictlyPerfect X O K ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
            DerivedCategory.Q.obj K))
    (hRT : ∀ (i : ℤ) (x : X), x ∈ W → x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))) :
    let F := (schemeOpenRestriction X W).mapDerivedCategory.obj R
    IsPerfect W.toScheme F ∧
    (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F).val.presheaf x))) ∧
    IsPerfect W.toScheme (F ⊞ F⟦(1 : ℤ)⟧) ∧
    (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj
          (F ⊞ F⟦(1 : ℤ)⟧)).val.presheaf x))) := by
  classical
  -- Reuse the abelian structures and exactness instances in the derived comparisons.
  let : Abelian (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let : Abelian (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) := inferInstance
  let G := schemeOpenRestriction X W
  have : G.Additive := schemeOpenRestriction_additive X W
  have : PreservesFiniteLimits G := schemeOpenRestriction_preservesFiniteLimits X W
  have : PreservesFiniteColimits G := schemeOpenRestriction_preservesFiniteColimits X W
  let F := G.mapDerivedCategory.obj R
  have hF : IsPerfect W.toScheme F := by
    intro x
    obtain ⟨O, hxO, K, hK, ⟨eK⟩⟩ := hR x.val x.property
    let V := W.ι ⁻¹ᵁ O
    let O₀ := W.ι ''ᵁ V
    let : Abelian (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O₀)) :=
      inferInstance
    let : Abelian (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over V)) :=
      inferInstance
    have hO₀ : O₀ ≤ O := by
      rintro y ⟨z, hz, rfl⟩
      exact hz
    let K₀ := ((SheafOfModules.overMap
      (moduleRings X.toRingedSpace) (homOfLE hO₀)).mapHomologicalComplex (.up ℤ)).obj K
    have hK₀ : IsStrictlyPerfect X O₀ K₀ := restrict_strictlyPerfect X O O₀ hO₀ K hK
    obtain ⟨eK₀⟩ := restrict_model X O O₀ hO₀ R K eK
    let s := W.ι.isoImage V
    let EV := Modules.overEquiv V
    let EO := Modules.overEquiv O₀
    let ES := CategoryTheory.Equivalence.mk
      (Modules.restrictFunctor s.inv) (Modules.restrictFunctor s.hom)
      ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
        Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId).symm
      ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
        Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId)
    let A := (EV.trans ES).trans EO.symm
    -- Inferring these repeatedly unfolds all three constituent equivalences.
    have : A.functor.Additive := inferInstance
    have : A.inverse.Additive := inferInstance
    have : PreservesFiniteLimits A.functor := inferInstance
    have : PreservesFiniteColimits A.functor := inferInstance
    have : PreservesFiniteLimits A.inverse := inferInstance
    have : PreservesFiniteColimits A.inverse := inferInstance
    let K' := (A.inverse.mapHomologicalComplex (.up ℤ)).obj K₀
    have unitIso : A.functor.obj
        (SheafOfModules.unit ((moduleRings W.toScheme.toRingedSpace).over V)) ≅
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over O₀) :=
      EO.inverse.mapIso ((Modules.restrictFunctor s.inv).mapIso
        (V.sheafOfModulesEquivOverUnit (moduleRings W.toScheme.toRingedSpace)) ≪≫
        Modules.restrictUnitIso s.inv) ≪≫
          O₀.sheafOfModulesEquivOverInverseUnit (moduleRings X.toRingedSpace)
    have unitIso' : A.inverse.obj
        (SheafOfModules.unit ((moduleRings X.toRingedSpace).over O₀)) ≅
        SheafOfModules.unit ((moduleRings W.toScheme.toRingedSpace).over V) :=
      A.inverse.mapIso unitIso.symm ≪≫ A.unitIso.symm.app _
    have hK' : IsStrictlyPerfect W.toScheme V K' := by
      obtain ⟨⟨a, b, hb⟩, hp⟩ := hK₀
      constructor
      · exact ⟨a, b, fun n hn ↦ A.inverse.map_isZero (hb n hn)⟩
      · intro n
        obtain ⟨m, j, p, hjp⟩ := hp n
        let c : A.inverse.obj (SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over O₀) (ULift.{u} (Fin m))) ≅
            SheafOfModules.free
              (R := (moduleRings W.toScheme.toRingedSpace).over V) (ULift.{u} (Fin m)) :=
          (SheafOfModules.mapFreeIso A.inverse (ULift.{u} (Fin m)) unitIso'.symm).symm
        refine ⟨m, A.inverse.map j ≫ c.hom, c.inv ≫ A.inverse.map p, ?_⟩
        change (A.inverse.map j ≫ c.hom) ≫ c.inv ≫ A.inverse.map p =
          𝟙 (A.inverse.obj (K₀.X n))
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hjp]
        exact A.inverse.map_id _
    refine ⟨V, hxO, K', hK', ?_⟩
    let H := SheafOfModules.overFunctor.{u} (moduleRings W.toScheme.toRingedSpace) V
    let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) O₀
    have : H.Additive := inferInstance
    have : PreservesFiniteLimits H := inferInstance
    have : PreservesFiniteColimits H := inferInstance
    have : L.Additive := inferInstance
    have : PreservesFiniteLimits L := inferInstance
    have : PreservesFiniteColimits L := inferInstance
    have fac : s.inv ≫ V.ι ≫ W.ι = O₀.ι := by
      rw [← Category.assoc, W.isoImage_ι_inv_ι V]
      exact X.homOfLE_ι _
    let c₀ : (G ⋙ H) ⋙ (EV.functor ⋙ ES.functor) ≅ L ⋙ EO.functor :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft G ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Modules.overFunctorEquiv V) ES.functor) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerRight (Modules.overFunctorEquiv W) _) _ ≪≫
        Functor.isoWhiskerRight (Modules.restrictFunctorComp V.ι W.ι).symm ES.functor ≪≫
        (Modules.restrictFunctorComp s.inv (V.ι ≫ W.ι)).symm ≪≫
        Modules.restrictFunctorCongr fac ≪≫ (Modules.overFunctorEquiv O₀).symm
    let c : (G ⋙ H) ⋙ A.functor ≅ L :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c₀ EO.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L EO.unitIso.symm ≪≫
        Functor.rightUnitor L
    let cD : A.functor.mapDerivedCategory.obj
        (H.mapDerivedCategory.obj (G.mapDerivedCategory.obj R)) ≅ L.mapDerivedCategory.obj R :=
      A.functor.mapDerivedCategory.mapIso ((Functor.mapDerivedCategoryCompIso G H).app R) ≪≫
        (Functor.mapDerivedCategoryCompIso (G ⋙ H) A.functor).app R ≪≫
        (Functor.mapDerivedCategoryNatIso c).app R
    let ed := A.mapDerivedCategory
    exact ⟨ed.unitIso.app _ ≪≫ ed.inverse.mapIso (cD ≪≫ eK₀) ≪≫
      A.inverse.mapDerivedCategoryFactors.app K₀⟩
  have hFT : ∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F).val.presheaf x)) := by
    intro i x hx
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i
    let HW := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i
    let d : HW.obj F ≅ (Modules.restrictFunctor W.ι).obj (H.obj R) :=
      ((G.mapDerivedCategoryHomologyFunctorIso i).app R).symm ≪≫
        (Modules.overFunctorEquiv W).app (H.obj R)
    let st := SheafOfModules.toSheaf.{u} (moduleRings W.toScheme.toRingedSpace) ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} W.toScheme.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let dS := st.mapIso d ≪≫ (Modules.restrictStalkNatIso W.ι x).app (H.obj R)
    have hS : IsZero (TopCat.Presheaf.stalk (H.obj R).val.presheaf x.val) :=
      AddCommGrpCat.isZero_iff_subsingleton.mpr (hRT i x.val x.property hx)
    exact AddCommGrpCat.subsingleton_of_isZero (hS.of_iso dS)
  have hstab : IsPerfect W.toScheme (F ⊞ F⟦(1 : ℤ)⟧) :=
    (isPerfect_two_out_of_three W.toScheme (binaryBiproductTriangle F (F⟦(1 : ℤ)⟧))
      (binaryBiproductTriangle_distinguished F (F⟦(1 : ℤ)⟧))).2.2 hF
        (perfect_shift W.toScheme hF (1 : ℤ))
  let P := supportedProperty W.toScheme (Subtype.val ⁻¹' T)
  let : P.IsStableUnderShift ℤ :=
    supported_qcoh_stableShift W.toScheme (Subtype.val ⁻¹' T)
  have hPF : P F := ⟨schemeDerivedQCohProperty_of_isPerfect W.toScheme F hF, hFT⟩
  have hPS := P.le_shift (1 : ℤ) F hPF
  refine ⟨hF, hFT, hstab, ?_⟩
  intro i x hx
  let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i ⋙
    SheafOfModules.toSheaf.{u} (moduleRings W.toScheme.toRingedSpace) ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{u} W.toScheme.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive := inferInstance
  have : (TopCat.Sheaf.forget AddCommGrpCat.{u} W.toScheme.toTopCat).Additive := inferInstance
  have : H.Additive := by dsimp [H]; infer_instance
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have hZ : IsZero (H.obj F ⊞ H.obj (F⟦(1 : ℤ)⟧)) :=
    (biprod_isZero_iff _ _).mpr
      ⟨AddCommGrpCat.isZero_iff_subsingleton.mpr (hFT i x hx),
        AddCommGrpCat.isZero_iff_subsingleton.mpr (hPS.2 i x hx)⟩
  exact AddCommGrpCat.subsingleton_of_isZero (hZ.of_iso (H.mapBiprod F (F⟦(1 : ℤ)⟧)))

end AlgebraicGeometry.Scheme
