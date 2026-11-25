/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.RelativeOpenGluing
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Supported gluing relative to an ambient scheme

Source: Stacks Project, Tag 08DG; Tag 08CM for local perfectness.
(blueprint: lem-sc-supported-relative-open-gluing).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable abbrev moduleRestriction {Z X : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f] :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) := Modules.restrictFunctor f

private instance restriction_additive {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsOpenImmersion f] : (moduleRestriction f).Additive := by
  change (Modules.restrictFunctor f).Additive
  infer_instance

private instance restriction_limits {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsOpenImmersion f] : PreservesFiniteLimits (moduleRestriction f) := by
  change PreservesFiniteLimits (Modules.restrictFunctor f)
  infer_instance

private instance restriction_colimits {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsOpenImmersion f] : PreservesFiniteColimits (moduleRestriction f) := by
  change PreservesFiniteColimits (Modules.restrictFunctor f)
  infer_instance

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_perfect_of_open_immersion
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ O : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ O : Z.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over O))]
    (R : schemeDerivedCategory X) (F : schemeDerivedCategory Z)
    (hF : IsPerfect Z F)
    (e : (moduleRestriction f).mapDerivedCategory.obj R ≅ F)
    (x : Z) :
    ∃ O : X.Opens, f x ∈ O ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
        IsStrictlyPerfect X O K ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
            DerivedCategory.Q.obj K) := by
  obtain ⟨V, hxV, K, hK, ⟨hmodel⟩⟩ := hF x
  let O := f ''ᵁ V
  let s := f.isoImage V
  let EV := Modules.overEquiv V
  let EO := Modules.overEquiv O
  let ES := CategoryTheory.Equivalence.mk
    (Modules.restrictFunctor s.inv) (Modules.restrictFunctor s.hom)
    ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
      Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId).symm
    ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
      Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId)
  let A := (EV.trans ES).trans EO.symm
  have : A.functor.Additive := inferInstance
  let K' := (A.functor.mapHomologicalComplex (.up ℤ)).obj K
  have unitIso : A.functor.obj
      (SheafOfModules.unit ((moduleRings Z.toRingedSpace).over V)) ≅
      SheafOfModules.unit ((moduleRings X.toRingedSpace).over O) :=
    EO.inverse.mapIso ((Modules.restrictFunctor s.inv).mapIso
      (V.sheafOfModulesEquivOverUnit (moduleRings Z.toRingedSpace)) ≪≫
      Modules.restrictUnitIso s.inv) ≪≫
        O.sheafOfModulesEquivOverInverseUnit (moduleRings X.toRingedSpace)
  have hK' : IsStrictlyPerfect X O K' := by
    obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
    constructor
    · exact ⟨a, b, fun n hn ↦ A.functor.map_isZero (hb n hn)⟩
    · intro n
      obtain ⟨m, i, p, hip⟩ := hp n
      let c : A.functor.obj (SheafOfModules.free
          (R := (moduleRings Z.toRingedSpace).over V) (ULift.{u} (Fin m))) ≅
          SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over O) (ULift.{u} (Fin m)) :=
        (asIso (sigmaComparison A.functor (fun _ : ULift.{u} (Fin m) ↦
          SheafOfModules.unit ((moduleRings Z.toRingedSpace).over V)))).symm ≪≫
          Sigma.mapIso (fun _ ↦ unitIso)
      refine ⟨m, A.functor.map i ≫ c.hom, c.inv ≫ A.functor.map p, ?_⟩
      change (A.functor.map i ≫ c.hom) ≫ c.inv ≫ A.functor.map p =
        𝟙 (A.functor.obj (K.X n))
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hip]
      exact A.functor.map_id _
  refine ⟨O, ?_, K', hK', ?_⟩
  · exact ⟨x, hxV, rfl⟩
  · let G := moduleRestriction f
    let H := SheafOfModules.overFunctor.{u} (moduleRings Z.toRingedSpace) V
    let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) O
    have fac : s.inv ≫ V.ι ≫ f = O.ι := f.isoImage_inv_ι V
    let c0 : (G ⋙ H) ⋙ (EV.functor ⋙ ES.functor) ≅ L ⋙ EO.functor :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft G ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Modules.overFunctorEquiv V) ES.functor) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Modules.restrictFunctorComp V.ι f).symm ES.functor ≪≫
        (Modules.restrictFunctorComp s.inv (V.ι ≫ f)).symm ≪≫
        Modules.restrictFunctorCongr fac ≪≫ (Modules.overFunctorEquiv O).symm
    let c : (G ⋙ H) ⋙ A.functor ≅ L :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c0 EO.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L EO.unitIso.symm ≪≫
        Functor.rightUnitor L
    exact ⟨(Functor.mapDerivedCategoryNatIso c).symm.app R ≪≫
      (Functor.mapDerivedCategoryCompIso (G ⋙ H) A.functor).symm.app R ≪≫
      A.functor.mapDerivedCategory.mapIso
        ((Functor.mapDerivedCategoryCompIso G H).symm.app R ≪≫
          H.mapDerivedCategory.mapIso e ≪≫ hmodel) ≪≫
      A.functor.mapDerivedCategoryFactors.app K⟩


set_option backward.isDefEq.respectTransparency false in
private noncomputable def overlapRestrictionIso (X : Scheme.{u})
    {U W : X.Opens} (i : W ⟶ U) :
    schemeOpenOverlapRestriction X i ≅ moduleRestriction (X.homOfLE (leOfHom i)) :=
  Functor.isoWhiskerLeft (Modules.overEquiv U).inverse
      (Modules.overMapCompOverEquiv i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Modules.overEquiv U).counitIso _ ≪≫
    Functor.leftUnitor _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalk_subsingleton_of_open_immersion
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (R : schemeDerivedCategory X) (F : schemeDerivedCategory Z)
    (e : (moduleRestriction f).mapDerivedCategory.obj R ≅ F)
    (i : ℤ) (x : Z)
    (h : Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) i).obj F).val.presheaf x))) :
    Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf (f x))) := by
  let H := Modules.toPresheaf Z ⋙ TopCat.Presheaf.stalkFunctor _ x
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R
  let t := H.mapIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) i).mapIso e.symm) ≪≫
    H.mapIso (((moduleRestriction f).mapDerivedCategoryHomologyFunctorIso i).symm.app R) ≪≫
      (Modules.restrictStalkNatIso f x).app M
  exact t.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp h

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Glue arbitrary supported perfect local objects and compatible maps on W union V.
Neither affineness nor a stabilization of either source is assumed.
Source: Stacks Project, Tags 08DG and 08CM, used in Tag 09IM.
(blueprint: lem-sc-supported-relative-open-gluing).

Proof: Set Y=W union V and pull W and V back to opens of Y. They cover Y and are
canonically isomorphic as open subschemes to W and V. Transport A and B through these
isomorphisms and the exact module over-equivalences. The corresponding equivalence on the
intersection transports c. The natural composition comparisons for restriction identify
the given compatibility equation with the hypothesis of derived_open_gluing on Y for
the target E restricted to Y. That theorem supplies F, its two restriction isomorphisms,
and a map alpha with the required equations. Transport those equations back to the
relative functors PW and PV; the composition comparison kW (respectively kV) identifies
iterated restriction of E with its direct restriction to W (respectively V).
For a point of Y choose W or V containing it. A strictly perfect neighbourhood model
of A or B, restricted and transported to the corresponding open of Y, is a model of F.
This gives IsPerfect Y F. Exact restriction identifies each homology stalk of F with
the corresponding stalk of A or B. Off T that stalk is zero by hAT or hBT, so F is
supported on T intersect Y. No compactness, closedness of T, or boundedness of E is used.
If a member of the cover is empty, choose the other at each point; if Y is empty,
the perfectness and support conclusions are vacuous. -/
theorem exists_supported_relative_open_gluing
    (X : Scheme.{u}) (W V : X.Opens) (T : Set X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [∀ O : (W ⊔ V).toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (W ⊔ V).toScheme.toRingedSpace).over O))]
    (A : schemeDerivedCategory W.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : IsPerfect W.toScheme A) (hB : IsPerfect V.toScheme B)
    (hAT : ∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj A).val.presheaf x)))
    (hBT : ∀ (i : ℤ) (x : V.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) i).obj B).val.presheaf x))) :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    ∀ (c : SW.obj A ≅ SV.obj B) (E : schemeDerivedCategory X)
      (a : A ⟶ JW.obj E) (b : B ⟶ JV.obj E),
      SW.map a ≫ sW.hom.app E = c.hom ≫ SV.map b ≫ sV.hom.app E →
      ∃ (F : schemeDerivedCategory (W ⊔ V).toScheme) (α : F ⟶ L.obj E),
        IsPerfect (W ⊔ V).toScheme F ∧
        (∀ (i : ℤ) (x : (W ⊔ V).toScheme), x.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace)) i).obj F).val.presheaf
              x))) ∧
        ∃ (iW : PW.obj F ≅ A) (iV : PV.obj F ≅ B),
          PW.map α ≫ kW.hom.app E = iW.hom ≫ a ∧
          PV.map α ≫ kV.hom.app E = iV.hom ≫ b := by
  dsimp only
  intro c E a b hab
  obtain ⟨F, α, iW, iV, hW, hV⟩ := exists_relative_open_gluing X W V A B c E a b hab
  let fW := X.homOfLE (show W ≤ W ⊔ V from le_sup_left)
  let fV := X.homOfLE (show V ≤ W ⊔ V from le_sup_right)
  let eW : (moduleRestriction fW).mapDerivedCategory.obj F ≅ A :=
    (Functor.mapDerivedCategoryNatIso
      (overlapRestrictionIso X (homOfLE le_sup_left : W ⟶ W ⊔ V))).symm.app F ≪≫ iW
  let eV : (moduleRestriction fV).mapDerivedCategory.obj F ≅ B :=
    (Functor.mapDerivedCategoryNatIso
      (overlapRestrictionIso X (homOfLE le_sup_right : V ⟶ W ⊔ V))).symm.app F ≪≫ iV
  refine ⟨F, α, ?_, ?_, iW, iV, hW, hV⟩
  · intro x
    rcases x.property with hx | hx
    · simpa only [fW, Scheme.homOfLE_apply', Subtype.coe_eta] using
        local_perfect_of_open_immersion fW F A hA eW ⟨x.val, hx⟩
    · simpa only [fV, Scheme.homOfLE_apply', Subtype.coe_eta] using
        local_perfect_of_open_immersion fV F B hB eV ⟨x.val, hx⟩
  · intro i x hxT
    rcases x.property with hx | hx
    · simpa only [fW, Scheme.homOfLE_apply', Subtype.coe_eta] using
        stalk_subsingleton_of_open_immersion fW F A eW i ⟨x.val, hx⟩
        (hAT i ⟨x.val, hx⟩ hxT)
    · simpa only [fV, Scheme.homOfLE_apply', Subtype.coe_eta] using
        stalk_subsingleton_of_open_immersion fV F B eV i ⟨x.val, hx⟩
        (hBT i ⟨x.val, hx⟩ hxT)

end AlgebraicGeometry.Scheme
