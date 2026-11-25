/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived


/-! # Supported perfect restriction in a compact-open overlap model

Source: Stacks Project, Tags 08EK and 09IM.
(blueprint: lem-sc-supported-overlap-restriction-data).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a chosen localization along an exact equivalence of abelian categories.
This is the localization construction in `SchemeIsoDerivedLocalizations`, specialized
to the module-sheaf universe; its helper there is private. -/
private theorem hasDerivedCategory_of_equivalence {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩


set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {S T : Scheme.{u}} (s : S ≅ T) :
    SheafOfModules.{u} (moduleRings S.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings T.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Modules.pushforwardComp s.hom s.inv ≪≫
      Modules.pushforwardCongr s.hom_inv_id ≪≫ Modules.pushforwardId S).symm)
    (Modules.pushforwardComp s.inv s.hom ≪≫
      Modules.pushforwardCongr s.inv_hom_id ≪≫ Modules.pushforwardId T)


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Express restriction of a supported perfect complex to the overlap on a compact
open of V. This is restriction data only; no extension to V is asserted.
Source: Stacks Project, Tag 09IM, the overlap input to Tag 08EK.
(blueprint: lem-sc-supported-overlap-restriction-data).

Proof: Set U to the open range of the inclusion of W intersect V into V. The intersection
is compact by quasi-separatedness and compactness of W and affine V, so U is compact.
The inverse image of T in V is closed. Its complement identifies through the open
embedding with V intersect the compact open complement of T, hence is compact by the
same intersection criterion. The inclusion U.toScheme into W is an open immersion.
Define G by exact restriction of F along that inclusion. At each point of U, pull back
a strictly perfect neighbourhood model of F, preserving the degree bounds, finite free
modules and retract equations. These give perfectness of G. Exact homology and the
restriction-stalk comparison identify each stalk of G with the corresponding stalk of F,
so support restricts as stated. The scheme isomorphism from the ambient overlap to U
supplies the exact module equivalence and the derived equivalence e. Transport the
chosen derived localization along it, and transport the localized-site localizations
through the corresponding equivalences on each open of U to supply hO. The natural
restriction composition comparisons identify ordinary restriction from V followed by e
with SV, and identify e(G) with SW(F). Both comparisons arise by deriving the underived
restriction comparisons, so commute with shifts and biproducts. Apply those comparisons
to G plus G[1] to obtain the last isomorphism. Empty opens and empty support need no
separate case: the same scheme isomorphism, exact restrictions and zero stalks apply. -/
theorem exists_supported_overlap_restriction_data
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    (F : schemeDerivedCategory W.toScheme) (hF : IsPerfect W.toScheme F)
    (hFT : (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F).val.presheaf x)))) :
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    ∃ U : V.toScheme.Opens, IsCompact (U : Set V.toScheme) ∧
      IsClosed (Subtype.val ⁻¹' T : Set V.toScheme) ∧
      IsCompact (Subtype.val ⁻¹' T : Set V.toScheme)ᶜ ∧
      ∃ hD : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      letI := hD
      ∃ hO : ∀ O : U.toScheme.Opens, HasDerivedCategory.{w}
          (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over O)),
      letI := hO
      ∃ G : schemeDerivedCategory U.toScheme, IsPerfect U.toScheme G ∧
        (∀ (i : ℤ) (x : U.toScheme), x.val.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).obj G).val.presheaf
              x))) ∧
        ∃ e : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory (W ⊓ V).toScheme,
          Nonempty ((schemeOpenRestriction V.toScheme U).mapDerivedCategory ⋙ e.functor ≅ SV) ∧
          Nonempty (e.functor.obj (G ⊞ G⟦(1 : ℤ)⟧) ≅ SW.obj (F ⊞ F⟦(1 : ℤ)⟧)) := by
  classical
  -- Reuse the abelian structures throughout the derived comparisons. Keep their values visible
  -- so the chosen derived localizations still have definitionally equal instance parameters.
  let : Abelian (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) := inferInstance
  let : Abelian (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) := inferInstance
  let : Abelian (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace)) :=
    inferInstance
  let U : V.toScheme.Opens := V.ι ⁻¹ᵁ W
  let : Abelian (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := inferInstance
  have hcU : IsCompact (U : Set V.toScheme) := by
    apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
    have he : Subtype.val '' (U : Set V.toScheme) = (V : Set X) ∩ W := by
      ext x
      simp [U, Set.mem_inter_iff, and_comm]
    rw [he]
    exact hV.isCompact.inter_of_isOpen hW V.isOpen W.isOpen
  have hcT : IsClosed (Subtype.val ⁻¹' T : Set V.toScheme) :=
    hT.preimage continuous_subtype_val
  have hcTc : IsCompact (Subtype.val ⁻¹' T : Set V.toScheme)ᶜ := by
    apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
    have he : Subtype.val '' (Subtype.val ⁻¹' T : Set V.toScheme)ᶜ =
        (V : Set X) ∩ Tᶜ := by
      ext x
      simp [Set.mem_inter_iff, and_comm]
    rw [he]
    exact hV.isCompact.inter_of_isOpen hTc V.isOpen hT.isOpen_compl
  obtain ⟨hD⟩ : Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) :=
    hasDerivedCategory_of_equivalence (Modules.overEquiv U).symm
  let := hD
  obtain ⟨hO⟩ := nonempty_derivedOpenLocalization U.toScheme
  let := hO
  let j : U.toScheme ⟶ W.toScheme := V.ι ∣_ W
  let R : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.restrictFunctor j
  have : PreservesFiniteLimits R := by
    dsimp [R, Modules.restrictFunctor]
    infer_instance
  have : PreservesFiniteColimits R := by
    change PreservesFiniteColimits (Modules.restrictFunctor j)
    infer_instance
  let G : schemeDerivedCategory U.toScheme := R.mapDerivedCategory.obj F
  refine ⟨U, hcU, hcT, hcTc, hD, hO, G, ?_, ?_, ?_⟩
  · let B := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)
    let C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
    let P : B ⥤ C := Modules.tensorPullback j
    obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      L, hLobj, hLmap, hLadd, ε, hL, htri, hK⟩ :=
      derivedPullback_spec j
    have h : L = P := CategoryTheory.Functor.ext hLobj (fun M N a ↦ hLmap a)
    subst L
    let θ : R ≅ P := Modules.restrictFunctorIsoPullback j ≪≫
      ((Modules.nonempty_tensorPullbackAdjunction j).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction j)).symm
    have : PreservesFiniteLimits P := preservesFiniteLimits_of_natIso θ
    have : PreservesFiniteColimits P := preservesFiniteColimits_of_natIso θ
    let Q := HomotopyCategory.quasiIso B (.up ℤ)
    have : (derivedPullback j).IsLeftDerivedFunctor ε Q := hL
    have : P.mapDerivedCategory.IsLeftDerivedFunctor P.mapDerivedCategoryFactorsh.hom Q :=
      Functor.isLeftDerivedFunctor_of_inverts _ _ P.mapDerivedCategoryFactorsh
    let i : derivedPullback j ≅ P.mapDerivedCategory :=
      Functor.leftDerivedUnique P.mapDerivedCategory (derivedPullback j) ε
        P.mapDerivedCategoryFactorsh.hom Q
    let c := (Functor.mapDerivedCategoryNatIso θ).app F ≪≫ i.symm.app F
    have hp := derivedPullback_preserve_perfect j F hF
    intro x
    obtain ⟨A, hx, K, hK, ⟨iK⟩⟩ := hp x
    refine ⟨A, hx, K, hK, ?_⟩
    exact ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) A).mapDerivedCategory.mapIso c ≪≫ iK⟩
  · intro i x hx
    let S := Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
    let c := S.mapIso ((R.mapDerivedCategoryHomologyFunctorIso i).symm.app F) ≪≫
      (Modules.restrictStalkNatIso j x).app
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F)
    have hp : (j x).val = x.val.val := morphismRestrict_base_coe V.ι W x
    have ht : (j x).val ∉ T := hp ▸ hx
    let : Subsingleton (↑((Modules.toPresheaf W.toScheme ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (j x)).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F))) :=
      hFT i (j x) ht
    exact (ConcreteCategory.bijective_of_isIso c.hom).1.subsingleton
  · let s : U.toScheme ≅ (W ⊓ V).toScheme :=
      V.ι.isoImage U ≪≫ X.isoOfEq (V.functor_map_eq_inf W)
    let E := moduleIsoEquivalence s
    have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
    have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
    let e := E.mapDerivedCategory
    let cE : E.functor ≅ Modules.restrictFunctor s.inv :=
      E.toAdjunction.leftAdjointUniq (Modules.restrictAdjunction s.inv)
    have hsV : s.inv ≫ U.ι = X.homOfLE (inf_le_right : W ⊓ V ≤ V) := by
      apply (cancel_mono V.ι).mp
      simp [s, Category.assoc, Scheme.isoOfEq_inv_ι]
    have hsW : s.inv ≫ j = X.homOfLE (inf_le_left : W ⊓ V ≤ W) := by
      apply (cancel_mono W.ι).mp
      simp only [Category.assoc, j, morphismRestrict_ι, Scheme.homOfLE_ι]
      rw [← Category.assoc, hsV, Scheme.homOfLE_ι]
    let cV : schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : W ⊓ V ⟶ V) ≅
        Modules.restrictFunctor (X.homOfLE (inf_le_right : W ⊓ V ≤ V)) :=
      Functor.isoWhiskerLeft (Modules.overEquiv V).inverse
          (Modules.overMapCompOverEquiv (homOfLE inf_le_right : W ⊓ V ⟶ V)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Modules.overEquiv V).counitIso _ ≪≫
        Functor.leftUnitor _
    let cW : schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : W ⊓ V ⟶ W) ≅
        Modules.restrictFunctor (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) :=
      Functor.isoWhiskerLeft (Modules.overEquiv W).inverse
          (Modules.overMapCompOverEquiv (homOfLE inf_le_left : W ⊓ V ⟶ W)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Modules.overEquiv W).counitIso _ ≪≫
        Functor.leftUnitor _
    let tV : schemeOpenRestriction V.toScheme U ⋙ E.functor ≅
        schemeOpenOverlapRestriction X (homOfLE inf_le_right : W ⊓ V ⟶ V) :=
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U) _ ≪≫
        Functor.isoWhiskerLeft _ cE ≪≫ (Modules.restrictFunctorComp s.inv U.ι).symm ≪≫
        Modules.restrictFunctorCongr hsV ≪≫ cV.symm
    let tW : R ⋙ E.functor ≅
        schemeOpenOverlapRestriction X (homOfLE inf_le_left : W ⊓ V ⟶ W) :=
      Functor.isoWhiskerLeft _ cE ≪≫ (Modules.restrictFunctorComp s.inv j).symm ≪≫
        Modules.restrictFunctorCongr hsW ≪≫ cW.symm
    let dV := (Functor.mapDerivedCategoryCompIso
      (schemeOpenRestriction V.toScheme U) E.functor) ≪≫
        Functor.mapDerivedCategoryNatIso tV
    let dW := (Functor.mapDerivedCategoryCompIso R E.functor) ≪≫
      Functor.mapDerivedCategoryNatIso tW
    refine ⟨e, ⟨dV⟩, ⟨?_⟩⟩
    have : R.mapDerivedCategory.Additive := inferInstance
    have : PreservesBinaryBiproducts R.mapDerivedCategory :=
      preservesBinaryBiproducts_of_preservesBinaryProducts R.mapDerivedCategory
    let b : R.mapDerivedCategory.obj (F ⊞ F⟦(1 : ℤ)⟧) ≅ G ⊞ G⟦(1 : ℤ)⟧ :=
      R.mapDerivedCategory.mapBiprod F (F⟦(1 : ℤ)⟧) ≪≫
        biprod.mapIso (Iso.refl _) ((R.mapDerivedCategory.commShiftIso (1 : ℤ)).app F)
    exact e.functor.mapIso b.symm ≪≫ dW.app (F ⊞ F⟦(1 : ℤ)⟧)

end AlgebraicGeometry.Scheme
