/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.NormalizedHomotopyTensorHom

/-! # Bijectivity of normalized derived tensor-Hom maps
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex, Tag 0A90.
(blueprint: lem-pc-canonical-derived-tensor-hom-map-bijective).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

-- Keep the definitional component comparison explicit in the normalization proof.
-- Both sides use the product projections chosen by homComplex_exists.
private theorem uncurryComponent_eq (X : Scheme.{uCD})
    (P L M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p r n : ℤ) (h' : r + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.symmetricCategory X.sheaf
    schemeTensorHomUncurryComponent X P L M φ p r n h' =
      (β_ (P.X p) (L.X r)).hom ≫
        (SheafOfModules.tensorHomEquiv (L.X r) (P.X p)
          (((schemeHomKInjectiveResolution X).obj M).X n)).symm
          (φ.f p ≫ homTensorProjection X.sheaf L
            ((schemeHomKInjectiveResolution X).obj M) p r n h') := by
  rfl

private def localizedHomEquiv (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (P I : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient _ (.up ℤ)).obj I) ≃
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :=
  (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P) I)).trans
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso _).app P)
        ((DerivedCategory.quotientCompQhIso _).app I))

private theorem localizedHomEquiv_map (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (P I : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (φ : P ⟶ I) :
    localizedHomEquiv X P I ((HomotopyCategory.quotient _ (.up ℤ)).map φ) =
      DerivedCategory.Q.map φ := by
  change (DerivedCategory.quotientCompQhIso _).inv.app P ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map φ) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app I = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  simp

private theorem tensorModelMap_isIso (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) : IsIso (pullbackTensorModelMap X P N) := by
  let C := SheafOfModules.{uCD} (moduleRings X.toRingedSpace)
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{uCD} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : Limits.HasColimitsOfSize.{0, 0} C := Limits.hasColimitsOfSizeShrink.{0, 0, uCD, uCD} C
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have (M : C) : Limits.PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) :=
    Limits.preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M : C) : Limits.PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ C := inferInstance
  have (j : ℤ) : Limits.HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C := inferInstance
  have : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
    inferInstance
  have hk : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro M hM
    obtain ⟨M, rfl⟩ := M.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hM
    have hr : HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj M ⊗
          (HomotopyCategory.quotient C (.up ℤ)).obj P) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP M hM)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj N)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ)) _ _ hk
  change IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) P N)
  change IsIso (_ ≫ _ ≫ _)
  change IsIso (_ ≫ (_ ≫ _) ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Every normalized natural uncurrying map is bijective.
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom), using
sites-cohomology.tex, Tag 0A90 (Hom complexes).
(blueprint: lem-pc-canonical-derived-tensor-hom-map-bijective).
Proof: Reuse `homTensorDegreewiseMap_spec`, `homTensorDegreewiseMap_comm`, and
`homTensorDegreewiseMap_natural` for the normalized degreewise construction,
differential compatibility and functoriality. The global-cochain comparison
`homComplex_global_cochains` identifies chain maps with degree-zero cocycles and
homotopies with degree-minus-one boundaries; hence this comparison gives precisely
the stated map on homotopy classes. The pure-tensor condition in the degreewise
specification agrees with `schemeTensorHomUncurryComponent` by the sheaf tensor-Hom
adjunction and symmetry. Thus these existing lemmas supply the component calculation,
including its normalization, rather than an arbitrary existential isomorphism.
First take K=QP and L=QLc with P,Lc K-flat, and M=QMc. The tensor model
comparison is an isomorphism, and QHom(Lc,I(Mc)) computes derived internal Hom.
Both I(Mc) and Hom(Lc,I(Mc)) are K-injective, so maps to them in the derived category
are homotopy classes of chain maps. Componentwise currying is inverse to the
uncurrying in the representative clause. The sheaf tensor-Hom inverse identities
on every tensor summand prove the two inverse identities for chain maps. The same
calculation for homotopies shows these inverse maps descend to homotopy classes.
Consequently the map prescribed by that clause is injective and surjective on
these representatives. Every derived object has a K-flat representative, and every
target has a complex representative. Naturality with respect to their isomorphisms
conjugates t by bijections of Hom sets. Bijectivity is preserved by these
conjugations, proving the result for arbitrary K,L,M. -/
theorem canonicalDerivedTensorHomMap_bijective (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : IsCanonicalDerivedTensorHomMap X t) :
    ∀ K L M, Function.Bijective (t K L M) := by
  classical
  let C := SheafOfModules.{uCD} (moduleRings X.toRingedSpace)
  -- Cache the abelian structure used by the localization and resolution constructions.
  let : Abelian C := inferInstance
  let Q := DerivedCategory.Q.{wCD} (C := C)
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf
  have := SheafOfModules.isMonoidal_W X.sheaf
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{uCD} :=
    inferInstance
  have : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{uCD} :=
    inferInstance
  let := SheafOfModules.monoidalCategory X.sheaf
  let := schemeDerivedTensorMonoidal X
  let := SheafOfModules.symmetricCategory X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  have : IsGrothendieckAbelian.{uCD} C := SheafOfModules.isGrothendieckAbelian _
  have : Limits.HasColimitsOfSize.{0, 0} C :=
    Limits.hasColimitsOfSizeShrink.{0, 0, uCD, uCD} C
  have hrep (P L M : CochainComplex C ℤ) (hP : P.IsKFlatTensor) (hL : L.IsKFlatTensor) :
      Function.Bijective (t (Q.obj P) (Q.obj L) (Q.obj M)) := by
    let q := HomotopyCategory.quotient C (.up ℤ)
    let I := (schemeHomKInjectiveResolution X).obj M
    have : I.IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{uCD} C M
    have : (homComplex (R := X.sheaf) L I).IsKInjective :=
      CochainComplex.isKInjective_homComplex_of_isKFlat (R := X.sheaf) L I hL
    have := tensorModelMap_isIso X P L hP
    have : IsIso (Q.map
        ((CochainComplex.toKInjectiveResolution.{uCD} C).app M)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uCD} C M).2
    have : IsIso (schemeHomResolutionInverse X M) := by
      change IsIso (inv (Q.map
        ((CochainComplex.toKInjectiveResolution.{uCD} C).app M)))
      infer_instance
    let j := schemeDerivedInternalHomResolutionIso X L M
    let src := (localizedHomEquiv X P (homComplex (R := X.sheaf) L I)).trans
      (Iso.homCongr (Iso.refl (Q.obj P)) j.symm)
    let dst := (localizedHomEquiv X (pullbackTensorTotal X P L) I).trans
      (Iso.homCongr (asIso (pullbackTensorModelMap X P L)).symm
        (asIso (schemeHomResolutionInverse X M)))
    obtain ⟨e, he⟩ := exists_normalizedHomotopyTensorHom X P L I
    have hcomm : (t (Q.obj P) (Q.obj L) (Q.obj M)) ∘ src = dst ∘ e := by
      funext v
      -- Compare chosen representatives, then transport along the quotient equation.
      let φ : P ⟶ homComplex (R := X.sheaf) L I := v.out
      have hv : q.map φ = v := HomotopyCategory.quotient_map_out v
      have hψ_exists := ht.2 P L M hP φ
      let ψ := hψ_exists.choose
      have hψ := hψ_exists.choose_spec.1
      have htψ := hψ_exists.choose_spec.2
      let ψ' := (he φ).choose
      have hψ' := (he φ).choose_spec.1
      have heψ := (he φ).choose_spec.2
      have hψeq : ψ = ψ' := by
        apply HomologicalComplex.hom_ext
        intro n
        apply HomologicalComplex.mapBifunctor.hom_ext
          (K₁ := P) (K₂ := L) (F := curriedTensor C) (c := .up ℤ)
        intro p r hpr
        change p + r = n at hpr
        have hrp : r + p = n := (add_comm r p).trans hpr
        exact (hψ p r n hpr hrp).trans
          ((uncurryComponent_eq X P L M φ p r n hrp).trans
            (hψ' p r n hpr hrp).symm)
      have hs : src (q.map φ) = Q.map φ ≫ j.inv := by
        dsimp only [src, Equiv.trans_apply, Iso.homCongr_apply]
        exact (Category.id_comp _).trans
          (congrArg (fun f ↦ f ≫ j.inv) (localizedHomEquiv_map X P _ φ))
      have hd : dst (q.map ψ) =
          pullbackTensorModelMap X P L ≫ Q.map ψ ≫ schemeHomResolutionInverse X M := by
        dsimp only [dst, Equiv.trans_apply, Iso.homCongr_apply]
        exact congrArg
          (fun f ↦ pullbackTensorModelMap X P L ≫ f ≫ schemeHomResolutionInverse X M)
          (localizedHomEquiv_map X (pullbackTensorTotal X P L) I ψ)
      change t (Q.obj P) (Q.obj L) (Q.obj M) (src v) = dst (e v)
      calc
        _ = t (Q.obj P) (Q.obj L) (Q.obj M) (src (q.map φ)) :=
          congrArg (fun v ↦ t (Q.obj P) (Q.obj L) (Q.obj M) (src v)) hv.symm
        _ = t (Q.obj P) (Q.obj L) (Q.obj M) (Q.map φ ≫ j.inv) := congrArg _ hs
        _ = pullbackTensorModelMap X P L ≫ Q.map ψ ≫ schemeHomResolutionInverse X M := htψ
        _ = dst (q.map ψ) := hd.symm
        _ = dst (q.map ψ') := congrArg (fun f ↦ dst (q.map f)) hψeq
        _ = dst (e (q.map φ)) := congrArg dst heψ.symm
        _ = dst (e v) := congrArg (fun v ↦ dst (e v)) hv
    have hb := dst.bijective.comp e.bijective
    rw [← hcomm] at hb
    exact (Function.Bijective.of_comp_iff _ src.bijective).mp hb
  intro K L M
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage K)
  obtain ⟨Lc, l, hL, _, hl, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage L)
  have : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have : IsIso (Q.map l) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ l).2 hl
  let a : Q.obj P ≅ K := asIso (Q.map p) ≪≫ Q.objObjPreimageIso K
  let b : Q.obj Lc ≅ L := asIso (Q.map l) ≪≫ Q.objObjPreimageIso L
  let Mc := Q.objPreimage M
  let c : Q.obj Mc ≅ M := Q.objObjPreimageIso M
  let d := H.mapIso (Iso.prod b.op c.symm)
  let src := Iso.homCongr a.symm d
  let dst := Iso.homCongr (tensorIso a b).symm c.symm
  have hcomm : (t (Q.obj P) (Q.obj Lc) (Q.obj Mc)) ∘ src = dst ∘ t K L M := by
    funext f
    exact ht.1 K (Q.obj P) L (Q.obj Lc) M (Q.obj Mc) a.hom b.hom c.inv f
  have hb := (hrep P Lc Mc hP hL).comp src.bijective
  rw [hcomm] at hb
  exact (Function.Bijective.of_comp_iff' dst.bijective _).mp hb

end AlgebraicGeometry
