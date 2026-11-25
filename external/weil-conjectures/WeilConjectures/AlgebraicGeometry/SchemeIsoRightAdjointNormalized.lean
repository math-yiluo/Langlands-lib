/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalized comparison of right adjoints under a source isomorphism

Source: Stacks Project, Tags 0ATR and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
private theorem normalized_comparison
    {P U S : Type*} [Category P] [Category U] [Category S]
    {L : P ⥤ U} {R : U ⥤ P} {F : P ⥤ S} {F' : U ⥤ S}
    {A : S ⥤ P} {B : S ⥤ U}
    (adj : L ⊣ R) [IsIso adj.unit] [IsIso adj.counit]
    (adjA : F ⊣ A) (adjB : F' ⊣ B) (δ : F' ≅ R ⋙ F) :
    ∃ φ : A ⋙ L ≅ B, ∀ K : S,
      F.map (adj.unit.app (A.obj K)) ≫ δ.inv.app (L.obj (A.obj K)) ≫
        F'.map (φ.hom.app K) ≫ adjB.counit.app K = adjA.counit.app K := by
  let flip : R ⊣ L := adj.toEquivalence.symm.toAdjunction
  let transport : F' ⊣ A ⋙ L := (flip.comp adjA).ofNatIsoLeft δ.symm
  let φ := Adjunction.rightAdjointUniq transport adjB
  refine ⟨φ, ?_⟩
  intro K
  have hφ := Adjunction.rightAdjointUniq_hom_app_counit transport adjB K
  change F'.map (φ.hom.app K) ≫ adjB.counit.app K = transport.counit.app K at hφ
  rw [hφ]
  simp only [transport, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_inv, Adjunction.comp_counit_app]
  change F.map (adj.unit.app (A.obj K)) ≫ δ.inv.app (L.obj (A.obj K)) ≫
    (δ.hom.app (L.obj (A.obj K)) ≫ F.map (inv (adj.unit.app (A.obj K))) ≫
      adjA.counit.app K) = adjA.counit.app K
  simp only [Iso.inv_hom_id_app_assoc, ← F.map_comp_assoc,
    IsIso.hom_inv_id, F.map_id, Category.id_comp]

/-- Counit normalization specifying the comparison uniquely. It is the counit equation
for transport by the inverse of the isomorphism pullback adjunction.
Source: Stacks Project, Tag 0ATR, uniqueness of right adjoints. 
(blueprint: lem-sc-scheme-iso-right-adjoint-normalized)
-/
def SchemeIsoRightAdjointNormalized
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f')
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (adja : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty P).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjb : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty U).ι ⋙ schemeDerivedDirectImage f')
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f') _ _ _ _ f' _ _).fst E.obj E.property) ⊣ b)
    (φ : (a ⋙ (schemeDerivedQCohProperty P).ι) ⋙ derivedPullback e.hom ≅
      b ⋙ (schemeDerivedQCohProperty U).ι) : Prop :=
  let adj := fun {X Y : Scheme.{u}} (k : X ⟶ Y) ↦
    Classical.choose (exists_schemeDerivedAdjunction k
      (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) k))
  let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let c := comp e.hom f ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) he)
  let δ := conjugateIsoEquiv (adj f')
    ((adj f).comp (adj e.hom)) c
  ∀ K : schemeDerivedQCohCategory S,
    (schemeDerivedDirectImage f).map
        ((adj e.hom).unit.app (a.obj K).obj) ≫
      δ.inv.app ((derivedPullback e.hom).obj (a.obj K).obj) ≫
      (schemeDerivedDirectImage f').map (φ.hom.app K) ≫
      (adjb.counit.app K).hom = (adja.counit.app K).hom

/-- A normalized natural isomorphism of right adjoints under an isomorphism of sources.
This statement concerns one vertical morphism, with no base-change square or second mate.
Source: Stacks Project, Tag 0ATR, composite adjunction comparison, and Tag 0D5S.
(blueprint: lem-sc-scheme-iso-right-adjoint-normalized)

Proof: Pullback along e.hom is an equivalence, with inverse pullback along e.inv,
by the identity and composition comparisons. Its pinned adjunction therefore has
invertible unit and counit. Conjugate the pullback composition comparison for e.hom
and f to identify Rf' with Re followed by Rf. Restrict these comparisons to the full
quasi-coherent subcategories, using pullback preservation and qcqs pushforward
preservation. Reverse the equivalence adjunction and compose with adja, obtaining
a right adjoint to Rf' given by a followed by pullback along e.hom. Right-adjoint
uniqueness against adjb gives φ. The uniqueness counit equation, multiplied by
the unit of the pinned e.hom adjunction, is precisely the displayed normalization.
Full faithfulness of the inclusions gives its ambient form. The triangle identities
show that the normalization determines φ and work also on empty schemes. -/
theorem exists_schemeIsoRightAdjoint_normalized
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f')
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (adja : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty P).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjb : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty U).ι ⋙ schemeDerivedDirectImage f')
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f') _ _ _ _ f' _ _).fst E.obj E.property) ⊣ b)
 :
    ∃ φ : (a ⋙ (schemeDerivedQCohProperty P).ι) ⋙ derivedPullback e.hom ≅
        b ⋙ (schemeDerivedQCohProperty U).ι,
      SchemeIsoRightAdjointNormalized f f' e he a b adja adjb φ := by
  classical
  let adj := fun {X Y : Scheme.{u}} (k : X ⟶ Y) ↦
    Classical.choose (exists_schemeDerivedAdjunction k
      (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) k))
  let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  obtain ⟨i, _, _, _⟩ :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2
  let ev := CategoryTheory.Equivalence.mk (derivedPullback e.hom) (derivedPullback e.inv)
    (comp e.inv e.hom ≪≫ eqToIso
      (congrArg (fun k ↦ derivedPullback k) e.inv_hom_id) ≪≫ i P).symm
    (comp e.hom e.inv ≪≫ eqToIso
      (congrArg (fun k ↦ derivedPullback k) e.hom_inv_id) ≪≫ i U)
  have : (derivedPullback e.hom).IsEquivalence := ev.isEquivalence_functor
  have : (schemeDerivedDirectImage e.hom).IsEquivalence :=
    (adj e.hom).isEquivalence_right_of_isEquivalence_left
  let PP := schemeDerivedQCohProperty P
  let PU := schemeDerivedQCohProperty U
  let PS := schemeDerivedQCohProperty S
  let L := PU.lift (PP.ι ⋙ derivedPullback e.hom)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh e.hom).1 E.obj E.property)
  let R := PP.lift (PU.ι ⋙ schemeDerivedDirectImage e.hom)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint U P e.hom).fst
      E.obj E.property)
  let F := PS.lift (PP.ι ⋙ schemeDerivedDirectImage f)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint P S f).fst E.obj E.property)
  let F' := PS.lift (PU.ι ⋙ schemeDerivedDirectImage f')
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint U S f').fst E.obj E.property)
  let cl : PP.ι ⋙ derivedPullback e.hom ≅ L ⋙ PU.ι :=
    (PU.liftCompιIso _ _).symm
  let cr : PU.ι ⋙ schemeDerivedDirectImage e.hom ≅ R ⋙ PP.ι :=
    (PP.liftCompιIso _ _).symm
  let ar : L ⊣ R := Adjunction.restrictFullyFaithful (adj e.hom)
    PP.fullyFaithfulι PU.fullyFaithfulι cl cr
  have : L.Full := by dsimp [L]; infer_instance
  have : L.Faithful := by dsimp [L]; infer_instance
  have : R.Full := by dsimp [R]; infer_instance
  have : R.Faithful := by dsimp [R]; infer_instance
  have : IsIso ar.unit := inferInstance
  have : IsIso ar.counit := inferInstance
  let c := comp e.hom f ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) he)
  let δ := conjugateIsoEquiv (adj f') ((adj f).comp (adj e.hom)) c
  let δq : F' ≅ R ⋙ F := NatIso.ofComponents
    (fun E ↦ PS.isoMk (δ.app E.obj)) (by
      intro E E' t
      ext
      exact δ.hom.naturality t.hom)
  obtain ⟨φq, hφq⟩ := normalized_comparison ar adja adjb δq
  let φ : (a ⋙ PP.ι) ⋙ derivedPullback e.hom ≅ b ⋙ PU.ι :=
    Functor.isoWhiskerRight φq PU.ι
  refine ⟨φ, ?_⟩
  change ∀ K : schemeDerivedQCohCategory S,
    (schemeDerivedDirectImage f).map ((adj e.hom).unit.app (a.obj K).obj) ≫
      δ.inv.app ((derivedPullback e.hom).obj (a.obj K).obj) ≫
      (schemeDerivedDirectImage f').map (φ.hom.app K) ≫
      (adjb.counit.app K).hom = (adja.counit.app K).hom
  intro K
  have h := congrArg (fun t ↦ t.hom) (hφq K)
  have hu : (ar.unit.app (a.obj K)).hom = (adj e.hom).unit.app (a.obj K).obj := by
    have hunit := Adjunction.map_restrictFullyFaithful_unit_app (adj e.hom)
      PP.fullyFaithfulι PU.fullyFaithfulι cl cr (a.obj K)
    change (ar.unit.app (a.obj K)).hom = (adj e.hom).unit.app (a.obj K).obj ≫
      (schemeDerivedDirectImage e.hom).map (𝟙 _) ≫ 𝟙 _ at hunit
    erw [(schemeDerivedDirectImage e.hom).map_id, Category.comp_id,
      Category.comp_id] at hunit
    exact hunit
  change (schemeDerivedDirectImage f).map (ar.unit.app (a.obj K)).hom ≫
    δ.inv.app ((derivedPullback e.hom).obj (a.obj K).obj) ≫
    (schemeDerivedDirectImage f').map (φ.hom.app K) ≫
    (adjb.counit.app K).hom = (adja.counit.app K).hom at h
  rwa [hu] at h

end
end AlgebraicGeometry
