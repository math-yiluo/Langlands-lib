/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison

/-! # The canonical pointed strict-local morphism

Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
The existing residue-field formulation is retained; this interface packages its uniquely
characterized map without requiring the caller to supply residue identifications.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Evaluation at the geometric point `y` on the small coordinate-ring colimit
`strictHenselizationRing y`: upstream's `strictHenselizationPointEvaluation` precomposed with
the comparison isomorphism `smallStrictHenselizationColimitIso`.
Source: Stacks Project, Tag 04HX
(blueprint: def-weil-pbc-strict-henselization-point-evaluation). -/
noncomputable def strictHenselizationRingPointEvaluation
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) : strictHenselizationRing y →+* Ω :=
  (strictHenselizationPointEvaluation y).comp (smallStrictHenselizationColimitIso y).hom.hom

/-- On spectra, the ring-level evaluation factors through the comparison isomorphism. -/
theorem Spec_map_strictHenselizationRingPointEvaluation
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation y)) =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation y)) ≫
        Spec.map (smallStrictHenselizationColimitIso y).hom := by
  rw [← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ring-level evaluation recovers the given geometric point at every chosen
neighbourhood; this transports `strictHenselizationPointEvaluation_pointed` along
`smallStrictHenselizationColimitIso`.
Source: Stacks Project, Tag 04HX
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-pointed). -/
theorem strictHenselizationRingPointEvaluation_pointed
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) :
    Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation y)) ≫
      (strictHenselizationCone y).π.app (Opposite.op (Opposite.op j)) ≫
      (Spec (Opposite.unop ((equivSmallModel.{u}
        (strictHenselizationNeighbourhoods y)).inverse.obj j).1.left)).isoSpec.inv =
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).2.left := by
  let : HasColimit (strictHenselizationDiagram y) := inferInstance
  let : (strictHenselizationAffineInclusion y).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence y
  let r := (equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse ⋙
    strictHenselizationAffineInclusion y
  have hleg : colimit.ι (strictHenselizationAffineDiagram y) (Opposite.op j) ≫
      (smallStrictHenselizationColimitIso y).hom =
        (smallStrictHenselizationCocone y).ι.app (Opposite.op j) :=
    Functor.Final.ι_colimitIso_hom r.op (strictHenselizationDiagram y) (Opposite.op j)
  have hring : colimit.ι (strictHenselizationAffineDiagram y) (Opposite.op j) ≫
      CommRingCat.ofHom (strictHenselizationRingPointEvaluation y) =
        (smallStrictHenselizationCocone y).ι.app (Opposite.op j) ≫
          CommRingCat.ofHom (strictHenselizationPointEvaluation y) := by
    rw [← hleg]
    rfl
  change _ ≫ Spec.map (colimit.ι (strictHenselizationAffineDiagram y) (Opposite.op j)) ≫ _ = _
  rw [← Spec.map_comp_assoc, hring, Spec.map_comp_assoc]
  exact strictHenselizationPointEvaluation_pointed y j

set_option backward.isDefEq.respectTransparency false in
/-- Colimit extensionality identifies a pointed residue formula with colimit evaluation. -/
private theorem evaluation_eq_of_pointed
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (ψ : strictHenselization y →+* Ω)
    (hp : ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods y),
      Spec.map (CommRingCat.ofHom ψ) ≫
        (strictHenselizationAffineCone y).π.app (Opposite.op (Opposite.op j)) ≫
        (Spec (Opposite.unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods y)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).2.left) :
    ψ = strictHenselizationPointEvaluation y := by
  have he : CommRingCat.ofHom ψ = CommRingCat.ofHom (strictHenselizationPointEvaluation y) := by
    apply (isColimitSmallStrictHenselizationCocone y).hom_ext
    intro j
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{u}
      (strictHenselizationNeighbourhoods y)).inverse.obj j.unop).1.left)).isoSpec.inv).1
    simp only [Category.assoc]
    exact (hp j.unop).trans (strictHenselizationPointEvaluation_pointed y j.unop).symm
  exact congrArg CommRingCat.Hom.hom he

set_option backward.isDefEq.respectTransparency false in
/-- The unique pointed map of upstream strict localizations over the original morphism. -/
private theorem strictLocalizationMap_existsUnique
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃! h : strictLocalization x ⟶ strictLocalization (x ≫ f),
      h ≫ strictLocalizationToBase (x ≫ f) = strictLocalizationToBase x ≫ f ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ h =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ f))) := by
  let : Algebra (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom.toAlgebra
  let : Algebra (S.residueField ((x ≫ f) (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (x ≫ f))).hom.toAlgebra
  obtain ⟨_, _, _, _, hxx⟩ := strictHenselizationResidue x rfl
  obtain ⟨_, _, _, _, hxff⟩ := strictHenselizationResidue (x ≫ f) rfl
  obtain ⟨σx, hσx, _⟩ := hxx
  obtain ⟨σxf, hσxf, _⟩ := hxff
  obtain ⟨_, hdata⟩ := strictHenselizationFunctoriality f x (x ≫ f) rfl rfl rfl
      σxf σx hσxf.1 hσx.1
  obtain ⟨h, hlocal, hbase, hpoint, huniq, _⟩ := hdata
  have hevalx := evaluation_eq_of_pointed x _ hσx.1
  have hevalxf := evaluation_eq_of_pointed (x ≫ f) _ hσxf.1
  have hpoint' :
      strictHenselizationPointEvaluation (x ≫ f) =
        (strictHenselizationPointEvaluation x).comp h.hom := by
    simpa only [hevalx, hevalxf] using hpoint
  have hspoint : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
      Spec.map h = Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ f))) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hpoint'.symm
  refine ⟨Spec.map h, ⟨hbase, hspoint⟩, ?_⟩
  intro h' hh'
  obtain ⟨hbase', hpoint'⟩ := hh'
  let r : strictHenselization (x ≫ f) ⟶ strictHenselization x := Spec.preimage h'
  have hr : Spec.map r = h' := Spec.map_preimage h'
  have hrpoint : strictHenselizationPointEvaluation (x ≫ f) =
      (strictHenselizationPointEvaluation x).comp r.hom := by
    have heq : CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ f)) =
        r ≫ CommRingCat.ofHom (strictHenselizationPointEvaluation x) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hr]
      exact hpoint'.symm
    exact congrArg CommRingCat.Hom.hom heq
  have hrlocal : IsLocalHom r.hom := by
    have heval_local : IsLocalHom (strictHenselizationPointEvaluation (x ≫ f)) := by
      rw [← hevalxf]
      infer_instance
    have : IsLocalHom ((strictHenselizationPointEvaluation x).comp r.hom) :=
      hrpoint ▸ heval_local
    exact isLocalHom_of_comp r.hom (strictHenselizationPointEvaluation x)
  have hrh : r = h := huniq r hrlocal (hr ▸ hbase') (by
    simpa only [hevalx, hevalxf] using hrpoint)
  exact hr.symm.trans (congrArg Spec.map hrh)

/-- The spectra of the two sides of the comparison isomorphism are mutually inverse. -/
private theorem Spec_map_smallStrictHenselizationColimitIso_hom_inv
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Spec.map (smallStrictHenselizationColimitIso y).hom ≫
      Spec.map (smallStrictHenselizationColimitIso y).inv = 𝟙 _ := by
  rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

/-- The spectra of the two sides of the comparison isomorphism are mutually inverse. -/
private theorem Spec_map_smallStrictHenselizationColimitIso_inv_hom
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Spec.map (smallStrictHenselizationColimitIso y).inv ≫
      Spec.map (smallStrictHenselizationColimitIso y).hom = 𝟙 _ := by
  rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- The unique pointed map over the original morphism.
Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
Proof: apply strictHenselizationResidue to obtain the local structures and the uniquely
pointed residue identifications. Use strictHenselizationFunctoriality with these
identifications and the residue embeddings furnished by the geometric points.
Its local homomorphism gives the required spectrum map. Evaluation is the compatible
geometric-point cocone, so its residue equation is exactly the second displayed equation.
Conversely a pointed map maps the closed point to the closed point and is local.
The residue equation and the uniqueness clause of functoriality give uniqueness.
Finally transport along the comparison isomorphisms `smallStrictHenselizationColimitIso`. -/
theorem strictHenselizationMap_existsUnique
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃! h : strictHenselizationScheme x ⟶ strictHenselizationScheme (x ≫ f),
      h ≫ strictHenselizationStructuralMap (x ≫ f) =
        strictHenselizationStructuralMap x ≫ f ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation x)) ≫ h =
        Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation (x ≫ f))) := by
  obtain ⟨k, ⟨hkb, hkp⟩, hku⟩ := strictLocalizationMap_existsUnique f x
  have hab {Y : Scheme.{u}} (y : Spec (.of Ω) ⟶ Y) :=
    Spec_map_smallStrictHenselizationColimitIso_hom_inv y
  have hba {Y : Scheme.{u}} (y : Spec (.of Ω) ⟶ Y) :=
    Spec_map_smallStrictHenselizationColimitIso_inv_hom y
  have hstr {Y : Scheme.{u}} (y : Spec (.of Ω) ⟶ Y) :=
    smallStrictHenselizationColimitIso_toBase y
  have hev {Y : Scheme.{u}} (y : Spec (.of Ω) ⟶ Y) :=
    Spec_map_strictHenselizationRingPointEvaluation y
  refine ⟨Spec.map (smallStrictHenselizationColimitIso x).inv ≫ k ≫
    Spec.map (smallStrictHenselizationColimitIso (x ≫ f)).hom, ⟨?_, ?_⟩, ?_⟩
  · rw [← hstr (x ≫ f), ← hstr x]
    simp only [Category.assoc, reassoc_of% (hab (x ≫ f)), hkb]
  · rw [hev x, hev (x ≫ f)]
    simp only [Category.assoc, reassoc_of% (hab x), reassoc_of% hkp]
  · rintro h ⟨hb, hp⟩
    have hk : Spec.map (smallStrictHenselizationColimitIso x).hom ≫ h ≫
        Spec.map (smallStrictHenselizationColimitIso (x ≫ f)).inv = k := by
      apply hku
      constructor
      · rw [Category.assoc, Category.assoc, hstr (x ≫ f), hb, ← hstr x]
        rw [← Category.assoc, ← Category.assoc, hab x]
        exact Category.id_comp (strictLocalizationToBase x ≫ f)
      · rw [← Category.assoc, ← hev x, reassoc_of% hp, hev (x ≫ f), Category.assoc,
          hab (x ≫ f)]
        exact Category.comp_id _
    rw [← hk]
    simp only [Category.assoc, reassoc_of% (hba x), hba (x ≫ f)]
    exact (Category.comp_id h).symm

end AlgebraicGeometry.Scheme
