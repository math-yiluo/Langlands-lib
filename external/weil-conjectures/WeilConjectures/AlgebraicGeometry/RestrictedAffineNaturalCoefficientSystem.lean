/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleMaps
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleTransitionLaws
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleConeNaturality
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleConeLeg
import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomologyMapFormula

/-! # Base change and the restricted coefficient complex system

Source: Stacks Project, Tag 09Z1 proof and Tag 0EZM.
(blueprint: lem-sbc-restricted-affine-natural-coefficient-system).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

attribute [local irreducible] cohomology upperStar rawAffineComplexPullback
  rightDerivedGlobalSections DerivedCategory.Q
  restrictedAffineSingleTransition

-- Use the raw-map formula without expanding the derived cohomology structures.
private theorem restricted_stage_map_heq {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (p : ℕ) (U : S.Etale) :
    ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      HEq (rawAffineComplexPullback (p : ℤ) ((restrictedAffineDiagram D U).map f)
          (restrictedAffineK D F U i) ≫
        (cohomology AddCommGrpCat.{v + 1} ((restrictedAffineDiagram D U).obj j)
          (p : ℤ)).map (DerivedCategory.Q.map (restrictedAffineSingleTransition D F φ U f)))
      (rawAffineRestrictedCohomologyMap (D.map f).left
        (D.obj i).hom (D.obj j).hom (Over.w (D.map f)) p
        (F i.unop) (F j.unop) (φ f.unop) U) := by
  intro i j f
  with_unfolding_all exact (rawAffineRestrictedCohomologyMap_formula (D.map f).left
    (D.obj i).hom (D.obj j).hom (Over.w (D.map f)) p
    (F i.unop) (F j.unop) (φ f.unop) U).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
/-- Stage-arrow naturality for the actual restricted single-complex transition.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-affine-natural-coefficient-system-stage).

Proof: The stage scheme map is rawAffineRestrictedMap, and the transition is the
single-complex comparison followed by singleFunctor applied to
rawAffineRestrictedCoefficient. These are exactly the factors in
rawAffineRestrictedCohomologyMap. The cohomology comparison for these concrete
complexes is the identity, so unfolding the definitions proves the equality. -/
theorem restricted_affine_stage_naturality {S : Scheme.{v}} {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (p : ℕ) (U : S.Etale) :
    ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      rawAffineComplexPullback (p : ℤ) ((restrictedAffineDiagram D U).map f)
          (restrictedAffineK D F U i) ≫
        (cohomology AddCommGrpCat.{v + 1} ((restrictedAffineDiagram D U).obj j)
          (p : ℤ)).map (DerivedCategory.Q.map (restrictedAffineSingleTransition D F φ U f)) =
      rawAffineRestrictedCohomologyMap (D.map f).left
        (D.obj i).hom (D.obj j).hom (Over.w (D.map f)) p
        (F i.unop) (F j.unop) (φ f.unop) U := by
  intro i j f
  exact eq_of_heq (restricted_stage_map_heq D F φ p U f)

-- Equality transports commute with a heterogeneously identified morphism.
private theorem eqToHom_naturality {C : Type*} [Category C]
    {A B A' B' : C} (eA : A = A') (eB : B = B')
    (f : A ⟶ B) (f' : A' ⟶ B') (hf : HEq f f') :
    eqToHom eA ≫ f' = f ≫ eqToHom eB := by
  cases eA
  cases eB
  cases hf
  simp

private theorem restricted_stage_cohomology_eq {S : Scheme.{v}} {I : Type v}
    [Preorder I] (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (p : ℕ) (U : S.Etale) (i : Iᵒᵖ) :
    rawAffineRestrictedCohomology (D.obj (op i.unop)).hom p (F i.unop) U =
      (cohomology AddCommGrpCat.{v + 1} ((restrictedAffineDiagram D U).obj i)
        (p : ℤ)).obj (DerivedCategory.Q.obj (restrictedAffineK D F U i)) := by
  rfl

private theorem restricted_limit_cohomology_eq {S : Scheme.{v}} {I : Type v}
    [Preorder I] (D : Iᵒᵖ ⥤ Over S) (c : Cone D)
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    [HasColimit H] (p : ℕ) (U : S.Etale) :
    rawAffineRestrictedCohomology c.pt.hom p (colimit H) U =
      (cohomology AddCommGrpCat.{v + 1} (restrictedAffineCone D c U).pt (p : ℤ)).obj
        (DerivedCategory.Q.obj (restrictedAffineL D c H U).pt) := by
  rfl

private noncomputable def restricted_stage_iso {S : Scheme.{v}} {I : Type v}
    [Preorder I] (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (p : ℕ) (U : S.Etale) (i : Iᵒᵖ) :
    rawAffineRestrictedCohomology (D.obj (op i.unop)).hom p (F i.unop) U ≅
      (cohomology AddCommGrpCat.{v + 1} ((restrictedAffineDiagram D U).obj i)
        (p : ℤ)).obj (DerivedCategory.Q.obj (restrictedAffineK D F U i)) :=
  eqToIso (restricted_stage_cohomology_eq D F p U i)

private noncomputable def restricted_limit_iso {S : Scheme.{v}} {I : Type v}
    [Preorder I] (D : Iᵒᵖ ⥤ Over S) (c : Cone D)
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    [HasColimit H] (p : ℕ) (U : S.Etale) :
    rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅
      (cohomology AddCommGrpCat.{v + 1} (restrictedAffineCone D c U).pt (p : ℤ)).obj
        (DerivedCategory.Q.obj (restrictedAffineL D c H U).pt) :=
  eqToIso (restricted_limit_cohomology_eq D c H p U)

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_concrete_single_coherence {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    (U : S.Etale)
    (D' : Iᵒᵖ ⥤ Scheme.{v}) (c' : Cone D')
    (K : ∀ i : Iᵒᵖ, CochainComplex
      (Sheaf (D'.obj i).smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex
      (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (hD' : D' = restrictedAffineDiagram D U)
    (hc' : HEq c' (restrictedAffineCone D c U))
    (hK : HEq K (restrictedAffineK D F U))
    (hG' : HEq G (restrictedAffineG D c H U)) :
    ∃
    (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv),
    HEq (@eG) (@restrictedAffineSingleConeIso _ _ _ D c F H eH U) ∧
    HEq (@ψ) (@restrictedAffineSingleTransition _ _ _ D F φ U) := by
  subst D'
  cases eq_of_heq hc'
  cases eq_of_heq hK
  cases eq_of_heq hG'
  obtain ⟨hid, hcomp⟩ := restrictedAffineSingleTransition_laws D F φ hφid hφcomp U
  refine ⟨restrictedAffineSingleTransition D F φ U, hid, hcomp,
    restrictedAffineSingleConeIso D c F H eH U,
    restrictedAffineSingleConeIso_naturality D c F φ H eH hH U, HEq.rfl, HEq.rfl⟩

attribute [local irreducible] rawAffineRestrictedCohomology

-- Assemble the existential with abstract witnesses, keeping their types folded.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
private theorem assemble_restricted_affine_system {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left]
    (D' : Iᵒᵖ ⥤ Scheme.{v})
    (c' : Cone D')
    (hc : IsLimit c')
    (compact : ∀ i : Iᵒᵖ, CompactSpace (D'.obj i))
    (quasiSeparated : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D'.obj i))
    (affine : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D'.map f))
    (K : ∀ i : Iᵒᵖ, CochainComplex (Sheaf (D'.obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ)
    (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (hbelow : ∀ (i : Iᵒᵖ) (n : ℤ), n < 0 → IsZero ((K i).X n))
    (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv)
    (L : Cocone G)
    (hL : IsColimit L)
    (hbelowL : ∀ n : ℤ, n < 0 → IsZero (L.pt.X n))
    (r : ∀ i : Iᵒᵖ,
      rawAffineRestrictedCohomology (D.obj (op i.unop)).hom p (F i.unop) U ≅
        (cohomology AddCommGrpCat.{v + 1} (D'.obj i) (p : ℤ)).obj
          (DerivedCategory.Q.obj (K i)))
    (rL : rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅
      (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).obj
        (DerivedCategory.Q.obj L.pt))
    (hnatural : (∀ i : Iᵒᵖ,
      (r i).hom ≫ rawAffineComplexPullback (p : ℤ) (c'.π.app i) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))) =
      rawAffineRestrictedCohomologyMap (c.π.app (op i.unop)).left
        (D.obj (op i.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop))) p
        (F i.unop) (colimit H) ((eH i.unop).inv ≫ colimit.ι H i.unop) U ≫ rL.hom) ∧
    (∀ {i j : I} (f : i ⟶ j),
      (r (op i)).hom ≫ rawAffineComplexPullback (p : ℤ) (D'.map f.op) (K (op i)) ≫
        (cohomology AddCommGrpCat.{v + 1} (D'.obj (op j)) (p : ℤ)).map
          (DerivedCategory.Q.map (ψ f.op)) =
      rawAffineRestrictedCohomologyMap (D.map f.op).left
        (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
        (F i) (F j) (φ f) U ≫ (r (op j)).hom)) :
    ∃
    (D' : Iᵒᵖ ⥤ Scheme.{v})
    (c' : Cone D')
    (hc : IsLimit c')
    (compact : ∀ i : Iᵒᵖ, CompactSpace (D'.obj i))
    (quasiSeparated : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D'.obj i))
    (affine : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D'.map f))
    (K : ∀ i : Iᵒᵖ, CochainComplex (Sheaf (D'.obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ)
    (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (hbelow : ∀ (i : Iᵒᵖ) (n : ℤ), n < 0 → IsZero ((K i).X n))
    (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv)
    (L : Cocone G)
    (hL : IsColimit L)
    (hbelowL : ∀ n : ℤ, n < 0 → IsZero (L.pt.X n))
    (r : ∀ i : Iᵒᵖ,
      rawAffineRestrictedCohomology (D.obj (op i.unop)).hom p (F i.unop) U ≅
        (cohomology AddCommGrpCat.{v + 1} (D'.obj i) (p : ℤ)).obj
          (DerivedCategory.Q.obj (K i)))
    (rL : rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅
      (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).obj
        (DerivedCategory.Q.obj L.pt)),
    (∀ i : Iᵒᵖ,
      (r i).hom ≫ rawAffineComplexPullback (p : ℤ) (c'.π.app i) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))) =
      rawAffineRestrictedCohomologyMap (c.π.app (op i.unop)).left
        (D.obj (op i.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop))) p
        (F i.unop) (colimit H) ((eH i.unop).inv ≫ colimit.ι H i.unop) U ≫ rL.hom) ∧
    (∀ {i j : I} (f : i ⟶ j),
      (r (op i)).hom ≫ rawAffineComplexPullback (p : ℤ) (D'.map f.op) (K (op i)) ≫
        (cohomology AddCommGrpCat.{v + 1} (D'.obj (op j)) (p : ℤ)).map
          (DerivedCategory.Q.map (ψ f.op)) =
      rawAffineRestrictedCohomologyMap (D.map f.op).left
        (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
        (F i) (F j) (φ f) U ≫ (r (op j)).hom) := by
  exact ⟨D', c', hc, compact, quasiSeparated, affine, K, @ψ, hidentity, hcomposition,
    hbelow, G, eG, hG, L, hL, hbelowL, r, rL, hnatural⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option linter.unusedVariables false in
/-- Construct the base-changed schemes and their degree-zero coefficient complexes,
including the coefficient colimit and its restriction comparisons.
Source: Stacks Project, Tag 09Z1 proof, base change to an affine etale object;
Tag 0EZM, canonical pullback maps.
(blueprint: lem-sbc-restricted-affine-natural-coefficient-system).

Proof: Use the schemes U ×_S D(i) with transition maps induced by the pullback
universal property, and the cone U ×_S c.pt. The universal property gives a
limiting cone. Base change preserves affine, quasi-compact and quasi-separated
morphisms. Since U is affine, the stage schemes are compact and quasi-separated.
Restrict F_i along the second projection and put the resulting sheaf into the
single complex in degree zero. Define its transitions by the two composition
comparisons of inverse image around each pullback square followed by the
restriction of phi. Naturality and associativity of upperStarComp transport
hphiid and hphicomp to the complex identity and composition equations.
The single complexes have zero terms below zero. Restrict H to U ×_S c.pt,
reindex by double opposite, and apply the single functor to obtain G. The
composition comparisons and eH give eG; their naturality and hH give hG.
Map the colimit cocone of H by restriction and the single functor. Restriction
is a left adjoint, hence preserves colimits, and single complexes preserve
colimits degreewise. This gives L and hL. Its vertex is a degree-zero single complex,
so its terms in negative degrees are zero, giving hbelowL. The stage complexes are exactly
those defining rawAffineRestrictedCohomology, giving r. Preservation of the
coefficient colimit identifies L.pt with the restriction of colimit H as a
single complex, giving rL after applying Q and cohomology. On a stage arrow,
the same two inverse-image composition comparisons
identify the transported coefficient map with rawAffineRestrictedCoefficient
for phi f. Applying Q and cohomology gives the stage transition equation.
On a cone leg,
the two inverse-image comparisons used in eG are precisely the ones defining
rawAffineRestrictedCoefficient. Naturality of the single-functor comparison
and of Q therefore identifies the coefficient complex map with the one in
rawAffineRestrictedCohomologyMap. Apply cohomology and compose with the fixed
rawAffineComplexPullback to obtain the displayed morphism equality.
No cohomology diagram, cocone or cohomology continuity is constructed here. -/
theorem exists_restricted_affine_natural_coefficient_system {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left] :
    ∃
    (D' : Iᵒᵖ ⥤ Scheme.{v})
    (c' : Cone D')
    (hc : IsLimit c')
    (compact : ∀ i : Iᵒᵖ, CompactSpace (D'.obj i))
    (quasiSeparated : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D'.obj i))
    (affine : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D'.map f))
    (K : ∀ i : Iᵒᵖ, CochainComplex (Sheaf (D'.obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ)
    (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (hbelow : ∀ (i : Iᵒᵖ) (n : ℤ), n < 0 → IsZero ((K i).X n))
    (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv)
    (L : Cocone G)
    (hL : IsColimit L)
    (hbelowL : ∀ n : ℤ, n < 0 → IsZero (L.pt.X n))
    (r : ∀ i : Iᵒᵖ,
      rawAffineRestrictedCohomology (D.obj (op i.unop)).hom p (F i.unop) U ≅
        (cohomology AddCommGrpCat.{v + 1} (D'.obj i) (p : ℤ)).obj
          (DerivedCategory.Q.obj (K i)))
    (rL : rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅
      (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).obj
        (DerivedCategory.Q.obj L.pt)),
    (∀ i : Iᵒᵖ,
      (r i).hom ≫ rawAffineComplexPullback (p : ℤ) (c'.π.app i) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))) =
      rawAffineRestrictedCohomologyMap (c.π.app (op i.unop)).left
        (D.obj (op i.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop))) p
        (F i.unop) (colimit H) ((eH i.unop).inv ≫ colimit.ι H i.unop) U ≫ rL.hom) ∧
    (∀ {i j : I} (f : i ⟶ j),
      (r (op i)).hom ≫ rawAffineComplexPullback (p : ℤ) (D'.map f.op) (K (op i)) ≫
        (cohomology AddCommGrpCat.{v + 1} (D'.obj (op j)) (p : ℤ)).map
          (DerivedCategory.Q.map (ψ f.op)) =
      rawAffineRestrictedCohomologyMap (D.map f.op).left
        (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
        (F i) (F j) (φ f) U ≫ (r (op j)).hom) := by
  let D' := restrictedAffineDiagram D U
  let c' := restrictedAffineCone D c U
  let K := restrictedAffineK D F U
  let G := restrictedAffineG D c H U
  let L := restrictedAffineL D c H U
  obtain ⟨ψ, hid, hcomp, eG, hG, heG, hψ⟩ :=
    exists_concrete_single_coherence D c F φ hφid hφcomp H eH hH U
      D' c' K G rfl HEq.rfl HEq.rfl HEq.rfl
  refine assemble_restricted_affine_system D c hc F φ hφid hφcomp H eH hH p U
    D' c' (restrictedAffineConeIsLimit D c hc U)
    (restrictedAffineDiagram_compact D U) (restrictedAffineDiagram_quasiSeparated D U)
    (fun i j f ↦ restrictedAffineDiagram_affine D U f)
    K @ψ hid hcomp ?_ G eG hG L (restrictedAffineLIsColimit D c H U) ?_
    (restricted_stage_iso D F p U) (restricted_limit_iso D c H p U) ⟨?_, ?_⟩
  · intro i n hn
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
        (F i.unop)) n (ne_of_lt hn)
  · intro n hn
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom c.pt.hom)).obj
        (colimit H)) n (ne_of_lt hn)
  · intro i
    change eqToHom (restricted_stage_cohomology_eq D F p U i) ≫ (_ ≫ _) =
      _ ≫ eqToHom (restricted_limit_cohomology_eq D c H p U)
    apply eqToHom_naturality
    rw [eq_of_heq heG, restrictedAffineSingleConeIso_inv_leg]
    with_unfolding_all exact (rawAffineRestrictedCohomologyMap_formula (c.π.app i).left
      (D.obj i).hom c.pt.hom (Over.w (c.π.app i)) p (F i.unop) (colimit H)
      ((eH i.unop).inv ≫ colimit.ι H i.unop) U)
  · intro i j f
    rw [eq_of_heq hψ]
    change eqToHom (restricted_stage_cohomology_eq D F p U (op i)) ≫ (_ ≫ _) =
      _ ≫ eqToHom (restricted_stage_cohomology_eq D F p U (op j))
    apply eqToHom_naturality
    exact (restricted_stage_map_heq D F φ p U f.op).symm

end AlgebraicGeometry.Etale
