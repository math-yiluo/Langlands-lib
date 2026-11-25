/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties

/-! # The residue identification of the coordinate-ring strict henselization

Source: Stacks Project, Tag 04HX and Definition 03PS
(blueprint: lem-weil-pbc-strict-henselization-functoriality).

This is clause (1) of `lem-weil-pbc-strict-henselization-functoriality` for the
coordinate-ring model `Scheme.strictHenselizationRing` of the strict henselization,
whose canonical maps are the legs of `Scheme.strictHenselizationCone` and the structural
map `Scheme.strictHenselizationStructuralMap`. The pointed residue map is transported from
the point evaluation on `Scheme.strictHenselization` along the canonical colimit comparison
`Scheme.smallStrictHenselizationColimitIso`.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The pointed surjection from the coordinate-ring colimit onto the relative separable
closure: the point evaluation on `Scheme.strictHenselization`, precomposed with the canonical
colimit comparison. Its kernel is the maximal ideal, and followed by the inclusion into Ω it
recovers every chosen pointed neighbourhood through the legs of
`Scheme.strictHenselizationCone`.
Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-pointed-map). -/
private theorem strictHenselizationRingPointedMap
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom)
    [IsLocalRing (Scheme.strictHenselizationRing barY)] :
    ∃ ψ : Scheme.strictHenselizationRing barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      Function.Surjective ψ ∧
      RingHom.ker ψ = IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing barY) ∧
      ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
        Spec.map (CommRingCat.ofHom
          ((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              ψ)) ≫
          (Scheme.strictHenselizationCone barY).π.app (Opposite.op (Opposite.op j)) ≫
          (Spec (Opposite.unop ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by
  let e := Scheme.smallStrictHenselizationColimitIso barY
  let ψ : Scheme.strictHenselizationRing barY →+*
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.strictHenselizationPointEvaluationToSep barY hΩ).comp e.hom.hom
  have hp : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Scheme.strictHenselizationPointEvaluationToSep_surjective barY hΩ y
    refine ⟨e.inv.hom x, ?_⟩
    change Scheme.strictHenselizationPointEvaluationToSep barY hΩ (e.hom.hom (e.inv.hom x)) = _
    rw [← CommRingCat.comp_apply, e.inv_hom_id, CommRingCat.id_apply]
  refine ⟨ψ, hp, IsLocalRing.ker_eq_maximalIdeal ψ hp, fun j ↦ ?_⟩
  have hleg : colimit.ι (Scheme.strictHenselizationAffineDiagram barY) (Opposite.op j) ≫
      e.hom = (Scheme.smallStrictHenselizationCocone barY).ι.app (Opposite.op j) := by
    let : HasColimit (Scheme.strictHenselizationDiagram barY) := inferInstance
    let incl := Scheme.strictHenselizationAffineInclusion barY
    let : incl.IsEquivalence := Scheme.strictHenselizationAffineInclusion_isEquivalence barY
    let r := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY)).inverse ⋙ incl
    exact Functor.Final.ι_colimitIso_hom r.op (Scheme.strictHenselizationDiagram barY)
      (Opposite.op j)
  have hval : CommRingCat.ofHom ((IntermediateField.val
      (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        ψ) = e.hom ≫ CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation barY) := by
    ext a
    rfl
  have h := Scheme.strictHenselizationPointEvaluation_pointed barY j
  rw [hval]
  change Spec.map (e.hom ≫ CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation barY)) ≫
    Spec.map (colimit.ι (Scheme.strictHenselizationAffineDiagram barY) (Opposite.op j)) ≫ _ = _
  rw [← Spec.map_comp_assoc, ← Category.assoc, hleg, Spec.map_comp_assoc]
  exact h

/-- The strictly henselian ring, canonical base map, and unique pointed residue
identification of clause (1), for the coordinate-ring model
`Scheme.strictHenselizationRing`. The factorization condition forces the residue
identification to respect the base residue field; using ring equivalences therefore
also states uniqueness as an equivalence of base-residue-field algebras.
Source: Stacks Project, Tag 04HX and Definition 03PS
(blueprint: lem-weil-pbc-strict-henselization-functoriality).

Proof: by `strictHenselizationLocalStructure` the colimit ring $C$ is a strictly
henselian local ring. The pointed map of the colimit, the point evaluation $\psi$ to the
relative separable closure $\kappa(\bar x)$, is surjective with kernel the maximal ideal,
so it induces an isomorphism $\sigma : C/\mathfrak m_C \to \kappa(\bar x)$. Let
$\lambda : \operatorname{Spec}\Omega \to \operatorname{Spec} C$ be given by
$C \to C/\mathfrak m_C \to \kappa(\bar x) \subset \Omega$. By construction of $\psi$ every
leg $c_V$ of the limit cone satisfies $c_V \circ \lambda = \bar v$; composing with the
structure morphism of any neighbourhood gives $j_Y \circ \lambda = \bar x$, hence $j_Y$ maps
the closed point (the image of $\lambda$) to $y$. Since $\Omega$ is algebraically closed,
$\kappa(\bar x)$ is a separable closure of $\kappa(y)$, hence separably closed. Uniqueness:
another $\sigma'$ with the same factorizations gives $\lambda_{\sigma'}$ with the same
composites with all legs of the limit cone, so $\lambda_{\sigma'} = \lambda$; then the two
ring maps $C \to \Omega$ agree, and since the residue map is surjective and the inclusion
into $\Omega$ is injective, $\sigma' = \sigma$. -/
theorem strictHenselizationRingResidue
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom) :
    ∃ (_ : IsLocalRing (Scheme.strictHenselizationRing barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselizationRing barY) ∧
      Scheme.strictHenselizationStructuralMap barY
          (IsLocalRing.closedPoint (Scheme.strictHenselizationRing barY)) =
        barY (IsLocalRing.closedPoint Ω) ∧
      IsSepClosed (separableClosure
        (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω) ∧
      ∃! σ : IsLocalRing.ResidueField (Scheme.strictHenselizationRing barY) ≃+*
          separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
        (∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
          Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σ.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselizationRing barY)))) ≫
            (Scheme.strictHenselizationCone barY).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
            ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left) ∧
        Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σ.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselizationRing barY)))) ≫
          Scheme.strictHenselizationStructuralMap barY = barY := by
  classical
  obtain ⟨hlocal, hstrict⟩ := strictHenselizationLocalStructure barY
  let := hlocal
  obtain ⟨ψ, hsurj, hker, hpoint⟩ := strictHenselizationRingPointedMap barY hΩ
  let σ : IsLocalRing.ResidueField (Scheme.strictHenselizationRing barY) ≃+*
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hσ : σ.toRingHom.comp (IsLocalRing.residue _) = ψ := by
    apply RingHom.ext
    intro r
    change (RingHom.quotientKerEquivOfSurjective hsurj)
      (Ideal.quotEquivOfEq hker.symm (IsLocalRing.residue _ r)) = ψ r
    simpa only [IsLocalRing.residue, Ideal.quotEquivOfEq_mk] using!
      RingHom.quotientKerEquivOfSurjective_apply_mk hsurj r
  let ι := (IntermediateField.val
    (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom
  let liftY := Spec.map (CommRingCat.ofHom ((ι.comp σ.toRingHom).comp
    (IsLocalRing.residue (Scheme.strictHenselizationRing barY))))
  have hliftYpoint : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
      liftY ≫ (Scheme.strictHenselizationCone barY).π.app (Opposite.op (Opposite.op j)) ≫
        (Spec (Opposite.unop ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
      ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by
    simpa only [liftY, RingHom.comp_assoc, hσ] using hpoint
  have hliftYbase : liftY ≫ Scheme.strictHenselizationStructuralMap barY = barY := by
    have hc := (Scheme.strictHenselization_properties barY).2.1
    let := hc
    obtain ⟨j⟩ := IsCofiltered.nonempty
      (C := SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY))
    have hstruct := (Scheme.exists_strictHenselizationStructuralMap barY).choose_spec j
    change _ = Scheme.strictHenselizationStructuralMap barY at hstruct
    rw [← hstruct]
    rw [← Scheme.isoSpec_Spec_inv]
    simpa only [Category.assoc] using!
      (congrArg (fun f ↦ f ≫ ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1).hom)
        (hliftYpoint j)).trans (CategoryTheory.Over.w
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2)
  have hliftYclosed : liftY (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (Scheme.strictHenselizationRing barY) := by
    change PrimeSpectrum.comap ((ι.comp σ.toRingHom).comp
      (IsLocalRing.residue (Scheme.strictHenselizationRing barY))) _ = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  refine ⟨hlocal, hstrict, ?_, IsSepClosure.sep_closed
    (Y.residueField (barY (IsLocalRing.closedPoint Ω))), σ, ⟨hliftYpoint, hliftYbase⟩, ?_⟩
  · have he := congrArg (fun f : Spec (.of Ω) ⟶ Y ↦
      f (IsLocalRing.closedPoint Ω)) hliftYbase
    simpa only [Scheme.Hom.comp_apply, hliftYclosed] using! he
  · intro σ' hσ'
    let liftY' := Spec.map (CommRingCat.ofHom ((ι.comp σ'.toRingHom).comp
      (IsLocalRing.residue (Scheme.strictHenselizationRing barY))))
    have he : liftY' = liftY := by
      obtain ⟨hl⟩ := (Scheme.strictHenselization_properties barY).2.2
      apply hl.hom_ext
      intro j
      apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj
          j.unop.unop).1.left)).isoSpec.inv).1
      exact (hσ'.1 j.unop.unop).trans (hliftYpoint j.unop.unop).symm
    have he' := Spec.map_injective he
    ext z
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective
      (R := Scheme.strictHenselizationRing barY) z
    exact ConcreteCategory.congr_hom he' r

end AlgebraicGeometry
