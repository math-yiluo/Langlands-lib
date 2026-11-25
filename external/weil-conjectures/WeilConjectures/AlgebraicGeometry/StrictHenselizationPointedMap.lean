/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties

/-! # The pointed map from the neighbourhood colimit to its residue closure

Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-pointed-map).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The colimit comparison supplies the residue map and its algebraic properties.
Source: Stacks Project, Tag 04HX.

Proof: Choose an affine chart through the point. The neighbourhood/triple
comparison identifies the chosen small coordinate-ring colimit with the triple
colimit. Transport the triple theorem's surjection across this ring isomorphism.
The open immersion identifies the chart residue field with the residue field of
Y. After restriction of scalars along this field isomorphism, the chart's separable
closure is a separable closure of the latter field. The equivalence of separable
closures identifies it abstractly with the specified relative separable closure.
Compose the surjection with that equivalence. A surjective map from a local ring
to a field has kernel its maximal ideal. This existential assertion requires no
compatibility of the chosen equivalence with the embedding into Ω; it does not
assert that every such surjection is pointed.
(blueprint: lem-weil-pbc-strict-henselization-pointed-map-core) -/
theorem strictHenselizationPointedMap_core
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom)
    [IsLocalRing (Scheme.strictHenselization barY)] :
    ∃ ψ : Scheme.strictHenselization barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      Function.Surjective ψ ∧
      RingHom.ker ψ = IsLocalRing.maximalIdeal (Scheme.strictHenselization barY) := by
  classical
  have _hcompat := hΩ
  obtain ⟨A, i, hi, hx, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := barY (IsLocalRing.closedPoint Ω)) (U := ⊤) (by simp)
  let := hi
  have hrange : Set.range barY ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint Ω)] using hx
  let xU := IsOpenImmersion.lift i barY hrange
  have hfac : xU ≫ i = barY := IsOpenImmersion.lift_fac i barY hrange
  let p := (Scheme.SpecToEquivOfField Ω (Spec A) xU).1
  let F := (Spec A).residueField p
  let e := (Scheme.SpecToEquivOfField Ω (Spec A) xU).2
  let : Algebra F Ω := e.hom.toAlgebra
  let K := separableClosure F Ω
  obtain ⟨_, _, _, _, E, δ, _, cn, cu, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩, r, s, _, _⟩ :=
    Scheme.etale_local_ring_triples Y Ω A i xU
  obtain ⟨_, c, ⟨hc⟩, hlocal, ρ, ψ, _, _, hsurj, _, _, _, _, _⟩ :=
    Scheme.strictHenselization_triples A p K
  let Nall := (Scheme.pointSmallEtale (xU ≫ i)).fiber.Elements
  let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
  let D := (P.ι ⋙ Functor.Elements.π (Scheme.pointSmallEtale (xU ≫ i)).fiber ⋙
    Scheme.Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
  let : HasColimit D := ⟨⟨cn, hcn⟩⟩
  let incl := Scheme.strictHenselizationAffineInclusion (xU ≫ i)
  let : incl.IsEquivalence :=
    Scheme.strictHenselizationAffineInclusion_isEquivalence (xU ≫ i)
  let rep := (equivSmallModel.{v}
    (Scheme.strictHenselizationNeighbourhoods (xU ≫ i))).inverse
  let q := (rep ⋙ incl).op
  let cmp : Scheme.strictHenselization (xU ≫ i) ≅ cn.pt :=
    (Scheme.smallStrictHenselizationColimitIso (xU ≫ i)).symm ≪≫
      (HasColimit.isoOfEquivalence q.asEquivalence (Iso.refl _)) ≪≫
      colimit.isoColimitCocone ⟨cn, hcn⟩
  let ringIso : Scheme.strictHenselization barY ≅ c.pt :=
    eqToIso (congrArg Scheme.strictHenselization hfac.symm) ≪≫
      cmp ≪≫ s ≪≫ hct.coconePointUniqueUpToIso hc
  let G := Y.residueField (barY (IsLocalRing.closedPoint Ω))
  have hp : i p = barY (IsLocalRing.closedPoint Ω) :=
    congrArg (fun f : Spec (.of Ω) ⟶ Y ↦ f (IsLocalRing.closedPoint Ω)) hfac
  let b : G ≅ F := (Y.residueFieldCongr hp).symm ≪≫ asIso (i.residueFieldMap p)
  let : Algebra G K := ((algebraMap F K).comp b.hom.hom).toAlgebra
  have : Algebra.IsSeparable G K :=
    Algebra.IsSeparable.of_equiv_equiv b.symm.commRingCatIsoToRingEquiv
      (RingEquiv.refl K) (by
        apply RingHom.ext
        intro x
        change algebraMap F K (b.hom.hom (b.inv.hom x)) = algebraMap F K x
        exact congrArg (algebraMap F K)
          (ConcreteCategory.congr_hom b.inv_hom_id x))
  have : IsSepClosed K := IsSepClosure.sep_closed F
  have : IsSepClosure G K := ⟨inferInstance, inferInstance⟩
  let k := IsSepClosure.equiv G K (separableClosure G Ω)
  let φ := k.toRingHom.comp (ψ.comp ringIso.hom.hom)
  have hφ : Function.Surjective φ :=
    k.surjective.comp (hsurj.comp ringIso.commRingCatIsoToRingEquiv.surjective)
  exact ⟨φ, hφ, IsLocalRing.ker_eq_maximalIdeal φ hφ⟩


/-- The compatible residue maps give a surjection to the relative separable closure.
Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP
(blueprint: lem-weil-pbc-strict-henselization-pointed-map).

Proof: Choose an affine open containing the geometric point. By
`Scheme.etale_local_ring_triples`, the residue embedding of every neighbourhood
lying over that open lands in the relative separable closure. These embeddings
commute with pointed transition morphisms. The initial inclusion of these
neighbourhoods therefore gives a compatible family on the whole coordinate-ring
diagram, and its colimit map psi. Under the colimit comparison with the triple
diagram this is precisely the map psi of `Scheme.strictHenselization_triples`.
That theorem proves surjectivity and identifies its kernel with the maximal ideal.
Transport both assertions along the colimit comparison. The identification of the
chart residue field with the residue field of Y respects the given embedding into
Omega, by hOmega. The triple theorem's coprojection equation and the natural
isomorphism in `Scheme.etale_local_ring_triples` give the displayed pointed
factorization for neighbourhoods over the chart. Every neighbourhood receives a
pointed map from one over the chart. Cone naturality and the equation defining a
pointed map extend that factorization to every representative j.
-/
theorem strictHenselizationPointedMap
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom)
    [IsLocalRing (Scheme.strictHenselization barY)] :
    ∃ ψ : Scheme.strictHenselization barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      Function.Surjective ψ ∧
      RingHom.ker ψ = IsLocalRing.maximalIdeal (Scheme.strictHenselization barY) ∧
      ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
        Spec.map (CommRingCat.ofHom
          ((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              ψ)) ≫
          (Scheme.strictHenselizationAffineCone barY).π.app (Opposite.op (Opposite.op j)) ≫
          (Spec (Opposite.unop ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by
  let ψ := Scheme.strictHenselizationPointEvaluationToSep barY hΩ
  have hp := Scheme.strictHenselizationPointEvaluationToSep_surjective barY hΩ
  refine ⟨ψ, hp, IsLocalRing.ker_eq_maximalIdeal ψ hp, ?_⟩
  intro j
  have h := Scheme.strictHenselizationPointEvaluation_pointed barY j
  have he : ((IntermediateField.val
      (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        (Scheme.strictHenselizationPointEvaluationToSep barY hΩ)) =
      Scheme.strictHenselizationPointEvaluation barY := by
    ext a
    rfl
  rw [he]
  exact h


end AlgebraicGeometry
