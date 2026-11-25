/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleChartResidueTriplesFunctorConstruction
import WeilConjectures.AlgebraicGeometry.EtaleChartResidueTriplesFull
import WeilConjectures.AlgebraicGeometry.EtaleChartResidueTriplesEssentiallySurjective

/-!
# Equivalence between affine chart neighbourhoods and residue-field triples

Source: Stacks Project, proof of Tag 04HX and Remark Tag 04HT
(blueprint: lem-weil-pbc-etale-chart-residue-triples-equivalence).
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem affine_global_sections_faithful
    {C : Type*} [Category C] (G : C ⥤ Scheme.{v}) [G.Faithful]
    (h : ∀ c, IsAffine (G.obj c)) : (G.op ⋙ Scheme.Γ).Faithful where
  map_injective {c d} f g hfg := by
    apply Quiver.Hom.unop_inj
    apply G.map_injective
    have : IsAffine (G.obj c.unop) := h _
    apply ext_of_isAffine
    exact hfg


-- The legacy statement has unused diagram lets; keep its signature unchanged.
set_option linter.unusedVariables false in
/-- Source: Stacks Project, proof of Tag 04HX, first paragraph, and Remark Tag 04HT.
(blueprint: lem-weil-pbc-etale-chart-residue-triples-equivalence).

Proof: For an affine pointed neighbourhood V over the chart, choose its unique map
V → Spec A by cancellation of the open immersion. Identify V with Spec Γ(V).
The map A → Γ(V) is étale by cancellation and the affine spectrum anti-equivalence.
The point gives a prime q and a residue-field embedding into Ω. Restrict this
embedding to the relative separable closure using the assumed image containment.
The point-over-base equation implies that q lies over p and that the residue map
is compatible on A. These data define the triple, with B = Γ(V); the natural ring
identification gives δ and the two displayed compatibility equations.

A map between neighbourhoods induces the reverse map on global sections. Its
commutation with the geometric points is equivalent to commutation with B → K,
since K → Ω is injective. Cancellation of the chart inclusion identifies maps over
Y with maps over Spec A. The affine spectrum anti-equivalence consequently proves
full faithfulness, including identities and composition.

For a triple (B,q,φ), take V = Spec B with structure map Spec α followed by the
chart inclusion, and point Spec(B → κ(q) → K → Ω). Compatibility on A puts this
point over x. Its kernel is q, since both field embeddings are injective; uniqueness
of residue-field factorization recovers φ. ΓSpecIso identifies the reconstructed
ring with B, giving essential surjectivity. The fully faithful, essentially
surjective functor is an equivalence, with δ and the stated formulas unchanged. 
(blueprint: split-etale-chart-functor)
-/
/- The affine chart construction supplies an equivalence of the indexing categories.
The construction follows affine-spectrum duality and residue-point factorization.
The proof constructs object and morphism maps, proves full faithfulness by
cancellation over the open immersion, and proves essential surjectivity from the
spectrum of each triple. (blueprint: split-etale-chart-functor) -/
theorem etale_chart_residue_triples_equivalence_functor
    (Y : Scheme.{v}) (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let x := xU ≫ i
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let e := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := e.hom.toAlgebra
    let K := separableClosure F Ω
    let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
    let Nall := (pointSmallEtale x).fiber.Elements
    let P : ObjectProperty Nall := fun c ↦ IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    (∀ (c : NU) (z : c.obj.obj.1.left.residueField
          (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈ K) → Nonempty (NUᵒᵖ ≌ T)
 := by
  intros x p F e K χ Nall P N Q NU D DU T _DT h
  obtain ⟨H, δ, hδ⟩ := etale_chart_residue_triples_functor_construction
    Y Ω A i xU h
  have hfull := etale_chart_residue_triples_full Y Ω A i xU H δ hδ
  let G := Q.ι ⋙ P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
    Etale.forget Y ⋙ Over.forget Y
  have : G.Faithful := by dsimp [G]; infer_instance
  have : DU.Faithful := affine_global_sections_faithful G (fun c ↦ c.obj.property)
  have hfaithful : H.Faithful := Functor.Faithful.of_comp_iso (H := DU) δ.symm
  have hess := etale_chart_residue_triples_essentially_surjective Y Ω A i xU H δ hδ
  let : H.IsEquivalence := ⟨hfaithful, hfull, hess⟩
  exact ⟨H.asEquivalence⟩


/- The unused arbitrary-equivalence ring-compatibility assertion was retired.
Abstract equivalences need not preserve the pointed ring diagram.
The source's compatible equivalence is constructed in the theorem below.
 -/
/-- (blueprint: lem-weil-pbc-etale-chart-residue-triples-equivalence)
(blueprint: split-etale-chart-ring-iso) -/
theorem etale_chart_residue_triples_equivalence
    (Y : Scheme.{v}) (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let x := xU ≫ i
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let e := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := e.hom.toAlgebra
    let K := separableClosure F Ω
    let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
    let Nall := (pointSmallEtale x).fiber.Elements
    let P : ObjectProperty Nall := fun c ↦ IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    (∀ (c : NU) (z : c.obj.obj.1.left.residueField
          (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈ K) →
      ∃ (E : NUᵒᵖ ≌ T) (δ : DU ≅ E.functor ⋙ DT),
        (∀ c : NU,
          let t := E.functor.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))) := by
  intros x p F e K χ Nall P N Q NU D DU T _DT h
  obtain ⟨H, δ, hδ⟩ := etale_chart_residue_triples_functor_construction
    Y Ω A i xU h
  have hfull := etale_chart_residue_triples_full Y Ω A i xU H δ hδ
  let G := Q.ι ⋙ P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
    Etale.forget Y ⋙ Over.forget Y
  have : G.Faithful := by dsimp [G]; infer_instance
  have : DU.Faithful := affine_global_sections_faithful G (fun c ↦ c.obj.property)
  have hfaithful : H.Faithful := Functor.Faithful.of_comp_iso (H := DU) δ.symm
  have hess := etale_chart_residue_triples_essentially_surjective Y Ω A i xU H δ hδ
  let : H.IsEquivalence := ⟨hfaithful, hfull, hess⟩
  exact ⟨H.asEquivalence, δ, hδ⟩

end AlgebraicGeometry.Scheme
