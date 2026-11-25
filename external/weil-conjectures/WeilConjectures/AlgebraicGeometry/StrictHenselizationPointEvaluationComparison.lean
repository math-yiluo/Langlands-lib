/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples

/-! # Compatibility of the affine-chart colimit comparison

Source: Stacks Project, Tag 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-comparison).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem pointEvaluation_of_comp_specMap
    {X : Scheme.{v}} {Ω : Type v} [Field Ω]
    (s : Spec (.of Ω) ⟶ X) {B C : CommRingCat.{v}}
    (d : Γ(X, ⊤) ⟶ B) (g : B ⟶ C) (e : C ⟶ .of Ω)
    (h : s ≫ X.toSpecΓ = Spec.map e ≫ Spec.map g ≫ Spec.map d) :
    d ≫ g ≫ e = s.appTop ≫ (ΓSpecIso (.of Ω)).hom := by
  apply Spec.map_injective
  have hnat := Scheme.toSpecΓ_naturality s
  change s ≫ X.toSpecΓ = (Spec (.of Ω)).toSpecΓ ≫ Spec.map s.appTop at hnat
  rw [← SpecMap_ΓSpecIso_hom] at hnat
  simpa only [Spec.map_comp, Category.assoc] using h.symm.trans hnat

private theorem colimit_comparison_evaluation
    {J N T : Type*} [Category J] [Category N] [Category T]
    (q : J ⥤ N) [q.Final] {D : N ⥤ CommRingCat.{v}} {DT : T ⥤ CommRingCat.{v}}
    (E : J ⥤ T) (δ : q ⋙ D ⟶ E ⋙ DT)
    (cn : Cocone D) (hcn : IsColimit cn) (ct c : Cocone DT)
    (hct : IsColimit ct) (hc : IsColimit c) (t : cn.pt ≅ ct.pt)
    (ht : ∀ j, cn.ι.app (q.obj j) ≫ t.hom = δ.app j ≫ ct.ι.app (E.obj j))
    (ev : Cocone D) {K : CommRingCat.{v}} (ψ : c.pt ⟶ K) (e : K ⟶ ev.pt)
    (ρ : ∀ j, DT.obj j ⟶ K) (hψ : ∀ j, c.ι.app j ≫ ψ = ρ j)
    (hev : ∀ j, δ.app j ≫ ρ (E.obj j) ≫ e = ev.ι.app (q.obj j)) :
    t.hom ≫ (hct.coconePointUniqueUpToIso hc).hom ≫ ψ ≫ e = hcn.desc ev := by
  apply ((Functor.Final.isColimitWhiskerEquiv q cn).symm hcn).hom_ext
  intro j
  change cn.ι.app (q.obj j) ≫ _ = cn.ι.app (q.obj j) ≫ hcn.desc ev
  rw [← Category.assoc (cn.ι.app _) t.hom, ht]
  simp only [Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
  rw [← Category.assoc (c.ι.app _) ψ, hψ, hev, hcn.fac]

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate-ring colimit comparison preserves geometric evaluation.
Source: Stacks Project, Tag 04HX, and `etale_local_ring_triples`.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-comparison)

Proof: the ring-written affine pointed neighbourhoods are equivalent to the full
subcategory of affine pointed neighbourhoods, by
`strictHenselizationAffineInclusion_isEquivalence`. Compose this with the small-model
equivalence. Restrict to neighbourhoods over the chosen chart; the inclusion is
initial by `etale_local_ring_triples`, and its opposite is final. That theorem's
natural diagram isomorphism then identifies the ring diagram with the residue-triple
diagram. Transport the colimit along these functors and identify the resulting
colimit cocone with `c` using `hc`. All comparison maps commute with coprojections.
On a neighbourhood over the chart, the pointed embedding equation in
`etale_local_ring_triples`, after applying global sections and the affine spectrum
adjunction, identifies evaluation into Ω with the triple residue map followed by
inclusion into Ω. The hypothesis `hψ` identifies that map with ψ on each
coprojection. These equations therefore agree on the chart-neighbourhood diagram.
Finality extends equality to its whole colimit; the small-model and affine
comparisons give the displayed equality for every element of the chosen colimit.
This comparison does not assert or assume surjectivity of ψ. -/
theorem strictHenselizationPointEvaluation_comparison
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let emb := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := emb.hom.toAlgebra
    let K := separableClosure F Ω
    ∀ (c : Cocone (etaleResidueTriplesRingDiagram A p K
        (CommRingCat.ofHom (algebraMap F K)))) (_hc : IsColimit c)
      (ψ : c.pt →+* K),
      (∀ t, ψ.comp (c.ι.app t).hom =
        ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) →
      ∃ e : strictHenselization (xU ≫ i) ≅ c.pt,
        ∀ a, (ψ (e.hom a) : Ω) = strictHenselizationPointEvaluation (xU ≫ i) a := by
  classical
  dsimp only
  intro c hc ψ hψ
  let x := xU ≫ i
  let p := (SpecToEquivOfField Ω (Spec A) xU).1
  let F := (Spec A).residueField p
  let emb := (SpecToEquivOfField Ω (Spec A) xU).2
  let : Algebra F Ω := emb.hom.toAlgebra
  let K := separableClosure F Ω
  obtain ⟨_, hinitial, _, _, E, δ, hδ, cn, cu, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩,
      r, t, _, ht⟩ := etale_local_ring_triples Y Ω A i xU
  let Nall := (pointSmallEtale x).fiber.Elements
  let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
  let Q : ObjectProperty P.FullSubcategory := fun n ↦
    ∃ g : n.obj.1.left ⟶ Spec A, g ≫ i = n.obj.1.hom
  let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
    Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
  let incl := strictHenselizationAffineInclusion x
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence x
  let rep := (equivSmallModel.{v} (strictHenselizationNeighbourhoods x)).inverse
  let q := (rep ⋙ incl).op
  let cmp : strictHenselization x ≅ cn.pt :=
    (isColimitSmallStrictHenselizationCocone x).coconePointUniqueUpToIso
      ((Functor.Final.isColimitWhiskerEquiv q cn).symm hcn)
  let k := hct.coconePointUniqueUpToIso hc
  let ringIso : strictHenselization x ≅ c.pt := cmp ≪≫ t ≪≫ k
  let ev : Cocone D := {
    pt := .of Ω
    ι := {
      app := fun n ↦ n.unop.obj.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom
      naturality := by
        intro n m f
        have h := congrArg Over.Hom.left f.unop.hom.map_val
        change m.unop.obj.2.left ≫ f.unop.hom.1.left = n.unop.obj.2.left at h
        change f.unop.hom.1.left.appTop ≫
          m.unop.obj.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom = _
        rw [← Category.assoc, ← Hom.comp_appTop, h]
        simp } }
  let m := hcn.desc ev
  have hcmp (j) : (smallStrictHenselizationCocone x).ι.app j ≫ cmp.hom =
      cn.ι.app (q.obj j) := by
    exact (isColimitSmallStrictHenselizationCocone x).comp_coconePointUniqueUpToIso_hom
      ((Functor.Final.isColimitWhiskerEquiv q cn).symm hcn) j
  have hsmall : cmp.hom ≫ m = CommRingCat.ofHom
      (strictHenselizationPointEvaluation x) := by
    apply (isColimitSmallStrictHenselizationCocone x).hom_ext
    intro j
    rw [← Category.assoc, hcmp, hcn.fac ev]
    exact ((isColimitSmallStrictHenselizationCocone x).fac
      (strictHenselizationPointCocone x) j).symm
  let := hinitial
  have hchart : t.hom ≫ k.hom ≫ CommRingCat.ofHom ψ ≫
      CommRingCat.ofHom K.subtype = m := by
    apply colimit_comparison_evaluation Q.ι.op E.functor δ.hom cn hcn ct c hct hc t ht ev
      (CommRingCat.ofHom ψ) (CommRingCat.ofHom K.subtype)
      (fun z ↦ (ΓSpecIso z.B).inv ≫ (Spec z.B).Γevaluation z.q ≫ z.φ)
      (fun z ↦ CommRingCat.hom_ext (hψ z))
    intro d
    exact pointEvaluation_of_comp_specMap d.unop.obj.obj.2.left (δ.hom.app d)
      ((ΓSpecIso (E.functor.obj d).B).inv ≫
        (Spec (E.functor.obj d).B).Γevaluation (E.functor.obj d).q ≫
        (E.functor.obj d).φ) (CommRingCat.ofHom K.subtype) (hδ d.unop).2
  refine ⟨ringIso, ?_⟩
  have hmap : ringIso.hom ≫ CommRingCat.ofHom ψ ≫ CommRingCat.ofHom K.subtype =
      CommRingCat.ofHom (strictHenselizationPointEvaluation x) := by
    change cmp.hom ≫ t.hom ≫ k.hom ≫ CommRingCat.ofHom ψ ≫
      CommRingCat.ofHom K.subtype = _
    rw [hchart, hsmall]
  intro a
  exact ConcreteCategory.congr_hom hmap a

end AlgebraicGeometry.Scheme
