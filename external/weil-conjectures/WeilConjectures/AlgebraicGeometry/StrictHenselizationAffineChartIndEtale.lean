/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.EtaleResidueTriplesColimit

/-! # The strict henselization is ind-etale over an affine chart

Source: Stacks Project, Tag 04HX, proof, and Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-affine-chart-ind-etale).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The ring of a strict henselization is ind-etale over any affine neighbourhood
of its geometric point, with the algebra structure specified by its structural map.
Source: Stacks Project, Tag 04HX, proof, using Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-affine-chart-ind-etale).

Proof: Factor the geometric point through the open immersion i. Restrict affine
pointed etale neighbourhoods to those whose structural map factors through i.
`etale_local_ring_triples` proves this restriction cofinal and identifies its
coordinate-ring diagram with the etale residue-triples diagram. The small model
in `strictHenselizationDiagram` is equivalent to the affine pointed-neighbourhood
category by `strictHenselizationAffineInclusion_isEquivalence`.
`strictHenselization_triples` gives filteredness; take a small representative
category of triples. Regard each triple as an R-algebra via its structural map.
Every transition is R-linear. The ring colimit therefore has its compatible
R-algebra structure and is also the colimit in CommAlgCat R: an R-linear cocone
induces a ring map from the ring colimit, and its agreement with R is checked on
one stage; uniqueness follows from ring-colimit uniqueness. Cofinality identifies
this colimit with strictHenselization s. The equations defining
strictLocalizationToBase identify the induced R-map with the map a after
transport through e. Indeed their spectra agree after composing with i, which is
mono, and full faithfulness of Spec then gives equality of ring maps. Transport
the algebra colimit along this R-algebra isomorphism to A. This is exactly the
filtered etale colimit presentation required by Algebra.IndEtale.

Edge cases: no local or reduced hypothesis on R is used. The chart containing
the specified geometric point is nonempty, and the pointed-neighbourhood category
has an object, so no empty filtered diagram is asserted. The identification e is
arbitrary; the equation ha fixes the transported R-algebra structure. -/
theorem strictHenselization_indEtale_of_affine_chart
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    (s : Spec (.of Ω) ⟶ S) (R : CommRingCat.{u})
    (i : Spec R ⟶ S) [IsOpenImmersion i]
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i)
    (e : Spec (.of A) ≅ strictLocalization s)
    (a : R →+* A)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ i =
      e.hom ≫ strictLocalizationToBase s) :
    letI : Algebra R A := a.toAlgebra
    Algebra.IndEtale R A :=
  open CategoryTheory.Limits Opposite in
  set_option backward.isDefEq.respectTransparency false in
  by
    classical
    -- The spectrum of a field has one point, so the point factors through the chart.
    have hrange : Set.range s ⊆ Set.range i := by
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
      simpa only [hx] using hs
    obtain ⟨xR, hxR⟩ : ∃ xR : Spec (.of Ω) ⟶ Spec R, xR ≫ i = s :=
      ⟨IsOpenImmersion.lift i s hrange, IsOpenImmersion.lift_fac i s hrange⟩
    subst s
    let s := xR ≫ i
    let p := (SpecToEquivOfField Ω (Spec R) xR).1
    let F := (Spec R).residueField p
    let ε := (SpecToEquivOfField Ω (Spec R) xR).2
    let : Algebra F Ω := ε.hom.toAlgebra
    let K := separableClosure F Ω
    obtain ⟨_, _, _, _, E, δ, hδ, cn, _, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩, _, t, _, ht⟩ :=
      etale_local_ring_triples S Ω R i xR
    obtain ⟨hf, c, ⟨hc⟩, ρ, _, hρ, _⟩ :=
      etaleResidueTriples_filtered_colimit R p K
    -- Compare the small neighbourhood colimit with the filtered triple colimit.
    let Nall := (pointSmallEtale s).fiber.Elements
    let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
    let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale s).fiber ⋙
      Etale.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ
    let : HasColimit D := ⟨⟨cn, hcn⟩⟩
    let incl := strictHenselizationAffineInclusion s
    let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence s
    let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
    let q := (rep ⋙ incl).op
    let cmp : strictHenselization s ≅ cn.pt :=
      (isColimitSmallStrictHenselizationCocone s).coconePointUniqueUpToIso
        ((Functor.Final.isColimitWhiskerEquiv q cn).symm hcn)
    let k := hct.coconePointUniqueUpToIso hc
    let ringIso : strictHenselization s ≅ c.pt := cmp ≪≫ t ≪≫ k
    -- The chart object identifies the transported R-map with the structural map.
    have hstrmap : Spec.map (ρ ≫ ringIso.inv) ≫ i =
        strictLocalizationToBase s := by
      let a := AffineEtale.mk i
      let y : (pointSmallEtale s).fiber.obj ((AffineEtale.Spec S).obj a) :=
        Over.homMk xR rfl
      let n := (AffineEtale.Spec S ⋙ (pointSmallEtale s).fiber).elementsMk a y
      let j := rep.objPreimage n
      let η := rep.objObjPreimageIso n
      let g : ((incl.obj (rep.obj j)).obj.1.left) ⟶ Spec R :=
        (AffineEtale.Spec S).map η.hom.1 |>.1.left
      have hg : g ≫ i = (incl.obj (rep.obj j)).obj.1.hom := η.hom.1.w
      let b := incl.obj (rep.obj j)
      let Q : ObjectProperty P.FullSubcategory := fun z ↦
        ∃ g : z.obj.1.left ⟶ Spec R, g ≫ i = z.obj.1.hom
      let d : Q.FullSubcategory := ⟨b, ⟨g, hg⟩⟩
      have hcmp : (smallStrictHenselizationCocone s).ι.app (op j) ≫ cmp.hom =
          cn.ι.app (op b) := by
          exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
      have htrip := (hδ d).1 g hg
      have hbase : (ΓSpecIso R).inv ≫ g.appTop ≫ δ.hom.app (op d) ≫
          c.ι.app (E.functor.obj (op d)) = ρ := by
        simpa only [Category.assoc] using
          (congrArg (fun f ↦ f ≫ c.ι.app (E.functor.obj (op d))) htrip).trans (hρ _)
      have hleg : cn.ι.app (op b) ≫ t.hom ≫ k.hom =
          δ.hom.app (op d) ≫ c.ι.app (E.functor.obj (op d)) := by
        calc
          _ = (δ.hom.app (op d) ≫ ct.ι.app (E.functor.obj (op d))) ≫ k.hom :=
            congrArg (fun f ↦ f ≫ k.hom) (ht (op d))
          _ = _ := by
            simp only [Category.assoc, k, IsColimit.comp_coconePointUniqueUpToIso_hom]
      have hring : (ΓSpecIso R).inv ≫ g.appTop ≫
          (smallStrictHenselizationCocone s).ι.app (op j) = ρ ≫ ringIso.inv := by
        apply (cancel_mono ringIso.hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        change (ΓSpecIso R).inv ≫ g.appTop ≫
          (smallStrictHenselizationCocone s).ι.app (op j) ≫ cmp.hom ≫ t.hom ≫ k.hom = ρ
        rw [← Category.assoc _ cmp.hom, hcmp, hleg]
        exact hbase
      let : IsAffine b.obj.1.left := b.property
      have hgSpec : Spec.map g.appTop ≫ Spec.map (ΓSpecIso R).inv =
          Spec.map (ΓSpecIso (rep.obj j).1.left.unop).inv ≫ g := by
        have hh := isoSpec_inv_naturality g
        change Spec.map g.appTop ≫ (Spec R).isoSpec.inv =
          (Spec (rep.obj j).1.left.unop).isoSpec.inv ≫ g at hh
        simpa only [isoSpec_Spec_inv] using hh
      have hstr := strictHenselizationStructuralMap_eq s j
      change Spec.map ((smallStrictHenselizationCocone s).ι.app (op j)) ≫
        Spec.map (ΓSpecIso (rep.obj j).1.left.unop).inv ≫ b.obj.1.hom =
        strictLocalizationToBase s at hstr
      calc
        Spec.map (ρ ≫ ringIso.inv) ≫ i =
            Spec.map ((smallStrictHenselizationCocone s).ι.app (op j)) ≫
              Spec.map g.appTop ≫ Spec.map (ΓSpecIso R).inv ≫ i := by
          simpa only [Spec.map_comp, Category.assoc] using
            congrArg (fun f ↦ Spec.map f ≫ i) hring.symm
        _ = Spec.map ((smallStrictHenselizationCocone s).ι.app (op j)) ≫
            Spec.map (ΓSpecIso (rep.obj j).1.left.unop).inv ≫ b.obj.1.hom := by
          rw [← Category.assoc (Spec.map g.appTop), hgSpec, Category.assoc, hg]
        _ = _ := hstr
    -- Shrink the chart category using its equivalence with affine neighbourhoods.
    have : IsFiltered (EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap F K))) :=
      hf
    let Q : ObjectProperty P.FullSubcategory := fun z ↦
      ∃ g : z.obj.1.left ⟶ Spec R, g ≫ i = z.obj.1.hom
    have : EssentiallySmall.{u} P.FullSubcategory :=
      essentiallySmall_of_fully_faithful
        (incl.asEquivalence.inverse ⋙
          (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).functor)
    have : EssentiallySmall.{u} Q.FullSubcategory :=
      essentiallySmall_of_fully_faithful Q.ι
    have : EssentiallySmall.{u} (Q.FullSubcategory)ᵒᵖ := inferInstance
    let H := (equivSmallModel.{u} (Q.FullSubcategory)ᵒᵖ).inverse ⋙ E.functor
    have : IsFiltered (SmallModel.{u} (Q.FullSubcategory)ᵒᵖ) :=
      IsFiltered.of_equivalence
        ((equivSmallModel.{u} (Q.FullSubcategory)ᵒᵖ).symm.trans E).symm
    let ca := c.whisker H
    have hca : IsColimit ca := (Functor.Final.isColimitWhiskerEquiv H c).symm hc
    -- Transport the ring colimit to A along the given spectrum isomorphism.
    let eRing : strictHenselization s ≅ CommRingCat.of A :=
      { hom := Spec.preimage e.hom
        inv := Spec.preimage e.inv
        hom_inv_id := by
          apply Spec.map_injective
          simp
        inv_hom_id := by
          apply Spec.map_injective
          simp }
    let isoA : c.pt ≅ CommRingCat.of A := ringIso.symm ≪≫ eRing
    let caA := ca.extend isoA.hom
    have hcaA : IsColimit caA := hca.ofIsoColimit (ca.extendIso isoA)
    let α : (Functor.const _).obj R ⟶ H ⋙
        etaleResidueTriplesRingDiagram R p K
          (CommRingCat.ofHom (algebraMap F K)) :=
      { app := fun j ↦ (H.obj j).α
        naturality := fun j k f ↦ by
          have h := congrArg Over.Hom.left (Under.w (H.map f).hom)
          change (H.obj j).α ≫ (H.map f).hom.right.left = (H.obj k).α at h
          change (𝟙 R) ≫ (H.obj k).α = (H.obj j).α ≫ (H.map f).hom.right.left
          simpa only [Category.id_comp] using h.symm }
    -- Cancellation through the open immersion fixes the algebra structure.
    have hmap : ρ ≫ isoA.hom = CommRingCat.ofHom a := by
      apply Spec.map_injective
      apply (cancel_mono i).1
      simp only [isoA, Iso.trans_hom, Iso.symm_hom, Spec.map_comp,
        Category.assoc, eRing, Spec.map_preimage]
      rw [← Category.assoc (Spec.map ringIso.inv), ← Spec.map_comp, hstrmap]
      exact ha.symm
    -- The resulting compatible filtered etale presentation is exactly ind-etaleness.
    change a.IndEtale
    apply (RingHom.IndEtale.iff_exists (CommRingCat.ofHom a)).2
    refine ⟨_, inferInstance, inferInstance, H ⋙
      etaleResidueTriplesRingDiagram R p K
        (CommRingCat.ofHom (algebraMap F K)), α, caA.ι, hcaA, ?_⟩
    intro j
    refine ⟨?_, ?_⟩
    · have := (H.obj j).etale
      exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 inferInstance
    · change (H.obj j).α ≫ c.ι.app (H.obj j) ≫ isoA.hom = _
      rw [← Category.assoc, hρ, hmap]

end AlgebraicGeometry.Scheme
