/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # The maximal ideal in an affine chart of the strict henselization

Source: Stacks Project, Tags 04HX, 04GW and 04GP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- Comparing the nested chart, triple and small-model diagrams requires extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- In any affine open chart through which the geometric point factors, the structural
ring map extends the distinguished prime to the maximal ideal of the strict henselization.
Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-chart-maximal-ideal)

Proof: restrict affine pointed neighbourhoods to those over the chart. This inclusion
is initial by the shrinking argument in Tag 04HX. Identify its opposite with the category
of etale residue triples over R, pointed in the relative separable closure of the residue
field of xR in Ω. The residue embeddings land in this closure because etale residue
extensions are finite separable. The coordinate-ring diagram comparison respects the
R-map on each object. Initiality, this diagram comparison, and the small representative
comparison give a canonical ring isomorphism from the chosen strict-henselization ring
to the triple colimit. Tags 04GW and 04GP say the latter is local with maximal ideal equal
to the extension of the distinguished prime. Transport its local-ring structure and
its R-map through this isomorphism. Ring isomorphisms carry maximal ideals and extended
ideals to the corresponding ideals, giving the displayed equality. On the chart
neighbourhood the coprojection defines the structure morphism; the comparison preserves
that coprojection, so the transported R-map has spectrum followed by i equal to the
chosen structural morphism. The assertion includes the field case; the triple colimit
has a field quotient, so it is nonzero even when a chart ring has zero divisors. -/
theorem strictHenselization_chart_maximalIdeal
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    ∃ (_ : IsLocalRing (strictHenselization (xR ≫ i)))
      (ρ : R ⟶ strictHenselization (xR ≫ i)),
      Spec.map ρ ≫ i = strictLocalizationToBase (xR ≫ i) ∧
      IsLocalRing.maximalIdeal (strictHenselization (xR ≫ i)) =
        (xR (IsLocalRing.closedPoint Ω)).asIdeal.map ρ.hom  := by
  classical
  let s := xR ≫ i
  let p := (SpecToEquivOfField Ω (Spec R) xR).1
  let F := (Spec R).residueField p
  let e := (SpecToEquivOfField Ω (Spec R) xR).2
  let : Algebra F Ω := e.hom.toAlgebra
  let K := separableClosure F Ω
  obtain ⟨_, _, _, _, E, δ, hδ, cn, cu, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩, r, t, _, ht⟩ :=
    etale_local_ring_triples S Ω R i xR
  obtain ⟨_, c, ⟨hc⟩, hlocal, ρ, ψ, hρ, _, _, hm, hker, _, _, _⟩ :=
    strictHenselization_triples R p K
  let := hlocal
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
  let ringEquiv := ringIso.symm.commRingCatIsoToRingEquiv
  let := ringEquiv.isLocalRing
  refine ⟨inferInstance, ρ ≫ ringIso.inv, ?_, ?_⟩
  · let a := AffineEtale.mk i
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
  · rw [← IsLocalRing.map_ringEquiv_maximalIdeal ringEquiv, hm, hker]
    change Ideal.map ringEquiv.toRingHom (Ideal.map ρ.hom p.asIdeal) = _
    rw [Ideal.map_map]
    rfl

end AlgebraicGeometry.Scheme
