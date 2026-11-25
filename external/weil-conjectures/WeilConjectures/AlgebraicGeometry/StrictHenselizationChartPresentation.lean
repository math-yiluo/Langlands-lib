/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization

/-!
# The geometric strict henselization through an affine chart

Let `i : Spec R ⟶ S` be an open immersion and `xR : Spec Ω ⟶ Spec R` a geometric point with `Ω`
algebraically closed. The strict henselization of `S` at `xR ≫ i` is the ring-theoretic strict
henselization (`Algebra.IsStrictHenselization`) of the local ring `R_q` of `R` at the image `q`
of `xR`, compatibly with a ring map `ρ : R ⟶ 𝒪^{sh}_{S, xR ≫ i}` such that `Spec ρ ≫ i` is the
structure map of the strict localization (Stacks, Tag 04HX).

This is the chart version of
`AlgebraicGeometry.Scheme.strictHenselizationRing_local_presentation`; the proof is that of the
private chart lemma of `WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation`,
made available here for a non-affine `S` (blueprint `lemma-punctured-surface-punctured-curve--1`).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- The nested small-model, affine-chart, and triple diagrams require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- **The strict henselization through an affine chart** (Stacks, Tag 04HX). For an open
immersion `i : Spec R ⟶ S` and a geometric point `xR : Spec Ω ⟶ Spec R` with `Ω` algebraically
closed, there are a prime `q` of `R`, a separable closure `K` of the residue field of `R_q` and
a ring map `ρ : R ⟶ 𝒪^{sh}_{S, xR ≫ i}` with `Spec ρ ≫ i` the structure map of the strict
localization, such that `𝒪^{sh}_{S, xR ≫ i}` is the strict henselization of `R_q` with respect
to `K`, compatibly with `ρ`; the prime `q` is the image of `xR` (blueprint
`lemma-punctured-surface-punctured-curve--1`). -/
theorem strictHenselizationRing_chart_presentation
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselization (xR ≫ i)))
      (b : R ⟶ strictHenselization (xR ≫ i)),
      Spec.map b ≫ i = strictLocalizationToBase (xR ≫ i) ∧
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselization (xR ≫ i))
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselization (xR ≫ i)) ∧ (xR (IsLocalRing.closedPoint Ω)).asIdeal = q := by
  classical
  let s := xR ≫ i
  let p := (SpecToEquivOfField Ω (Spec R) xR).1
  let F := (Spec R).residueField p
  let e := (SpecToEquivOfField Ω (Spec R) xR).2
  let : Algebra F Ω := e.hom.toAlgebra
  let K := separableClosure F Ω
  obtain ⟨_, _, _, _, E, δ, hδ, cn, cu, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩, r, t, _, ht⟩ :=
    etale_local_ring_triples S Ω R i xR
  let c := ct
  have hc : IsColimit c := hct
  let χ := CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)
  let t₀ : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  let ρ := c.ι.app t₀
  have hρ (t : EtaleResidueTriples R p K χ) : t.α ≫ c.ι.app t = ρ := by
    let g : t₀ ⟶ t := InducedCategory.homMk
      (Under.homMk (Over.homMk t.α (by
        change t.α ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ
        exact t.compatible)) (by
        apply Over.OverMorphism.ext
        simp [t₀, EtaleResidueTriple.factorization]))
    exact c.w g
  let Nall := (pointSmallEtale s).fiber.Elements
  let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
  let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale s).fiber ⋙
    Etale.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ
  let : HasColimit D := ⟨⟨cn, hcn⟩⟩
  let incl := strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence s
  let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let q := (rep ⋙ incl).op
  let eSmall : strictHenselization s ≅ colimit (strictHenselizationAffineDiagram s) :=
    (isColimitSmallStrictHenselizationCocone s).coconePointUniqueUpToIso
      (colimit.isColimit (strictHenselizationAffineDiagram s))
  let cmp : strictHenselization s ≅ cn.pt :=
    eSmall ≪≫ Functor.Final.colimitIso q D ≪≫ colimit.isoColimitCocone ⟨cn, hcn⟩
  let k := hct.coconePointUniqueUpToIso hc
  let ringIso : strictHenselization s ≅ c.pt := cmp ≪≫ t ≪≫ k
  have hstruct : Spec.map (ρ ≫ ringIso.inv) ≫ i =
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
      change (smallStrictHenselizationCocone s).ι.app (op j) ≫
        (eSmall.hom ≫
        ((Functor.Final.colimitIso q D).hom ≫
          (colimit.isoColimitCocone ⟨cn, hcn⟩).hom)) = _
      rw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
      change colimit.ι (q ⋙ D) (op j) ≫
        ((Functor.Final.colimitIso q D).hom ≫
          (colimit.isoColimitCocone ⟨cn, hcn⟩).hom) = _
      rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
      exact colimit.isoColimitCocone_ι_hom ⟨cn, hcn⟩ (op b)
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
  obtain ⟨L, hL, ares, hsep, aL, htower, aH, hbase, hH⟩ :=
    etaleResidueTriples_localized_isStrictHenselization R p K c hc
      (strictHenselization s) ringIso.symm (ρ ≫ ringIso.inv) (by
        intro t
        rw [← Category.assoc, hρ t]
        rfl)
  exact ⟨p.asIdeal, p.isPrime, L, hL, ares, hsep, aL, htower, aH,
    ρ ≫ ringIso.inv, hstruct, hbase, hH, rfl⟩

end AlgebraicGeometry.Scheme
