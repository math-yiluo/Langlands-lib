/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization

/-! # Geometric strict henselization as a local-base algebra

Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring).
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- The nested small-model, affine-chart, and triple diagrams require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- In an affine open chart `i : Spec R ⟶ S` through which the geometric point factors as
`xR ≫ i`, the strict henselization of `S` at `xR ≫ i` is an algebraic strict henselization of
`R` localized at the image `xR(*)` of the geometric point, compatibly with a ring map
`b : R ⟶ 𝒪^{sh}` whose spectrum followed by `i` is the structure morphism.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), using Tag 04GW. -/
theorem strictHenselization_chart_isStrictHenselization
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
      q = (xR (IsLocalRing.closedPoint Ω)).asIdeal ∧
      Spec.map b ≫ i = strictLocalizationToBase (xR ≫ i) ∧
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselization (xR ≫ i))
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselization (xR ≫ i)) := by
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
    ρ ≫ ringIso.inv, rfl, hstruct, hbase, hH⟩


/-- The geometric strict henselization is an algebraic strict henselization of a prime
localization, compatibly with the given structural ring map. There is no divisor here.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), using Tag 04GW.
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)

Proof: Let q be the image of the geometric point, and put A = R_q. Its residue field is
canonically the residue field at q. Inside the geometric field take the relative separable
closure K of that residue field. Affine pointed etale neighbourhoods compute the geometric
strict henselization ring. By the affine neighbourhood/triples comparison their coordinate
ring diagram is equivalent to etale residue triples over R at q with embeddings into K.
Passing from R to A does not change its colimit: etale algebras and their finitely many
presentation equations descend from A to R after inverting one element outside q, and
these principal localizations are pointed etale neighbourhoods. The equivalence between
residue triples over the local ring A and etale A-algebras pointed in K identifies this
colimit with the diagram defining Algebra.IsStrictHenselization. Each element outside q
is a unit in the colimit, so the structural R-map extends uniquely to A. The comparison
preserves the maps from R; applying the faithful spectrum functor and hb identifies that
R-map with b. Transport the A-algebra structure through the colimit ring isomorphism;
its composite with R -> A is therefore b. All colimit identifications are characterized
by their legs, so no arbitrary algebraic object is chosen from mere existence. -/
theorem strictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselization barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselization barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselization barY) := by
  have h := strictHenselization_chart_isStrictHenselization R (𝟙 (Spec R)) barY
  rw [Category.comp_id] at h
  obtain ⟨q, hq, K, hK, ares, hsep, aK, htower, aH, ρ, -, hstruct, hbase, hH⟩ := h
  have hρ : ρ = b := by
    apply Spec.map_injective
    have hstruct' : Spec.map ρ = strictLocalizationToBase barY := by
      simpa only [Category.comp_id] using hstruct
    exact hstruct'.trans hb.symm
  subst ρ
  exact ⟨q, hq, K, hK, ares, hsep, aK, htower, aH, hbase, hH⟩

end AlgebraicGeometry.Scheme
