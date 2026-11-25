/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

/-!
# Construction of the compatible affine chart functor

Source: Stacks Project, proof of Tag 04HX and Remark Tag 04HT
(blueprint: lem-weil-pbc-etale-chart-residue-triples-equivalence).
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private lemma residuePoint_toSpec (X : Scheme.{v}) (r : X) :
    X.fromSpecResidueField r ≫ X.toSpecΓ = Spec.map (X.Γevaluation r) := by
  simp only [fromSpecResidueField, Category.assoc, fromSpecStalk_toSpecΓ,
    ← Spec.map_comp]
  rfl

private lemma spec_residuePoint (B : CommRingCat.{v}) (q : Spec B) :
    Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation q) =
      (Spec B).fromSpecResidueField q := by
  rw [Spec.map_comp, ← residuePoint_toSpec, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private def restrictedPoint (Ω : Type v) [Field Ω]
    {F : Type v} [Field F] [Algebra F Ω] (K : IntermediateField F Ω)
    (X : Scheme.{v}) (y : Spec (.of Ω) ⟶ X)
    (h : ∀ z, (SpecToEquivOfField Ω X y).2 z ∈ K) : Spec (.of K) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    ((SpecToEquivOfField Ω X y).2.hom.codRestrict K.toSubring h)) ≫
      X.fromSpecResidueField (SpecToEquivOfField Ω X y).1

private lemma restrictedPoint_lift (Ω : Type v) [Field Ω]
    (F : Type v) [Field F] [Algebra F Ω] (K : IntermediateField F Ω)
    (X : Scheme.{v}) (y : Spec (.of Ω) ⟶ X)
    (h : ∀ z, (SpecToEquivOfField Ω X y).2 z ∈ K) :
    Spec.map (CommRingCat.ofHom K.subtype) ≫ restrictedPoint Ω K X y h = y := by
  rw [restrictedPoint, ← Category.assoc, ← Spec.map_comp]
  exact (SpecToEquivOfField Ω X).symm_apply_apply y

private lemma affine_point_cancel {K Ω : Type v} [Field K] [Field Ω]
    (s : CommRingCat.of K ⟶ CommRingCat.of Ω) (B : CommRingCat.{v})
    {a b : Spec (.of K) ⟶ Spec B} (h : Spec.map s ≫ a = Spec.map s ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext z
  exact s.hom.injective (congrArg (fun f ↦ f z) h)

private lemma affine_triple_properties (A : CommRingCat.{v}) (p : Spec A)
    (K : Type v) [Field K] (χ : (Spec A).residueField p ⟶ .of K)
    (V : Scheme.{v}) [IsAffine V] (g : V ⟶ Spec A) [Etale g]
    (y : Spec (.of K) ⟶ V)
    (hy : y ≫ g = Spec.map χ ≫ (Spec A).fromSpecResidueField p) :
    let B := Γ(V, ⊤)
    let α := (ΓSpecIso A).inv ≫ g.appTop
    let qφ := SpecToEquivOfField K (Spec B) (y ≫ V.toSpecΓ)
    Etale (Spec.map α) ∧ Spec.map α qφ.1 = p ∧
      α ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation qφ.1 ≫ qφ.2 =
        (ΓSpecIso A).inv ≫ (Spec A).Γevaluation p ≫ χ := by
  dsimp only
  have hg : V.toSpecΓ ≫ Spec.map ((ΓSpecIso A).inv ≫ g.appTop) = g := by
    rw [Spec.map_comp, ← toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have he : Etale (Spec.map ((ΓSpecIso A).inv ≫ g.appTop)) := by
    have heq : Spec.map ((ΓSpecIso A).inv ≫ g.appTop) = V.isoSpec.inv ≫ g := by
      rw [← hg, ← Category.assoc]
      simp [isoSpec]
    rw [heq]
    infer_instance
  have hy' : (y ≫ V.toSpecΓ) ≫ Spec.map ((ΓSpecIso A).inv ≫ g.appTop) =
      Spec.map χ ≫ (Spec A).fromSpecResidueField p := by
    rw [Category.assoc, hg, hy]
  refine ⟨he, ?_, ?_⟩
  · simpa [SpecToEquivOfField_apply_fst] using
      congrArg (fun f : Spec (.of K) ⟶ Spec A ↦ f (IsLocalRing.closedPoint K)) hy'
  · apply Spec.map_injective
    have hp := (SpecToEquivOfField K (Spec Γ(V, ⊤))).symm_apply_apply
      (y ≫ V.toSpecΓ)
    simp only [SpecToEquivOfField_symm_apply] at hp
    rw [← spec_residuePoint] at hp hy'
    simpa only [Spec.map_comp, Category.assoc] using
      (congrArg (fun f ↦ f ≫ Spec.map ((ΓSpecIso A).inv ≫ g.appTop)) hp).trans hy'

set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, proof of Tag 04HX (lemma-describe-etale-local-ring),
first paragraph, and Tag 04HT (remark-etale-neighbourhoods).
(blueprint: lem-weil-pbc-etale-chart-functor-construction).

Proof: For c = (V, v) choose the chart map g. It is unique because i is a monomorphism.
Put B = Γ(V) and α = (ΓSpecIso A).inv followed by g.appTop. The affine isomorphism
V ≅ Spec B identifies Spec α with g; cancellation of the étale open immersion i
shows that g, hence Spec α, is étale. Transport v along V → Spec Γ(V), obtain its
prime q and residue embedding into Ω, and restrict that embedding to K using the
assumed image containment. Cancellation of i in v followed by the structure map
shows that q lies over p and gives the required compatibility on A. This constructs
the triple H(c); its underlying ring is Γ(V). On a reversed neighbourhood morphism
use the map on global sections. Commutation with the structure maps gives A-linearity.
Commutation with the points gives commutation of the maps to Ω; injectivity of K → Ω
gives commutation of the maps to K. These are exactly the morphisms of triples.
Functoriality follows from functoriality of global sections. The identity maps on
Γ(V) give the natural isomorphism δ, the definition of α gives the first formula,
and the residue-field factorization of the transported point gives the second.
This statement constructs only a functor, without claiming fullness or surjectivity. -/
theorem etale_chart_residue_triples_functor_construction
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
      ∃ (H : NUᵒᵖ ⥤ T) (δ : DU ≅ H ⋙ DT),
        (∀ c : NU,
          let t := H.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))) := by
  classical
  dsimp only
  intro hK
  let x := xU ≫ i
  let p := (SpecToEquivOfField Ω (Spec A) xU).1
  let F := (Spec A).residueField p
  let e := (SpecToEquivOfField Ω (Spec A) xU).2
  let : Algebra F Ω := e.hom.toAlgebra
  let K := separableClosure F Ω
  let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
  let Nall := (pointSmallEtale x).fiber.Elements
  let P : ObjectProperty Nall := fun c ↦ IsAffine c.1.left
  let N := P.FullSubcategory
  let Q : ObjectProperty N := fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A,
    g ≫ i = c.obj.1.hom
  let NU := Q.FullSubcategory
  let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
    Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
  let DU := Q.ι.op ⋙ D
  let T := EtaleResidueTriples A p K χ
  let DT := etaleResidueTriplesRingDiagram A p K χ
  let g (c : NU) : c.obj.obj.1.left ⟶ Spec A := c.property.choose
  have hg (c : NU) : g c ≫ i = c.obj.obj.1.hom := c.property.choose_spec
  have g_unique (c : NU) (g' : c.obj.obj.1.left ⟶ Spec A)
      (hg' : g' ≫ i = c.obj.obj.1.hom) : g' = g c := by
    apply (cancel_mono i).mp
    exact hg'.trans (hg c).symm
  let y (c : NU) : Spec (.of K) ⟶ c.obj.obj.1.left :=
    restrictedPoint Ω K _ c.obj.obj.2.left (hK c)
  have hy (c : NU) : Spec.map (CommRingCat.ofHom K.subtype) ≫ y c =
      c.obj.obj.2.left := restrictedPoint_lift Ω F K _ _ (hK c)
  have hχ : Spec.map (CommRingCat.ofHom K.subtype) ≫
      (Spec.map χ ≫ (Spec A).fromSpecResidueField p) = xU := by
    rw [← Category.assoc, ← Spec.map_comp]
    exact (SpecToEquivOfField Ω (Spec A)).symm_apply_apply xU
  have yg (c : NU) : y c ≫ g c = Spec.map χ ≫
      (Spec A).fromSpecResidueField p := by
    apply affine_point_cancel (CommRingCat.ofHom K.subtype) A
    rw [← Category.assoc, hy, hχ]
    apply (cancel_mono i).mp
    rw [Category.assoc, hg]
    exact c.obj.obj.2.w
  have affine (c : NU) : IsAffine c.obj.obj.1.left := c.obj.property
  have etale_g (c : NU) : Etale (g c) := by
    have : Etale (g c ≫ i) := by
      rw [hg]
      exact c.obj.obj.1.prop
    exact AlgebraicGeometry.Etale.of_comp (g c) i
  let α (c : NU) := (ΓSpecIso A).inv ≫ (g c).appTop
  let qφ (c : NU) := SpecToEquivOfField K (Spec Γ(c.obj.obj.1.left, ⊤))
    (y c ≫ c.obj.obj.1.left.toSpecΓ)
  have properties (c : NU) := @affine_triple_properties A p K _ χ
    c.obj.obj.1.left (affine c) (g c) (etale_g c) (y c) (yg c)
  let t (c : NU) : T :=
    { B := Γ(c.obj.obj.1.left, ⊤)
      α := α c
      etale := (properties c).1
      q := (qφ c).1
      over := (properties c).2.1
      φ := (qφ c).2
      compatible := (properties c).2.2 }
  have point_formula (c : NU) : c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
      Spec.map (CommRingCat.ofHom K.subtype) ≫
        Spec.map ((ΓSpecIso (t c).B).inv ≫ (Spec (t c).B).Γevaluation (t c).q ≫
          (t c).φ) := by
    have hp := (SpecToEquivOfField K (Spec Γ(c.obj.obj.1.left, ⊤))).symm_apply_apply
      (y c ≫ c.obj.obj.1.left.toSpecΓ)
    simp only [SpecToEquivOfField_symm_apply] at hp
    rw [← spec_residuePoint] at hp
    change _ = Spec.map (CommRingCat.ofHom K.subtype) ≫
      Spec.map ((ΓSpecIso Γ(c.obj.obj.1.left, ⊤)).inv ≫
        (Spec Γ(c.obj.obj.1.left, ⊤)).Γevaluation (qφ c).1 ≫ (qφ c).2)
    have hp' : Spec.map ((ΓSpecIso Γ(c.obj.obj.1.left, ⊤)).inv ≫
        (Spec Γ(c.obj.obj.1.left, ⊤)).Γevaluation (qφ c).1 ≫ (qφ c).2) =
        y c ≫ c.obj.obj.1.left.toSpecΓ := by
      simpa only [Spec.map_comp, Category.assoc] using hp
    rw [hp', ← Category.assoc, hy]
  have chart_map {c d : NU} (f : c ⟶ d) :
      f.hom.hom.hom.left ≫ g d = g c := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hg, hg]
    exact f.hom.hom.hom.w
  have point_map {c d : NU} (f : c ⟶ d) :
      c.obj.obj.2.left ≫ f.hom.hom.hom.left = d.obj.obj.2.left := by
    have hf := f.hom.hom.map_val
    exact congrArg Over.Hom.left hf
  have alpha_map {c d : NU} (f : c ⟶ d) :
      α d ≫ f.hom.hom.hom.left.appTop = α c := by
    dsimp only [α]
    rw [Category.assoc, ← Hom.comp_appTop, chart_map]
  have residue_map {c d : NU} (f : c ⟶ d) :
      f.hom.hom.hom.left.appTop ≫
        ((ΓSpecIso (t c).B).inv ≫ (Spec (t c).B).Γevaluation (t c).q ≫ (t c).φ) =
      (ΓSpecIso (t d).B).inv ≫ (Spec (t d).B).Γevaluation (t d).q ≫ (t d).φ := by
    apply Spec.map_injective
    apply affine_point_cancel (CommRingCat.ofHom K.subtype) (t d).B
    rw [Spec.map_comp, ← Category.assoc, ← point_formula,
      Category.assoc, ← toSpecΓ_naturality f.hom.hom.hom.left, ← Category.assoc,
      point_map, point_formula]
  let H : NUᵒᵖ ⥤ T :=
    { obj := fun c ↦ t c.unop
      map := fun f ↦ InducedCategory.homMk
        (Under.homMk (Over.homMk f.unop.hom.hom.hom.left.appTop (residue_map f.unop))
          (by
            apply Over.OverMorphism.ext
            exact alpha_map f.unop))
      map_id := by
        intro c
        apply InducedCategory.hom_ext
        apply Under.UnderMorphism.ext
        apply Over.OverMorphism.ext
        exact DU.map_id c
      map_comp := by
        intro c d e f k
        apply InducedCategory.hom_ext
        apply Under.UnderMorphism.ext
        apply Over.OverMorphism.ext
        exact DU.map_comp f k }
  let δ : DU ≅ H ⋙ DT := NatIso.ofComponents (fun c ↦ Iso.refl _) (by
    intro c d f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)
  refine ⟨H, δ, ?_⟩
  intro c
  constructor
  · intro g' hg'
    change (ΓSpecIso A).inv ≫ g'.appTop ≫ 𝟙 _ = α c
    exact (Category.comp_id _).trans
      (congrArg (fun k ↦ (ΓSpecIso A).inv ≫ k.appTop) (g_unique c g' hg'))
  · change c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
      Spec.map (CommRingCat.ofHom K.subtype) ≫
        Spec.map ((ΓSpecIso (t c).B).inv ≫ (Spec (t c).B).Γevaluation (t c).q ≫
          (t c).φ) ≫ Spec.map (𝟙 (t c).B)
    simpa only [Spec.map_id, Category.comp_id] using point_formula c

end AlgebraicGeometry.Scheme
