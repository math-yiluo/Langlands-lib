/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence

/-!
# Affine pointed étale neighbourhoods and residue-field triples

Source: Stacks Project, Tags 03PQ, 04HT and 04HX
(blueprint: lem-weil-pbc-etale-local-ring-triples).
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
private theorem affine_refinement
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Y) (c : (pointSmallEtale x).fiber.Elements)
    (U : c.1.left.Opens) (hU : c.2.left (default : Spec (.of Ω)) ∈ U) :
    ∃ (d : (pointSmallEtale x).fiber.Elements) (f : d ⟶ c),
      IsAffine d.1.left ∧ Set.range f.1.left ⊆ U := by
  obtain ⟨R, j, hj, hmem, hsub⟩ := exists_affine_mem_range_and_range_subset hU
  have := hj
  have hpoint : Set.range c.2.left ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    have ha : a = (default : Spec (.of Ω)) :=
      @Subsingleton.elim (Spec (.of Ω)) inferInstance a default
    rwa [ha]
  let l := IsOpenImmersion.lift j c.2.left hpoint
  have hl : l ≫ j = c.2.left := IsOpenImmersion.lift_fac j c.2.left hpoint
  let d : (pointSmallEtale x).fiber.Elements :=
    Functor.elementsMk _ (Etale.mk (j ≫ c.1.hom))
      (Over.homMk l (by
        change l ≫ (j ≫ c.1.hom) = x
        rw [← Category.assoc, hl]
        exact Over.w c.2))
  refine ⟨d, ⟨MorphismProperty.Over.homMk j rfl (by simp), ?_⟩,
    inferInstanceAs (IsAffine (Spec R)), hsub⟩
  apply Over.OverMorphism.ext
  exact hl

set_option backward.isDefEq.respectTransparency.types false in
private theorem residue_image_separable
    {X S : Scheme.{v}} {Ω : Type v} [Field Ω]
    (g : X ⟶ S) [Etale g] (s : Spec (.of Ω) ⟶ X)
    (z : X.residueField (SpecToEquivOfField Ω X s).1) :
    let p := (SpecToEquivOfField Ω S (s ≫ g)).1
    let e := (SpecToEquivOfField Ω S (s ≫ g)).2
    letI : Algebra (S.residueField p) Ω := e.hom.toAlgebra
    (SpecToEquivOfField Ω X s).2 z ∈ separableClosure (S.residueField p) Ω := by
  dsimp [SpecToEquivOfField] at z ⊢
  rw [descResidueField_stalkClosedPointTo_comp]
  let F := S.residueField (g (s (IsLocalRing.closedPoint Ω)))
  let L := X.residueField (s (IsLocalRing.closedPoint Ω))
  let f := g.residueFieldMap (s (IsLocalRing.closedPoint Ω))
  let e := X.descResidueField (stalkClosedPointTo s)
  let : Algebra F L := f.hom.toAlgebra
  let : Algebra F Ω := (f ≫ e).hom.toAlgebra
  change L at z
  have : Algebra.IsSeparable F L := inferInstance
  let a : L →ₐ[F] Ω := { e.hom with commutes' := fun _ ↦ rfl }
  apply (mem_separableClosure_iff).2
  exact (Algebra.IsSeparable.isSeparable F z).map a a.injective

private theorem compatible_colimits
    {J C T : Type*} [Category J] [Category C] [Category T]
    (H : J ⥤ C) [H.Final] (D : C ⥤ CommRingCat.{v}) [HasColimit D]
    (DT : T ⥤ CommRingCat.{v}) (E : J ≌ T) (δ : H ⋙ D ≅ E.functor ⋙ DT) :
    ∃ (cn : Cocone D) (cu : Cocone (H ⋙ D)) (ct : Cocone DT),
      Nonempty (IsColimit cn) ∧ Nonempty (IsColimit cu) ∧ Nonempty (IsColimit ct) ∧
      ∃ (r : cu.pt ≅ cn.pt) (s : cn.pt ≅ ct.pt),
        (∀ c : J, cu.ι.app c ≫ r.hom = cn.ι.app (H.obj c)) ∧
        (∀ c : J, cn.ι.app (H.obj c) ≫ s.hom =
          δ.hom.app c ≫ ct.ι.app (E.functor.obj c)) := by
  have : HasColimit (E.functor ⋙ DT) := hasColimit_of_iso δ.symm
  have : HasColimit DT := hasColimit_of_equivalence_comp E
  let r := Functor.Final.colimitIso H D
  let t := HasColimit.isoOfNatIso δ ≪≫ Functor.Final.colimitIso E.functor DT
  refine ⟨colimit.cocone D, colimit.cocone (H ⋙ D), colimit.cocone DT,
    ⟨colimit.isColimit D⟩, ⟨colimit.isColimit (H ⋙ D)⟩, ⟨colimit.isColimit DT⟩,
    r, r.symm ≪≫ t, ?_, ?_⟩
  · intro c
    exact Functor.Final.ι_colimitIso_hom H D c
  · intro c
    dsimp [r, t]
    simp only [Functor.Final.ι_colimitIso_inv_assoc,
      HasColimit.ι_isoOfNatIso_hom_assoc, Functor.Final.ι_colimitIso_hom]

/-- Stacks, Tags 03PQ, 04HT and 04HX
(blueprint: lem-weil-pbc-etale-local-ring-triples).

Proof:
1. Factor the point through the affine chart. Its prime is the kernel of the
corresponding ring map, and its residue-field map is the map in `SpecToEquivOfField`
(def-weil-affine-spectrum, def-weil-residue-field, def-weil-geometric-point).
2. Shrink any pointed neighbourhood to an affine open containing its point
(lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink).
3. The category of all neighbourhoods is cofiltered by Tag 03PQ
(definition-torsion-sheaves--3). The pointed chart itself
gives a nonempty affine subcategory. Shrink the fibre products and
equalizers to affine neighbourhoods. Fullness gives cofilteredness of the affine
subcategory (lem-weil-pbc-colimit-initial-full-subcategory).
4. Shrink inside the inverse image of the chosen chart. Every affine neighbourhood
then receives a map from one factoring through the chart. The full inclusion is
initial, and its opposite preserves the ring colimit
(lem-weil-pbc-colimit-initial-full-subcategory).
5. For a neighbourhood over the chart, the residue field is finite separable over
that of the base (lem-weil-pbc-etale-algebra-residue-field-separable, Tag 04HT).
Its embedding into Ω therefore lands in the relative separable closure
(def-weil-pbc-relative-separable-closure). Cancellation of the open immersion shows
that its ring is étale over A (definition-torsion-sheaves--3).
The equation that the point lies over x, cancelled through the open immersion,
shows that q lies over p and that the residue-field embedding is compatible over κ(p).
6. For morphisms, cancellation of the open immersion identifies Y-morphisms over
the chart with U-morphisms. The affine spectrum anti-equivalence identifies these
with A-ring maps (def-weil-affine-spectrum). Carrying one specified point to the
other is exactly commutation of the maps to Ω, equivalently inverse-image equality
of primes and agreement of residue embeddings. This gives full faithfulness.
7. Conversely a triple gives its point by composing B → κ(q) → K → Ω.
Compatibility over κ(p) makes it a point over x. Étale composition gives a
neighbourhood of Y (definition-torsion-sheaves--3). Its prime and
residue embedding recover the given triple, proving essential surjectivity and
the claimed equivalence with its specified effect on rings and points.
8. Under this equivalence the global-section diagram is naturally the diagram B.
Transport the colimit cocone along it and along the initial inclusion; the resulting
isomorphisms commute with every coprojection (def-weil-pbc-category-colimit,
lem-weil-pbc-colimit-initial-full-subcategory).

The three colimits are expressed by universal cocones, avoiding any additional
existence hypothesis or choice of a small skeleton. -/
theorem etale_local_ring_triples
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
    let P : ObjectProperty Nall := fun c => IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c => ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    IsCofiltered N ∧ Q.ι.Initial ∧
      (∀ c : N, ∃ d : NU, Nonempty (d.obj ⟶ c)) ∧
      (∀ (c : NU) (z : c.obj.obj.1.left.residueField
          (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈ K) ∧
      ∃ (E : NUᵒᵖ ≌ T) (δ : DU ≅ E.functor ⋙ DT),
        (∀ c : NU,
          let t := E.functor.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))) ∧
        ∃ (cn : Cocone D) (cu : Cocone DU) (ct : Cocone DT),
          Nonempty (IsColimit cn) ∧ Nonempty (IsColimit cu) ∧ Nonempty (IsColimit ct) ∧
          ∃ (r : cu.pt ≅ cn.pt) (s : cn.pt ≅ ct.pt),
            (∀ c : NUᵒᵖ, cu.ι.app c ≫ r.hom = cn.ι.app (Q.ι.op.obj c)) ∧
            (∀ c : NUᵒᵖ, cn.ι.app (Q.ι.op.obj c) ≫ s.hom =
              δ.hom.app c ≫ ct.ι.app (E.functor.obj c)) := by
  classical
  dsimp only
  let x := xU ≫ i
  let P : ObjectProperty (pointSmallEtale x).fiber.Elements := fun c ↦ IsAffine c.1.left
  let Q : ObjectProperty P.FullSubcategory :=
    fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
  have hP : ∀ c, ∃ d : P.FullSubcategory, Nonempty (P.ι.obj d ⟶ c) := by
    intro c
    obtain ⟨d, f, hd, -⟩ := affine_refinement x c ⊤ (by simp)
    exact ⟨⟨d, hd⟩, ⟨f⟩⟩
  have hN : IsCofiltered P.FullSubcategory :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful P.ι hP
  have := hN
  have hQ : ∀ c, ∃ d : Q.FullSubcategory, Nonempty (d.obj ⟶ c) := by
    intro c
    have hx : c.obj.1.hom (c.obj.2.left (default : Spec (.of Ω))) ∈ Set.range i := by
      refine ⟨xU default, ?_⟩
      have hw := congrArg (fun f : Spec (.of Ω) ⟶ Y ↦ f default) (Over.w c.obj.2)
      exact hw.symm
    obtain ⟨d, f, hd, hsub⟩ := affine_refinement x c.obj
      (c.obj.1.hom ⁻¹ᵁ i.opensRange) hx
    have hr : Set.range (d.1.hom) ⊆ Set.range i := by
      rintro _ ⟨a, rfl⟩
      have hf : f.1.left ≫ c.obj.1.hom = d.1.hom := Over.w f.1.hom
      rw [← hf]
      exact hsub ⟨a, rfl⟩
    let g := IsOpenImmersion.lift i d.1.hom hr
    have hg : g ≫ i = d.1.hom := IsOpenImmersion.lift_fac i d.1.hom hr
    exact ⟨⟨⟨d, hd⟩, g, hg⟩, ⟨P.homMk f⟩⟩
  have hinitial : Q.ι.Initial :=
    Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful Q.ι hQ
  let : Algebra ((Spec A).residueField (SpecToEquivOfField Ω (Spec A) xU).1) Ω :=
    (SpecToEquivOfField Ω (Spec A) xU).2.hom.toAlgebra
  have hres : ∀ (c : Q.FullSubcategory)
      (z : c.obj.obj.1.left.residueField
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
      (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈
        separableClosure ((Spec A).residueField (SpecToEquivOfField Ω (Spec A) xU).1) Ω := by
    intro c z
    obtain ⟨g, hg⟩ := c.property
    have : Etale (g ≫ i) := hg.symm ▸ c.obj.obj.1.prop
    have : Etale g := Etale.of_comp g i
    have heq : c.obj.obj.2.left ≫ g = xU := by
      apply (cancel_mono i).1
      rw [Category.assoc, hg]
      exact Over.w c.obj.obj.2
    have h := residue_image_separable g c.obj.obj.2.left z
    rw [heq] at h
    exact h
  refine ⟨hN, hinitial, hQ, hres, ?_⟩
  have hEquiv := etale_chart_residue_triples_equivalence Y Ω A i xU
  have he := hEquiv hres
  obtain ⟨E, δ, hE⟩ := he
  refine ⟨E, δ, hE, ?_⟩
  have hPinitial : P.ι.Initial :=
    Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful P.ι hP
  have := hPinitial
  have := hinitial
  let Dall := (Functor.Elements.π (pointSmallEtale x).fiber ⋙
    Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
  have : HasColimit Dall := inferInstance
  have : HasColimit ((P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ) := by
    change HasColimit (P.ι.op ⋙ Dall)
    infer_instance
  exact compatible_colimits Q.ι.op _ _ E δ

end AlgebraicGeometry.Scheme
