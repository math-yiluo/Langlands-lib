/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import WeilConjectures.AlgebraicGeometry.EtalePageMapCoherence
/-! # Coordinate-swapped diagram of functorial hypercohomology pages

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-page-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Swapping bidegrees interchanges the differential vectors. -/
private def swapEmbedding (r : ℤ) :
    (ComplexShape.up' ((1 - r, r) : ℤ × ℤ)).Embedding
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)) :=
  ComplexShape.Embedding.mk' _ _ Prod.swap Prod.swap_injective (by
    intro i j
    change i + (1 - r, r) = j ↔ i.swap + (r, 1 - r) = j.swap
    constructor <;> intro h
    · simpa using congrArg Prod.swap h
    · simpa using congrArg Prod.swap h)

private instance (r : ℤ) : (swapEmbedding r).IsRelIff := by
  unfold swapEmbedding
  infer_instance

/-- The restriction homology isomorphism for the coordinate swap. -/
private noncomputable def swapHomologyIso
    (r : ℤ) (K : HomologicalComplex AddCommGrpCat.{u + 1}
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ))) (j : ℤ × ℤ) :
    (K.restriction (swapEmbedding r)).homology j ≅ K.homology j.swap :=
  K.restrictionHomologyIso (swapEmbedding r)
    (j - (1 - r, r)) j (j + (1 - r, r))
    (ComplexShape.prev_eq' _ (by simp [ComplexShape.up', sub_add_cancel]))
    (ComplexShape.next_eq' _ rfl) rfl rfl rfl
    (ComplexShape.prev_eq' _ (by ext <;> simp [ComplexShape.up', swapEmbedding,
      ComplexShape.Embedding.mk']))
    (ComplexShape.next_eq' _ (by rfl))

set_option backward.isDefEq.respectTransparency false in
private theorem swapHomologyIso_naturality
    (r : ℤ) (K L : HomologicalComplex AddCommGrpCat.{u + 1}
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ))) (f : K ⟶ L) (j : ℤ × ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f
      (swapEmbedding r)) j ≫ (swapHomologyIso r L j).hom =
      (swapHomologyIso r K j).hom ≫ HomologicalComplex.homologyMap f j.swap := by
  rw [← cancel_epi ((K.restriction (swapEmbedding r)).homologyπ j)]
  simp only [HomologicalComplex.homologyπ_naturality_assoc,
    swapHomologyIso, HomologicalComplex.homologyπ_restrictionHomologyIso_hom,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom_assoc]
  erw [HomologicalComplex.homologyπ_naturality f j.swap]
  simp only [← Category.assoc]
  apply congrArg (fun t => t ≫ L.homologyπ j.swap)
  rw [← cancel_mono (L.iCycles j.swap)]
  simp only [Category.assoc]
  erw [HomologicalComplex.restrictionCyclesIso_hom_iCycles,
    HomologicalComplex.cyclesMap_i]
  erw [HomologicalComplex.cyclesMap_i f j.swap,
    HomologicalComplex.restrictionCyclesIso_hom_iCycles_assoc]
  simp only [HomologicalComplex.restrictionXIso, HomologicalComplex.restrictionMap_f,
    eqToIso_refl, Iso.refl_hom, Category.id_comp]
  rfl

/-- Reindex every page, and transport the successive homology isomorphisms. -/
private noncomputable def swapSequence
    (E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1) :
    SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' ((1 - r, r) : ℤ × ℤ)) 1 where
  page r hr := (E.page r hr).restriction (swapEmbedding r)
  iso r r' j h hr := swapHomologyIso r (E.page r hr) j ≪≫ E.iso r r' j.swap h hr

/-- Restrict page maps along the coordinate swap. -/
private noncomputable def swapSequenceMap
    {E E' : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1} (f : E ⟶ E') :
    swapSequence E ⟶ swapSequence E' where
  hom r hr := HomologicalComplex.restrictionMap (f.hom r hr) (swapEmbedding r)
  comm r r' j h hr := by
    dsimp [swapSequence]
    rw [← Category.assoc, swapHomologyIso_naturality, Category.assoc, f.comm r r' j.swap h hr]
    rfl

/-- The coordinate swap is functorial on spectral sequences. -/
private noncomputable def swapSequenceFunctor :
    CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1 ⥤
      SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' ((1 - r, r) : ℤ × ℤ)) 1 where
  obj := swapSequence
  map := swapSequenceMap
  map_id E := by apply SpectralSequence.hom_ext; intros; rfl
  map_comp f g := by apply SpectralSequence.hom_ext; intros; rfl

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent page and presentation families.
set_option linter.unusedVariables false in
/-- Assemble functorial pullback presentations into a spectral diagram, with coordinates swapped.
Source: Stacks Project, Tags 015J, 015K and 0EZM.

Proof: Send op i to the presentation T₀ of F i, and f.op to its pullback map M.
The identities and composition laws for M, transported through the displayed
canonical inverse-image isomorphisms, give the functor laws. The maps induced by
(c.π.app i, (eG i).inv followed by the cocone leg) form a compatible cocone: use
hG and the cocone equation, and then the composition law. Reindex every page
complex through the coordinate-swap equivalence (x,y) ↦ (y,x); the differential
vector becomes (1-r,r). Transport the successive homology isomorphisms through
this equivalence. Evaluation in a swapped bidegree gives pageIso and pageIsoLimit,
and transport of page morphisms gives their two naturality equations. The global
first-page equation hfirst supplies the ordinary cohomology dictionaries and their
naturality; the presentation's negative-degree vanishing supplies the two negative
resolution-degree statements. No stabilization or filtration comparison is used.
(blueprint: lem-weil-pbc-etale-complex-page-diagram). -/
theorem exists_etaleComplex_page_diagram
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    (hFK : ∀ i : I, CochainComplex.plus
      (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (F i))
    (hLK : CochainComplex.plus
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) L.pt)
    (p q : ℤ)
    (T₀ : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (T₀ X K).sequence ⟶ (T₀ Y L).sequence)
    (hfirst : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((T₀ Y L).firstPageIso p q).hom =
          ((T₀ X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p)))
    (hid : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        M (𝟙 X) K K
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) = 𝟙 (T₀ X K).sequence)
    (hcomp : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        M (g ≫ f) K N
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{u + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) = M f K L v ≫ M g L N w) :
    ∃ (E : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v : ∀ i : Iᵒᵖ, E.obj i ⟶ E')
      (compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), E.map f ≫ v j = v i)
      (firstIso : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((E.obj (op i)).page 1 (le_refl 1)).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
      (firstIsoLimit : ∀ (r : ℕ) (s : ℤ),
      (E'.page 1 (le_refl 1)).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
      (first_transition : ∀ (i j : I) (f : j ⟶ i) (r : ℕ) (s : ℤ),
      ((E.map f.op).hom 1 (le_refl 1)).f ⟨(r : ℤ), s⟩ ≫ (firstIso j r s).hom =
        (firstIso i r s).hom ≫ AddCommGrpCat.ofHom
          ((Sheaf.H.map ((φ f).f s) r).comp (cohomologyMap (D.map f) ((F i).X s) r)))
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v (op i)).hom 1 (le_refl 1)).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ AddCommGrpCat.ofHom
          ((Sheaf.H.map (((eG i).inv ≫ L.ι.app (op i)).f s) r).comp
            (cohomologyMap (c.π.app i) ((F i).X s) r)))
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E.obj i).page 1 (le_refl 1)).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1 (le_refl 1)).X ⟨r, s⟩))
      (pageIso : ∀ (i : I) (r : ℤ) (hr : 1 ≤ r),
        ((E.obj (op i)).page r hr).X ⟨p - q, q⟩ ≅
          ((T₀ (D.obj i) ⟨F i, hFK i⟩).sequence.page r hr).X ⟨q, p - q⟩)
      (pageIsoLimit : ∀ (r : ℤ) (hr : 1 ≤ r),
        (E'.page r hr).X ⟨p - q, q⟩ ≅
          ((T₀ c.pt ⟨L.pt, hLK⟩).sequence.page r hr).X ⟨q, p - q⟩),
      (∀ (i j : I) (f : j ⟶ i) (r : ℤ) (hr : 1 ≤ r),
        ((E.map f.op).hom r hr).f ⟨p - q, q⟩ ≫ (pageIso j r hr).hom =
          (pageIso i r hr).hom ≫
            ((M (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f)).hom r hr).f ⟨q, p - q⟩) ∧
      (∀ (i : I) (r : ℤ) (hr : 1 ≤ r),
        ((v (op i)).hom r hr).f ⟨p - q, q⟩ ≫ (pageIsoLimit r hr).hom =
          (pageIso i r hr).hom ≫
            ((M (c.π.app i) ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩
              ((eG i).inv ≫ L.ι.app (op i))).hom r hr).f ⟨q, p - q⟩) := by
  obtain ⟨hmid, hmcomp, hmcone⟩ := etale_page_map_coherence D c F φ hidentity
    hcomposition G eG hG L hFK hLK T₀ M hid hcomp
  let R : Iᵒᵖ ⥤ CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1 :=
    { obj i := (T₀ (D.obj i.unop) ⟨F i.unop, hFK i.unop⟩).sequence
      map {i j} f := M (D.map f.unop) ⟨F i.unop, hFK i.unop⟩
        ⟨F j.unop, hFK j.unop⟩ (φ f.unop)
      map_id i := hmid i.unop
      map_comp {i j k} f g := hmcomp i.unop j.unop k.unop f.unop g.unop }
  let E := R ⋙ swapSequenceFunctor
  let E' := swapSequence (T₀ c.pt ⟨L.pt, hLK⟩).sequence
  let v : ∀ i : Iᵒᵖ, E.obj i ⟶ E' := fun i =>
    swapSequenceMap (M (c.π.app i.unop) ⟨F i.unop, hFK i.unop⟩ ⟨L.pt, hLK⟩
      ((eG i.unop).inv ≫ L.ι.app i))
  refine ⟨E, E', v, ?_,
    (fun i r s => (T₀ (D.obj i) ⟨F i, hFK i⟩).firstPageIso r s),
    (fun r s => (T₀ c.pt ⟨L.pt, hLK⟩).firstPageIso r s),
    ?_, ?_, ?_, ?_,
    (fun i r hr => Iso.refl _), (fun r hr => Iso.refl _), ?_, ?_⟩
  · intro i j f
    change swapSequenceMap _ ≫ swapSequenceMap _ = swapSequenceMap _
    have hh := congrArg swapSequenceMap (hmcone i.unop j.unop f.unop)
    exact hh
  · intro i j f r s
    exact hfirst (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f) r s
  · intro i r s
    exact hfirst (c.π.app i) ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩
      ((eG i).inv ≫ L.ι.app (op i)) r s
  · intro i r s hr
    exact (T₀ (D.obj i.unop) ⟨F i.unop, hFK i.unop⟩).negative s r hr
  · intro r s hr
    exact (T₀ c.pt ⟨L.pt, hLK⟩).negative s r hr
  · intro i j f r hr
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · intro i r hr
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

end AlgebraicGeometry.Etale
