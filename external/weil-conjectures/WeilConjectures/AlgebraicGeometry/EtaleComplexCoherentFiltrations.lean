/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration


public import WeilConjectures.AlgebraicGeometry.EtaleComplexFiltrationPageData
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import WeilConjectures.AlgebraicGeometry.EtaleHypercohomologyUniformBound
import WeilConjectures.AlgebraicGeometry.EtalePageMapCoherence
import WeilConjectures.AlgebraicGeometry.EtaleComplexColimitBelow
import WeilConjectures.AlgebraicGeometry.EtalePresentationImageFiltration

/-! # Coherent categorical filtrations for an etale complex diagram

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-coherent-filtrations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Swapping bidegrees interchanges the differential vectors. -/
private def coherentSwapEmbedding (r : ℤ) :
    (ComplexShape.up' ((1 - r, r) : ℤ × ℤ)).Embedding
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)) :=
  ComplexShape.Embedding.mk' _ _ Prod.swap Prod.swap_injective (by
    intro i j
    change i + (1 - r, r) = j ↔ i.swap + (r, 1 - r) = j.swap
    constructor <;> intro h
    · simpa using congrArg Prod.swap h
    · simpa using congrArg Prod.swap h)

private instance (r : ℤ) : (coherentSwapEmbedding r).IsRelIff := by
  unfold coherentSwapEmbedding
  infer_instance

/-- The restriction homology isomorphism for the coordinate swap. -/
private noncomputable def coherentSwapHomologyIso
    (r : ℤ) (K : HomologicalComplex AddCommGrpCat.{u + 1}
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ))) (j : ℤ × ℤ) :
    (K.restriction (coherentSwapEmbedding r)).homology j ≅ K.homology j.swap :=
  K.restrictionHomologyIso (coherentSwapEmbedding r)
    (j - (1 - r, r)) j (j + (1 - r, r))
    (ComplexShape.prev_eq' _ (by simp [ComplexShape.up', sub_add_cancel]))
    (ComplexShape.next_eq' _ rfl) rfl rfl rfl
    (ComplexShape.prev_eq' _ (by ext <;> simp [ComplexShape.up', coherentSwapEmbedding,
      ComplexShape.Embedding.mk']))
    (ComplexShape.next_eq' _ (by rfl))

set_option backward.isDefEq.respectTransparency false in
private theorem coherentSwapHomologyIso_naturality
    (r : ℤ) (K L : HomologicalComplex AddCommGrpCat.{u + 1}
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ))) (f : K ⟶ L) (j : ℤ × ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f
      (coherentSwapEmbedding r)) j ≫ (coherentSwapHomologyIso r L j).hom =
      (coherentSwapHomologyIso r K j).hom ≫ HomologicalComplex.homologyMap f j.swap := by
  rw [← cancel_epi ((K.restriction (coherentSwapEmbedding r)).homologyπ j)]
  simp only [HomologicalComplex.homologyπ_naturality_assoc,
    coherentSwapHomologyIso, HomologicalComplex.homologyπ_restrictionHomologyIso_hom,
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
private noncomputable def coherentSwapSequence
    (E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1) :
    SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' ((1 - r, r) : ℤ × ℤ)) 1 where
  page r hr := (E.page r hr).restriction (coherentSwapEmbedding r)
  iso r r' j h hr := coherentSwapHomologyIso r (E.page r hr) j ≪≫ E.iso r r' j.swap h hr

/-- Restrict page maps along the coordinate swap. -/
private noncomputable def coherentSwapSequenceMap
    {E E' : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1} (f : E ⟶ E') :
    coherentSwapSequence E ⟶ coherentSwapSequence E' where
  hom r hr := HomologicalComplex.restrictionMap (f.hom r hr) (coherentSwapEmbedding r)
  comm r r' j h hr := by
    dsimp [coherentSwapSequence]
    rw [← Category.assoc, coherentSwapHomologyIso_naturality, Category.assoc,
      f.comm r r' j.swap h hr]
    rfl

/-- The coordinate swap is functorial on spectral sequences. -/
private noncomputable def coherentSwapSequenceFunctor :
    CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1 ⥤
      SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' ((1 - r, r) : ℤ × ℤ)) 1 where
  obj := coherentSwapSequence
  map := coherentSwapSequenceMap
  map_id E := by apply SpectralSequence.hom_ext; intros; rfl
  map_comp f g := by apply SpectralSequence.hom_ext; intros; rfl


/-- A complex supported above `a` contributes its whole cohomology at filtration step `a`. -/
private theorem coherentFiltration_step_top (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p a : ℤ)
    (hbelow : ∀ n : ℤ, n < a → IsZero (K.obj.X n)) : (T.H p).step a = ⊤ := by
  have hepi : Epi ((T.H p).step a).arrow := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro x
    apply (etalePresentation_image_filtration X K T p a x).1
    refine ⟨K.obj, hbelow, 𝟙 _, x, ?_⟩
    simp
  simpa only [Subobject.mk_arrow] using
    (Subobject.epi_iff_mk_eq_top ((T.H p).step a).arrow).1 hepi

/-- Filtration steps above the cohomological degree vanish. -/
private theorem coherentFiltration_step_bot (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) (hpq : p < q) :
    (T.H p).step q = ⊥ := by
  rw [← Subobject.mk_arrow ((T.H p).step q), Subobject.mk_eq_bot_iff_zero]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  have hx := (etalePresentation_image_filtration X K T p q _).2 ⟨x, rfl⟩
  exact eq_zero_of_inEtaleHypercohomologyFiltration X K.obj p q hpq _ hx


set_option backward.isDefEq.respectTransparency true in
-- Elaborate the dependent page isomorphisms and all filtration-degree witnesses.
set_option linter.unusedVariables false in
/-- One diagram of pages with categorical abutment filtrations at every degree.
This statement constructs no reindexing, subgroup presentation, or quotient homomorphism.
Source: Stacks Project, Tags 015J and 015K; the finite-support argument of Tag 0EZM.

Proof:
1. Apply the functorial Cartan--Eilenberg construction to the stage complexes and
   the degreewise colimit of their inverse images. Exact inverse image and degreewise
   colimits preserve the lower bound a. Identity and composition for the coefficient
   maps assemble the spectral-sequence functor and its compatible maps to the target.
   Swap coordinates to resolution degree first. The natural first-page isomorphisms
   give the two displayed equations; negative resolution degrees vanish.
2. Use the canonical image filtrations on degree-p hypercohomology. The step at a
   is the whole object, since the complex is supported above a. Steps above p vanish
   since the truncated complex and its derived global sections are supported above p.
   If p<a, hypercohomology itself vanishes, so the step at a is also zero. This gives
   the upper bound at max a (p+1) without excluding the zero-length case.
3. For each q, choose r>max(p-q+1,q-a) with r>=1. Both incident differentials at
   (p-q,q) vanish, at all stages and the target. Subquotient convergence identifies
   this common page with each categorical graded piece. All q use the same pages and
   filtrations chosen in step 1; only r and the convergence isomorphisms depend on q.
4. Pullback preserves each canonical image-filtration step. Restrict the abutment
   map to these steps; monicity proves the square for their inclusions. Naturality
   of the convergence isomorphisms identifies its graded map with cokernel.map.
   The specified formula hP fixes its underlying abutment map. No continuity or
   surjectivity of any page comparison is used.
(blueprint: lem-weil-pbc-etale-complex-coherent-filtrations). -/
theorem exists_etale_complex_coherent_filtrations
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
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
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
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (L : Cocone G) (hL : IsColimit L) :
    ∃ (E0 : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v0 : ∀ i : Iᵒᵖ, E0.obj i ⟶ E')
      (compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), E0.map f ≫ v0 j = v0 i)
      (firstIso : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((E0.obj (op i)).page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
      (firstIsoLimit : ∀ (r : ℕ) (s : ℤ),
      (E'.page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
      (first_transition : ∀ (i j : I) (f : j ⟶ i) (r : ℕ) (s : ℤ),
      ((E0.map f.op).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIso j r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v0 (op i)).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
          ((eG i).inv ≫ L.ι.app (op i)) r s)
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E0.obj i).page 1).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1).X ⟨r, s⟩))
      (V : ∀ i : I, DecreasingFiltration
        ((cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i))))
      (W : DecreasingFiltration
        ((cohomology AddCommGrpCat.{u + 1} c.pt p).obj (DerivedCategory.Q.obj L.pt))),
      W.step a = ⊤ ∧ W.step (max a (p + 1)) = ⊥ ∧
      ∀ q : ℤ, ∃ (r : ℤ) (hr : 1 ≤ r)
        (e : ∀ i : I, ((E0.obj (op i)).page r hr).X ⟨p - q, q⟩ ≅ (V i).gradedPiece q)
        (e' : (E'.page r hr).X ⟨p - q, q⟩ ≅ W.gradedPiece q),
        ∀ i : I,
          ∃ (t : ∀ z : ℤ, ((V i).step z : AddCommGrpCat.{u + 1}) ⟶
              (W.step z : AddCommGrpCat.{u + 1}))
            (ht : ∀ z : ℤ, t z ≫ (W.step z).arrow =
              ((V i).step z).arrow ≫ P (c.π.app i) (F i) ≫
                (cohomology AddCommGrpCat.{u + 1} c.pt p).map
                  (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))))
            (hc : ∀ z : ℤ,
              Subobject.ofLE ((V i).step (z + 1)) ((V i).step z)
                  ((V i).antitone_step (Int.le_add_one (le_refl z))) ≫ t z =
                t (z + 1) ≫ Subobject.ofLE (W.step (z + 1)) (W.step z)
                  (W.antitone_step (Int.le_add_one (le_refl z)))),
            ((v0 (op i)).hom r hr).f ⟨p - q, q⟩ ≫ e'.hom =
              (e i).hom ≫ cokernel.map _ _ (t (q + 1)) (t q) (hc q) := by
  classical
  have hlimit := etaleComplex_colimit_below D c F a hbelow G eG L hL
  have hFK : ∀ i : I, CochainComplex.plus
      (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (F i) := by
    intro i
    exact ⟨a, (CochainComplex.isStrictlyGE_iff _ _).mpr (hbelow i)⟩
  have hLK : CochainComplex.plus
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) L.pt := by
    exact ⟨a, (CochainComplex.isStrictlyGE_iff _ _).mpr hlimit⟩
  let P₀ := fun {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (J : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ J) (n : ℤ) ↦
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
      ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
        ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          (DerivedCategory.Q.obj K)) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} f).hom.app
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
            (DerivedCategory.Q.obj K)) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map v))
  have hP₀ : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (J : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ J),
      P₀ f K J v p = P f K ≫
        (cohomology AddCommGrpCat.{u + 1} Y p).map (DerivedCategory.Q.map v) := by
    intro X Y f K J v
    rw [hP]
    set_option backward.isDefEq.respectTransparency false in
      simp only [P₀, rightDerivedLowerStarCompRightDerivedGlobalSectionsIso,
        lowerStarCompGlobalSectionsIso, cohomology, Functor.comp_map,
        Functor.map_comp, Category.assoc]
  obtain ⟨T₀, M, bound, eInf, ⟨hfirst, hfiltered, hid, hcomp⟩, hbound⟩ :=
    exists_etaleHypercohomology_uniform_bound P₀ (by intros; rfl)
  obtain ⟨hmid, hmcomp, hmcone⟩ := etale_page_map_coherence D c F φ hidentity
    hcomposition G eG hG L hFK hLK T₀ M (fun X K ↦ (hid X K).1)
      (fun f g K J V t w ↦ (hcomp f g K J V t w).1)
  let R : Iᵒᵖ ⥤ CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1 :=
    { obj i := (T₀ (D.obj i.unop) ⟨F i.unop, hFK i.unop⟩).sequence
      map {i j} f := M (D.map f.unop) ⟨F i.unop, hFK i.unop⟩
        ⟨F j.unop, hFK j.unop⟩ (φ f.unop)
      map_id i := hmid i.unop
      map_comp {i j k} f g := hmcomp i.unop j.unop k.unop f.unop g.unop }
  let E := R ⋙ coherentSwapSequenceFunctor
  let E' := coherentSwapSequence (T₀ c.pt ⟨L.pt, hLK⟩).sequence
  let v : ∀ i : Iᵒᵖ, E.obj i ⟶ E' := fun i =>
    coherentSwapSequenceMap (M (c.π.app i.unop) ⟨F i.unop, hFK i.unop⟩ ⟨L.pt, hLK⟩
      ((eG i.unop).inv ≫ L.ι.app i))
  let V := fun i ↦ (T₀ (D.obj i) ⟨F i, hFK i⟩).H p
  let W := (T₀ c.pt ⟨L.pt, hLK⟩).H p
  have htop : W.step a = ⊤ :=
    coherentFiltration_step_top c.pt ⟨L.pt, hLK⟩ (T₀ c.pt ⟨L.pt, hLK⟩) p a hlimit
  have hbot : W.step (max a (p + 1)) = ⊥ :=
    coherentFiltration_step_bot c.pt ⟨L.pt, hLK⟩ (T₀ c.pt ⟨L.pt, hLK⟩) p
      (max a (p + 1)) (by omega)
  choose t ht hc hs using fun i : I ↦ hfiltered (X := D.obj i) (Y := c.pt) (c.π.app i)
    ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩ ((eG i).inv ≫ L.ι.app (op i)) p
  have ht' (i : I) (z : ℤ) : t i z ≫ (W.step z).arrow =
      ((V i).step z).arrow ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))) := by
    simpa only [hP₀, Category.assoc] using ht i z
  refine ⟨E, E', v, ?_,
    (fun i r s ↦ (T₀ (D.obj i) ⟨F i, hFK i⟩).firstPageIso r s),
    (fun r s ↦ (T₀ c.pt ⟨L.pt, hLK⟩).firstPageIso r s),
    ?_, ?_, ?_, ?_, V, W, htop, hbot, ?_⟩
  · intro i j f
    change coherentSwapSequenceFunctor.map _ ≫ coherentSwapSequenceFunctor.map _ =
      coherentSwapSequenceFunctor.map _
    rw [← Functor.map_comp, hmcone i.unop j.unop f.unop]
  · intro i j f r s
    exact hfirst (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f) r s
  · intro i r s
    exact hfirst (c.π.app i) ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩
      ((eG i).inv ≫ L.ι.app (op i)) r s
  · intro i r s hr
    exact (T₀ (D.obj i.unop) ⟨F i.unop, hFK i.unop⟩).negative s r hr
  · intro r s hr
    exact (T₀ c.pt ⟨L.pt, hLK⟩).negative s r hr
  · intro q
    let N := max 1 (max (q - a + 2) (p - q + 2))
    have one_le : 1 ≤ N := le_max_left _ _
    have hR : ∀ i : I, bound (D.obj i) ⟨F i, hFK i⟩ q p ≤ N := by
      intro i
      exact hbound (D.obj i) ⟨F i, hFK i⟩ a q p (hbelow i)
    have hR' : bound c.pt ⟨L.pt, hLK⟩ q p ≤ N :=
      hbound c.pt ⟨L.pt, hLK⟩ a q p hlimit
    let e := fun i ↦ eInf (D.obj i) ⟨F i, hFK i⟩ q p N one_le (hR i)
    let e' := eInf c.pt ⟨L.pt, hLK⟩ q p N one_le hR'
    refine ⟨N, one_le, e, e', ?_⟩
    intro i
    exact ⟨t i, ht' i, hc i, hs i q N one_le (hR i) hR'⟩


end AlgebraicGeometry.Etale
