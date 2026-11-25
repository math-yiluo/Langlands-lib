/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleHypercohomologyFiltration
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.AlgebraicGeometry.EtaleComplexUniformPages
import WeilConjectures.AlgebraicGeometry.EtalePresentationImageFiltration
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Stable-page representatives of the etale image filtration

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-filtration-page-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The map on ordinary sheaf cohomology in one complex degree, with fixed endpoints.
Source: Stacks Project, Tag 0EZM, the first-page comparison maps.
(blueprint: lem-weil-pbc-etale-complex-filtration-page-data). -/
noncomputable def complexTermCohomologyMap
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L) (r : ℕ) (s : ℤ) :
    AddCommGrpCat.of (Sheaf.H (K.X s) r) ⟶ AddCommGrpCat.of (Sheaf.H (L.X s) r) :=
  AddCommGrpCat.ofHom ((Sheaf.H.map (v.f s) r).comp (cohomologyMap f (K.X s) r))

private theorem step_quotient_zero_iff {A : AddCommGrpCat.{u + 1}}
    (B : DecreasingFiltration A) (q : ℤ) (y : (B.step q : AddCommGrpCat.{u + 1})) :
    cokernel.π (Subobject.ofLE (B.step (q + 1)) (B.step q)
      (B.antitone_step (Int.le_add_one (le_refl _)))) y = 0 ↔
        ∃ z : (B.step (q + 1) : AddCommGrpCat.{u + 1}),
          (B.step (q + 1)).arrow z = (B.step q).arrow y := by
  let j := Subobject.ofLE (B.step (q + 1)) (B.step q) (B.antitone_step (Int.le_add_one (le_refl _)))
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).mp (ShortComplex.exact_cokernel j) y h
    refine ⟨z, ?_⟩
    calc
      (B.step (q + 1)).arrow z = (B.step q).arrow (j z) := by
        exact (ConcreteCategory.congr_hom (Subobject.ofLE_arrow _) z).symm
      _ = (B.step q).arrow y := congrArg _ hz
  · rintro ⟨z, hz⟩
    have hy : j z = y := (AddCommGrpCat.mono_iff_injective (B.step q).arrow).mp
      inferInstance (by
        simpa only [← ConcreteCategory.comp_apply, j, Subobject.ofLE_arrow] using hz)
    rw [← hy]
    exact ConcreteCategory.congr_hom (cokernel.condition j) z

private theorem cokernel_map_apply
    {A B A' B' : AddCommGrpCat.{u + 1}} (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ g) (x : B) :
    (cokernel.map f g a b h) (cokernel.π f x) = cokernel.π g (b x) := by
  exact ConcreteCategory.congr_hom (cokernel.π_desc f (b ≫ cokernel.π g) _) x

set_option backward.isDefEq.respectTransparency false in
-- The dependent first-page and graded-class witnesses are elaborated together.
set_option maxRecDepth 1000000 in
set_option linter.unusedVariables false in
/-- Functorial hypercohomology pages identify image-filtration classes with stable pages.
This constructs the pages and their graded-class dictionary; it does not assert
continuity or that a kernel class eventually lies in a deeper step.
Source: Stacks Project, Tag 015J, and Tag 0EZM, proof of Lemma 59.52.1.

Proof: Apply the functorial Cartan--Eilenberg hypercohomology presentation to each
bounded-below complex, every transition pair, and each cocone pair at the limit.
The identity and composition laws give E and the compatible maps v. Swap the two
bidegree coordinates so that resolution degree comes first. The first-page
identifications are ordinary sheaf cohomology; functoriality gives exactly the two
first-page equations. Negative resolution degrees are zero. The limit complex
vanishes below a because inverse image preserves zero objects and complex colimits
are degreewise. The support region r >= 0, s >= a gives a single stable page N in
bidegree (p-q,q), simultaneously for all stages and the limit. Identify that page
with the q-th graded piece of the abutment filtration. This filtration equals the
predicate in the statement: a map T -> F with T zero below q factors through the
stupid truncation F^{>=q}, and its inclusion gives the converse. Define classMap
by the quotient projection and the inverse convergence isomorphism, transporting
along eH. Its kernel is the (q+1)-st step. Naturality gives transition_mem and
class_transition, using hH and hP to identify abutment maps. A class whose canonical
limit image is zero has zero limit graded projection, giving class_limit_zero.
These assertions use no sheaf-continuity or colimit-injectivity assertion.
(blueprint: lem-weil-pbc-etale-complex-filtration-page-data). -/
theorem exists_etaleComplexFiltrationPageData
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
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (q : ℤ) :
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
        (firstIso i r s).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v (op i)).hom 1 (le_refl 1)).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
          ((eG i).inv ≫ L.ι.app (op i)) r s)
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E.obj i).page 1 (le_refl 1)).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1 (le_refl 1)).X ⟨r, s⟩))
      (N : ℤ)
      (one_le : 1 ≤ N)
      (classMap : ∀ (i : I) (x : H.obj (op i)),
      InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x) →
        ((E.obj (op i)).page N one_le).X ⟨p - q, q⟩)
      (transition_mem : ∀ (i j : I) (f : j ⟶ i) (x : H.obj (op i)),
      InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x) →
        InEtaleHypercohomologyFiltration (D.obj j) (F j) p q
          ((eH j).hom (H.map f.op x)))
      (class_transition : ∀ (i j : I) (f : j ⟶ i) (x : H.obj (op i))
      (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)),
      (((E.map f.op).hom N one_le).f ⟨p - q, q⟩) (classMap i x hx) =
        classMap j (H.map f.op x) (transition_mem i j f x hx))
      (class_eq_zero_iff : ∀ (i : I) (x : H.obj (op i))
      (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)),
      classMap i x hx = 0 ↔
        InEtaleHypercohomologyFiltration (D.obj i) (F i) p (q + 1) ((eH i).hom x))
      ,
      ∀ (i : I) (x : H.obj (op i))
    (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)),
    ((eH i).hom ≫ P (c.π.app i) (F i) ≫
      (cohomology AddCommGrpCat.{u + 1} c.pt p).map
        (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) x = 0 →
    (((v (op i)).hom N one_le).f ⟨p - q, q⟩) (classMap i x hx) = 0 := by
  classical
  obtain ⟨E, E', v, compatible, firstIso, firstIsoLimit, first_transition,
    first_comparison, negative, negativeLimit, hFK, hLK, T, T', N, one_le,
    e, e', ht, ht'⟩ := exists_etaleComplex_uniform_pages D c F φ hidentity
      hcomposition a hbelow G eG hG p P hP L hL q
  clear hidentity hcomposition hbelow hG hP hL a
  have mem : ∀ (i : I) (z : ℤ) (x : H.obj (op i)),
      InEtaleHypercohomologyFiltration (D.obj i) (F i) p z ((eH i).hom x) ↔
        ∃ y : (((T i).H p).step z : AddCommGrpCat.{u + 1}),
          (((T i).H p).step z).arrow y = (eH i).hom x := by
    intro i z x
    exact etalePresentation_image_filtration (D.obj i) ⟨F i, hFK i⟩ (T i) p z _
  let y (i : I) (x : H.obj (op i))
      (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)) :
      (((T i).H p).step q : AddCommGrpCat.{u + 1}) :=
    Classical.choose ((mem i q x).mp hx)
  have hy (i : I) (x : H.obj (op i))
      (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)) :
      (((T i).H p).step q).arrow (y i x hx) = (eH i).hom x :=
    Classical.choose_spec ((mem i q x).mp hx)
  let classMap := fun i x hx ↦ (e i).inv
    (cokernel.π (Subobject.ofLE (((T i).H p).step (q + 1)) (((T i).H p).step q)
      (((T i).H p).antitone_step (Int.le_add_one (le_refl _)))) (y i x hx))
  have transition_mem : ∀ (i j : I) (f : j ⟶ i) (x : H.obj (op i)),
      InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x) →
        InEtaleHypercohomologyFiltration (D.obj j) (F j) p q
          ((eH j).hom (H.map f.op x)) := by
    intro i j f x hx
    obtain ⟨t, ht, hc, hs⟩ := ht i j f
    apply (mem j q _).mpr
    refine ⟨t q (y i x hx), ?_⟩
    have hh := ConcreteCategory.congr_hom (ht q) (y i x hx)
    simp only [ConcreteCategory.comp_apply] at hh
    rw [hh, hy i x hx, hH]
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  refine ⟨E, E', v, compatible, firstIso, firstIsoLimit, first_transition,
    first_comparison, negative, negativeLimit, N, one_le, classMap, transition_mem,
    ?_, ?_, ?_⟩
  · intro i j f x hx
    obtain ⟨t, ht, hc, hs⟩ := ht i j f
    have hrep : t q (y i x hx) = y j (H.map f.op x) (transition_mem i j f x hx) := by
      apply (AddCommGrpCat.mono_iff_injective (((T j).H p).step q).arrow).mp
        inferInstance
      have hh := ConcreteCategory.congr_hom (ht q) (y i x hx)
      simp only [ConcreteCategory.comp_apply] at hh
      rw [hh, hy i x hx, hy j (H.map f.op x) (transition_mem i j f x hx), hH]
      simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
    apply (AddCommGrpCat.mono_iff_injective (e j).hom).mp inferInstance
    have hh := ConcreteCategory.congr_hom hs (classMap i x hx)
    simp only [classMap, ConcreteCategory.comp_apply,
      Iso.inv_hom_id_apply] at hh ⊢
    let j' := Subobject.ofLE (((T j).H p).step (q + 1)) (((T j).H p).step q)
      (((T j).H p).antitone_step (Int.le_add_one (le_refl q)))
    exact hh.trans ((cokernel_map_apply _ _ (t (q + 1)) (t q) (hc q)
      (y i x hx)).trans (congrArg (fun z ↦ cokernel.π j' z) hrep))
  · intro i x hx
    have hz : classMap i x hx = 0 ↔
        cokernel.π (Subobject.ofLE (((T i).H p).step (q + 1)) (((T i).H p).step q)
          (((T i).H p).antitone_step (Int.le_add_one (le_refl _)))) (y i x hx) = 0 := by
      change (e i).inv.hom _ = 0 ↔ _
      exact map_eq_zero_iff (e i).inv.hom
        ((AddCommGrpCat.mono_iff_injective (e i).inv).mp inferInstance)
    rw [hz, step_quotient_zero_iff, mem]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, hz.trans (hy i x hx)⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, hz.trans (hy i x hx).symm⟩
  · intro i x hx hzero
    obtain ⟨t, ht, hc, hs⟩ := ht' i
    have hty : t q (y i x hx) = 0 := by
      apply (AddCommGrpCat.mono_iff_injective ((T'.H p).step q).arrow).mp inferInstance
      have hh := ConcreteCategory.congr_hom (ht q) (y i x hx)
      simp only [ConcreteCategory.comp_apply] at hh
      rw [hh, map_zero]
      rw [hy i x hx]
      simpa only [ConcreteCategory.comp_apply, Functor.const_obj_obj] using hzero
    apply (AddCommGrpCat.mono_iff_injective e'.hom).mp inferInstance
    have hh := ConcreteCategory.congr_hom hs (classMap i x hx)
    simp only [classMap, ConcreteCategory.comp_apply,
      Iso.inv_hom_id_apply] at hh
    have hk := cokernel_map_apply _ _ (t (q + 1)) (t q) (hc q) (y i x hx)
    let j' := Subobject.ofLE ((T'.H p).step (q + 1)) ((T'.H p).step q)
      ((T'.H p).antitone_step (Int.le_add_one (le_refl q)))
    have hz : cokernel.π j' (t q (y i x hx)) = 0 := by
      rw [hty]
      exact (cokernel.π j').hom.map_zero
    exact hh.trans (hk.trans (hz.trans e'.hom.hom.map_zero.symm))

end AlgebraicGeometry.Etale
