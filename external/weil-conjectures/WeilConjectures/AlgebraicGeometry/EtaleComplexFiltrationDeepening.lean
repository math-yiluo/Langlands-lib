/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.EtaleHypercohomologyFiltration
import WeilConjectures.AlgebraicGeometry.EtaleComplexFirstPageContinuity
import WeilConjectures.CategoryTheory.SpectralSequenceFinitePageComparison
import Mathlib.CategoryTheory.Presentable.Directed
import all Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Deepening the etale hypercohomology image filtration

The vanishing half of the finite spectral-sequence comparison in Stacks Tag 0EZM.
(blueprint: lem-weil-pbc-etale-complex-filtration-deepening).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem finite_comparison_filtered
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (E : J ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (v : ∀ i : J, E.obj i ⟶ E')
    (hv : ∀ {i j : J} (f : i ⟶ j), E.map f ≫ v j = v i)
    (hpage : ∀ (p q : ℤ)
      (ψ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
        (fun t ↦ ComplexShape.up' (⟨1 - t, t⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨p, q⟩) ⟶ (E'.page 1).X ⟨p, q⟩),
      (∀ i : J, colimit.ι _ i ≫ ψ = ((v i).hom 1).f ⟨p, q⟩) → IsIso ψ)
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (ψ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
      (fun t ↦ ComplexShape.up' (⟨1 - t, t⟩ : ℤ × ℤ)) 1 r hr ⋙
      HomologicalComplex.eval _ _ ⟨p, q⟩) ⟶ (E'.page r hr).X ⟨p, q⟩)
    (hψ : ∀ i : J, colimit.ι _ i ≫ ψ = ((v i).hom r hr).f ⟨p, q⟩) :
    IsIso ψ := by
  classical
  obtain ⟨A, horder, hdirected, hnonempty, R₀, hfinal⟩ :=
    IsFiltered.exists_directed (AsSmall.{u + 1} J)
  let := horder
  let := hdirected
  let := hnonempty
  let := hfinal
  let R : A ⥤ J := R₀ ⋙ (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).inverse
  have : R.Final := by
    dsimp [R]
    infer_instance
  have hpageR : ∀ (s t : ℤ)
      (θ : colimit ((R ⋙ E) ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
        (fun k ↦ ComplexShape.up' (⟨1 - k, k⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨s, t⟩) ⟶ (E'.page 1).X ⟨s, t⟩),
      (∀ i : A, colimit.ι _ i ≫ θ = ((v (R.obj i)).hom 1).f ⟨s, t⟩) →
        IsIso θ := by
    intro s t θ hθ
    let Q := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
      (fun k ↦ ComplexShape.up' (⟨1 - k, k⟩ : ℤ × ℤ)) 1 1 ⋙
      HomologicalComplex.eval _ _ ⟨s, t⟩
    let η : colimit Q ⟶ (E'.page 1).X ⟨s, t⟩ := inv (colimit.pre Q R) ≫ θ
    have hηR (i : A) : colimit.ι Q (R.obj i) ≫ η =
        ((v (R.obj i)).hom 1).f ⟨s, t⟩ := by
      rw [← colimit.ι_pre Q R i]
      simpa only [η, Q, Functor.assoc, Category.assoc, IsIso.hom_inv_id_assoc]
        using hθ i
    have hη (i : J) : colimit.ι Q i ≫ η = ((v i).hom 1).f ⟨s, t⟩ := by
      let j := Functor.Final.lift R i
      let f : i ⟶ R.obj j := Functor.Final.homToLift R i
      calc
        colimit.ι Q i ≫ η = Q.map f ≫ (colimit.ι Q (R.obj j) ≫ η) := by
          simpa only [Category.assoc] using
            (congrArg (fun t ↦ t ≫ η) (colimit.w Q f)).symm
        _ = Q.map f ≫ ((v (R.obj j)).hom 1).f ⟨s, t⟩ := by rw [hηR]
        _ = ((v i).hom 1).f ⟨s, t⟩ := by
          exact congrArg (fun w ↦ (w.hom 1).f ⟨s, t⟩) (hv f)
    have : IsIso η := hpage s t η hη
    have hfactor : θ = colimit.pre Q R ≫ η := by simp [η]
    rw [hfactor]
    infer_instance
  let Q := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
    (fun t ↦ ComplexShape.up' (⟨1 - t, t⟩ : ℤ × ℤ)) 1 r hr ⋙
    HomologicalComplex.eval _ _ ⟨p, q⟩
  have hpre : ∀ i : A, colimit.ι (R ⋙ Q) i ≫ (colimit.pre Q R ≫ ψ) =
      ((v (R.obj i)).hom r hr).f ⟨p, q⟩ := by
    intro i
    rw [← Category.assoc, colimit.ι_pre, hψ]
  have : IsIso (colimit.pre Q R ≫ ψ) := spectral_sequence_finite_page_comparison
    (R ⋙ E) E' (fun i ↦ v (R.obj i)) (fun f ↦ hv (R.map f))
    hpageR r hr p q (colimit.pre Q R ≫ ψ) hpre
  have hfactor : ψ = inv (colimit.pre Q R) ≫ (colimit.pre Q R ≫ ψ) := by simp
  rw [hfactor]
  infer_instance

/-- A kernel class in one image-filtration step moves to the next step at a later stage.
Source: Stacks Project, Tag 0EZM, finite-term comparison, and Tag 015J.

Proof: Reindex the filtered opposite category by a directed cofinal set (Tag 0032).
Apply sheaf continuity (Tag 09YQ) in every complex degree. Functoriality of the first
hypercohomology spectral sequence identifies these maps with the page-one comparison.
Exact filtered colimits carry kernels and images to kernels and images, hence comparison
isomorphisms propagate to every page. The common support region `r >= 0, s >= a`
gives a stabilization bound independent of the stage in each bidegree. Thus the comparison
on the stable graded piece in filtration degree `q` is injective on filtered colimits.
The filtration here is the image from the stupid truncation in degrees at least `q`:
a map from any complex supported there factors through that truncation, and its inclusion
is itself such a map. A class in this step with zero limit image has zero limit graded
component. Stable-page injectivity implies that component is zero at a later stage,
so its transition image lies in the next filtration step. For an arbitrary original
stage, finality first gives a map to a reindexed stage; compose that map with the later
witness. Functoriality on abutments identifies the maps with `P` followed by `φ`;
`hH` identifies their transitions with `H.map`.
(blueprint: lem-weil-pbc-etale-complex-filtration-deepening). -/
theorem exists_etale_complex_class_in_next_filtration
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    (q : ℤ) (i : I) (x : H.obj (op i))
    (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x))
    (hz : ((eH i).hom ≫ P (c.π.app i) (F i) ≫
      (cohomology AddCommGrpCat.{u + 1} c.pt p).map
        (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) x = 0) :
    ∃ (j : I) (f : j ⟶ i),
      InEtaleHypercohomologyFiltration (D.obj j) (F j) p (q + 1)
        ((eH j).hom (H.map f.op x)) := by
  obtain ⟨E, E', v, compatible, firstIso, firstIsoLimit, first_transition,
      first_comparison, negative, negativeLimit, N, one_le, classMap, transition_mem,
      class_transition, class_eq_zero_iff, class_limit_zero⟩ :=
    exists_etaleComplexFiltrationPageData
    D c F φ hidentity hcomposition a hbelow G eG hG p P hP H eH hH L hL q
  have hfirst := etale_complex_first_page_continuity
    D c hc F φ hidentity hcomposition a hbelow G eG hG p P hP H eH hH L hL q
    E E' v compatible firstIso firstIsoLimit
    first_transition first_comparison negative negativeLimit
  let Q := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
    (fun t ↦ ComplexShape.up' (⟨1 - t, t⟩ : ℤ × ℤ)) 1 N one_le ⋙
    HomologicalComplex.eval _ _ ⟨p - q, q⟩
  let C : Cocone Q :=
    { pt := (E'.page N one_le).X ⟨p - q, q⟩
      ι :=
        { app := fun i ↦ ((v i).hom N one_le).f ⟨p - q, q⟩
          naturality := by
            intro i j f
            exact congrArg (fun w ↦ (w.hom N one_le).f ⟨p - q, q⟩)
              (compatible f) } }
  let θ : colimit Q ⟶ C.pt := colimit.desc Q C
  have hθ (i : Iᵒᵖ) : colimit.ι Q i ≫ θ =
      ((v i).hom N one_le).f ⟨p - q, q⟩ := colimit.ι_desc C i
  have : IsIso θ := finite_comparison_filtered
    E E' v compatible hfirst N one_le (p - q) q θ hθ
  have hzero : colimit.ι Q (op i) (classMap i x hx) = 0 := by
    apply (AddCommGrpCat.mono_iff_injective θ).1 inferInstance
    have h := congrArg (fun f ↦ f (classMap i x hx)) (hθ (op i))
    simpa using h.trans (class_limit_zero i x hx hz)
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨j, f, hf⟩ := ((colimit.isColimit Q).eq_iff'
    (classMap i x hx) 0).1 (by
      change (colimit.ι Q (op i)).hom (classMap i x hx) = (colimit.ι Q (op i)).hom 0
      simpa only [map_zero] using hzero)
  refine ⟨unop j, f.unop, ?_⟩
  apply (class_eq_zero_iff (unop j) (H.map f.unop.op x)
    (transition_mem i (unop j) f.unop x hx)).1
  rw [← class_transition i (unop j) f.unop x hx]
  change (Q.map f).hom (classMap i x hx) = (Q.map f).hom 0 at hf
  rw [map_zero] at hf
  change (((E.map f).hom N one_le).f ⟨p - q, q⟩).hom (classMap i x hx) = 0 at hf
  simpa only [Quiver.Hom.op_unop] using hf

end AlgebraicGeometry.Etale
