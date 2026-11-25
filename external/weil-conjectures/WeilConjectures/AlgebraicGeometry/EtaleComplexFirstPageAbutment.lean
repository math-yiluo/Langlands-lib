/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import WeilConjectures.AlgebraicGeometry.EtaleComplexAbutmentPresentations
import WeilConjectures.AlgebraicGeometry.EtaleComplexFirstPageContinuity

/-! # First-page comparison and abutment quotient models

Source: Stacks Project, Tag 0EZM, proof of lemma-colimit-variant-complexes,
and Tags 015J and 015K.
(blueprint: lem-weil-pbc-etale-complex-first-page-abutment).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Assemble the termwise continuity comparison and its finite abutment quotient models.
This statement asserts comparison only on page one, not on the pages modeling the quotients.
The bidegrees here are (resolution degree, complex degree), matching the finite-page tool.
Source: Stacks Project, Tag 0EZM (lemma-colimit-variant-complexes), proof;
Tags 0032, 09YQ, 015J and 015K.
(blueprint: lem-weil-pbc-etale-complex-first-page-abutment).

Proof:
1. Apply exists_directed_reindexing to Iᵒᵖ with index A in universe u. Whisker
   the scheme limit and complex colimit with this same final functor. Evaluate
   the complex colimit degreewise. Exact inverse image and termwise colimits
   preserve the lower bound a. After the continuity calculation on A in step 2,
   set J = ULift A in universe u+1 and transport the diagram along this equivalence.
   This preserves its colimit cocones and selects the original stages k.
2. Choose termwise Cartan--Eilenberg hypercohomology presentations and the maps of
   exists_etaleHypercohomology_pullback_functorial for the stage transitions and limit legs.
   Their identity and composition equations assemble E and v. Swap the two coordinates
   from (complex,resolution) to (resolution,complex), yielding shape (1-r,r).
   In nonnegative resolution degrees, nonempty_isColimit_etale_cohomology_of_isLimit
   applied on A identifies the first-page comparison as an isomorphism. In negative
   resolution degrees all terms vanish. Transport this colimit cocone from A to J;
   the universal property proves the displayed page-one comparison on J.
3. The support region is resolution degree >=0 and complex degree >=a. Each later
   page is homology, so the region persists. At (t,s), both differentials vanish
   once r>max(t+1,s-a), uniformly at all stages and at the limit. The canonical
   subquotient descriptions of convergence therefore identify one common finite
   page with all the abutment graded pieces, naturally for v.
4. Transport the limit abutment filtration along eB and let S n be its step a+n.
   Its whole and zero bounds give S 0=top and S (p+1-a).toNat=bottom. If p<a,
   the degree-p abutment vanishes, so the length-zero case has both bounds at zero.
   Monotonicity gives Antitone S. Let T j be the corresponding stage filtration step.
5. For n below the length, choose the uniform page from step 3. The quotient
   projection followed by the inverse convergence isomorphism gives q and t j.
   The kernel of q is precisely S (n+1), and each t j is surjective because a
   quotient projection is surjective. Filtered abutment functoriality preserves
   the steps and commutes with these projections. The abutment comparison equations,
   together with hP, hH and hB, identify its underlying map with B.ι.app (op (k j)).
   This gives hy and the last equality. No page-r colimit comparison or choice of
   a stage representative of a target class is used in this construction. -/
theorem exists_etale_complex_first_page_and_abutment
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
    (B : Cocone H)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) :
    ∃ (J : Type (u + 1)) (_ : Preorder J) (_ : IsDirected J (· ≤ ·))
      (_ : Nonempty J) (k : J → I)
      (E : J ⥤ SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v : ∀ j : J, E.obj j ⟶ E') (S : ℕ → AddSubgroup B.pt),
      (∀ {i j : J} (f : i ⟶ j), E.map f ≫ v j = v i) ∧
      (∀ (s t : ℤ)
        (ψ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
          (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
          HomologicalComplex.eval _ _ ⟨s, t⟩) ⟶ (E'.page 1).X ⟨s, t⟩),
        (∀ j : J, colimit.ι _ j ≫ ψ = ((v j).hom 1).f ⟨s, t⟩) → IsIso ψ) ∧
      S 0 = ⊤ ∧ S (p + 1 - a).toNat = ⊥ ∧ Antitone S ∧
      ∀ n : ℕ, n < (p + 1 - a).toNat →
        ∃ (r : ℤ) (hr : 1 ≤ r) (T : ∀ j : J, AddSubgroup (H.obj (op (k j))))
          (q : S n →+ (E'.page r hr).X ⟨p - a - n, a + n⟩)
          (t : ∀ j : J, T j →+ ((E.obj j).page r hr).X ⟨p - a - n, a + n⟩),
          (∀ x : S n, q x = 0 ↔ (x : B.pt) ∈ S (n + 1)) ∧
          (∀ j : J, Function.Surjective (t j)) ∧
          ∀ (j : J) (y : T j),
            ∃ hy : B.ι.app (op (k j)) (y : H.obj (op (k j))) ∈ S n,
              q ⟨B.ι.app (op (k j)) (y : H.obj (op (k j))), hy⟩ =
                ((v j).hom r hr).f ⟨p - a - n, a + n⟩ (t j y) := by
  classical
  obtain ⟨J, hJ, hd, hn, R, hR, E0, E', v0, hv0,
    firstIso, firstIsoLimit, first_transition, first_comparison, negative, negativeLimit,
    S, htop, hbot, hanti, hmodels⟩ :=
    exists_etale_complex_abutment_presentations
      D c F φ hidentity hcomposition a hbelow G eG hG p P hP H eH hH L hL B eB hB
  let := hJ
  let := hd
  let := hn
  let := hR
  refine ⟨J, hJ, hd, hn, (fun j ↦ (R.obj j).unop), R ⋙ E0, E',
    (fun j ↦ v0 (R.obj j)), S, ?_, ?_, htop, hbot, hanti, hmodels⟩
  · intro i j f
    exact hv0 (R.map f)
  · intro s t ψ hψ
    apply reindex_first_page_comparison R hR E0 E' v0 hv0
    · intro s t ψ hψ
      exact etale_complex_first_page_continuity
        D c hc F φ hidentity hcomposition a hbelow G eG hG p P hP H eH hH L hL a
        E0 E' v0 hv0 firstIso firstIsoLimit first_transition first_comparison
        negative negativeLimit s t ψ hψ
    · exact hψ


end AlgebraicGeometry.Etale
