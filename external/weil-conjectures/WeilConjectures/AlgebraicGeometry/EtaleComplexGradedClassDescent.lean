/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleComplexFirstPageAbutment
import WeilConjectures.CategoryTheory.SpectralSequenceFinitePageComparison
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Etale complex graded class descent

The graded lifting step of the finite spectral-sequence comparison in Stacks Tag 0EZM.
(blueprint: lem-weil-pbc-etale-complex-graded-class-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The finite abutment filtration has stage representatives on each graded piece.
Source: Stacks Project, Tags 0EZM and 015J, finite-term spectral-sequence comparison.
(blueprint: lem-weil-pbc-etale-complex-graded-class-descent).

Proof: Reindex the filtered opposite category by a nonempty directed cofinal
system (0032). Termwise sheaf continuity (09YQ) identifies the colimit of the
first pages with the first page on the limit. Use the functorial termwise
hypercohomology spectral sequences of 015J, with bidegrees (complex degree,
resolution degree). Filtered colimits of abelian groups preserve homology.
Starting with the first-page comparison, induct on r: compatibility with
differentials identifies the colimit short complex of incoming and outgoing
differentials with the target short complex. Preservation of homology and the
page isomorphisms give the comparison isomorphism on page r+1. Vanishing outside
complex degree >= a and resolution degree >= 0 persists because the next page
is homology. At bidegree (s,t), incoming and outgoing differentials
are zero once r > max (t+1) (s-a); this bound is independent of the stage.
Consequently the stable-page comparison is an isomorphism in every bidegree.

The abutment filtration in degree p is whole at a and zero at p+1. Pull it
back along eB and set S n to its step a+n. If p<a, the entire abutment is zero,
so S 0 is both whole and zero. Otherwise the length is (p+1-a).toNat. For
x in S n, identify its coset modulo S (n+1) with its stable-page class in
bidegree (a+n,p-a-n). The stable-page colimit isomorphism gives a representative
at one stage. Convergence identifies that representative with a coset in the
stage abutment filtration. Choose a lift y in that stage filtration step.
Functoriality of convergence identifies its image coset with that of x, so
x minus its image belongs to S (n+1). The abutment clause of pullback
functoriality, hP, hH and hB identify this image with B.ι.app (op i) y.
A stage of the cofinal system is also an original stage. This proves the
asserted graded lifting property without combining the different pieces. -/
theorem exists_etale_complex_graded_class_rep
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
    ∃ S : ℕ → AddSubgroup B.pt,
      S 0 = ⊤ ∧ S (p + 1 - a).toNat = ⊥ ∧ Antitone S ∧
      ∀ (n : ℕ), n < (p + 1 - a).toNat → ∀ x : B.pt, x ∈ S n →
        ∃ (i : I) (y : H.obj (op i)),
          @Sub.sub B.pt inferInstance x (B.ι.app (op i) y) ∈ S (n + 1) := by
  classical
  obtain ⟨J, hJ, hdir, hne, k, E, E', v, S, hv, hpage, htop, hbot, hanti, hmodels⟩ :=
    exists_etale_complex_first_page_and_abutment
      D c hc F φ hidentity hcomposition a hbelow G eG hG p P hP H eH hH L hL B eB hB
  let := hJ
  let := hdir
  let := hne
  refine ⟨S, htop, hbot, hanti, ?_⟩
  intro n hn x hx
  obtain ⟨r, hr, T, q, t, hker, ht, hcompat⟩ := hmodels n hn
  let Q := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
    (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 r hr ⋙
      HomologicalComplex.eval _ _ ⟨p - a - n, a + n⟩
  let C : Cocone Q :=
    { pt := (E'.page r hr).X ⟨p - a - n, a + n⟩
      ι :=
        { app := fun j ↦ ((v j).hom r hr).f ⟨p - a - n, a + n⟩
          naturality := by
            intro i j f
            simpa [Q] using congrArg
              (fun w : E.obj i ⟶ E' ↦ (w.hom r hr).f ⟨p - a - n, a + n⟩) (hv f) } }
  let ψ : colimit Q ⟶ C.pt := colimit.desc Q C
  have hψ : ∀ j : J, colimit.ι Q j ≫ ψ = ((v j).hom r hr).f ⟨p - a - n, a + n⟩ :=
    fun j ↦ colimit.ι_desc C j
  have : IsIso ψ := spectral_sequence_finite_page_comparison
    E E' v hv hpage r hr (p - a - n) (a + n) ψ hψ
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective ψ).mp inferInstance (q ⟨x, hx⟩)
  obtain ⟨j, w, hw⟩ := Concrete.colimit_exists_rep Q z
  obtain ⟨y, hy⟩ := ht j w
  obtain ⟨himage, hq⟩ := hcompat j y
  refine ⟨k j, y, ?_⟩
  apply (hker (⟨x, hx⟩ - ⟨B.ι.app (op (k j)) y, himage⟩)).mp
  rw [map_sub, hq, hy]
  have heq : ((v j).hom r hr).f ⟨p - a - n, a + n⟩ w = q ⟨x, hx⟩ := by
    rw [← hψ j]
    change ψ (colimit.ι Q j w) = q ⟨x, hx⟩
    rw [hw, hz]
  rw [heq, sub_self]

end AlgebraicGeometry.Etale
