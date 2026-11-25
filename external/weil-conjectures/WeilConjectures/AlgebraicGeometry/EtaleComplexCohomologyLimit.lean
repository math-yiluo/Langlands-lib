/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.EtaleComplexClassDescent
import WeilConjectures.AlgebraicGeometry.EtaleComplexClassVanishing
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Continuity of etale cohomology for systems of complexes

Source: Stacks Project, Etale Cohomology, Lemma 59.52.1, Tag 0EZM
(blueprint: lem-weil-pbc-etale-cohomology-limit-complex-systems).

The diagrams and their object isomorphisms below present the varying-site system on the
limit site and its cohomology diagram. The parameter `P` is fixed by an explicit equation
with the derived adjunction unit, so the conclusion concerns the canonical map.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Uniformly bounded-below systems of abelian etale complexes satisfy cohomology continuity.
Source: Stacks Project, Tag 0EZM
(blueprint: lem-weil-pbc-etale-cohomology-limit-complex-systems).

Proof:
1. Apply lem-weil-pbc-etale-cohomology-limit-of-schemes (Tag 09YQ) to every degree
   of the complex system. The termwise colimit has the prescribed cohomology in each
   sheaf degree.
2. Apply thm-sp-if-e1 to global sections, using def-sp-etale-dictionary and
   def-sp-kinjective-bridge. The first-page entries are H^r(X_i,F_i^s).
   Their colimits are H^r(X,F^s) by step 1. The entries vanish for r < 0 or s < a.
   In total degree n only a <= s <= n occurs, uniformly in the stage. This gives
   uniform stabilization and finite filtrations by thm-sp-spectral-object-yields.
   The four hypotheses of lem-weil-pbc-complex-spectral-sequence-comparison therefore
   hold: first-page continuity, the common vanishing region, uniform stabilization,
   and the finite abutment filtration with its associated-graded identification.
3. The maps supplied by lem-weil-pbc-hypercohomology-e1-pullback-functorial are
   compatible by the cocycle law and lem-weil-pbc-inverse-image-composition. Their
   abutments are the canonical derived pullback maps, namely `P` followed by the
   maps of complexes, by def-weil-pbc-etale-cohomology. Thus the comparison gives
   exactly the cocone `B`, proving its colimit universal property.
-/
theorem nonempty_isColimit_etale_complex_cohomology
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
    Nonempty (IsColimit B) := by
  classical
  have hsurj := exists_etale_complex_class_rep D c hc F φ hidentity hcomposition
    a hbelow G eG hG p P hP H eH hH L hL B eB hB
  have hzero := exists_etale_complex_class_eq_zero D c hc F φ hidentity hcomposition
    a hbelow G eG hG p P hP H eH hH L hL B eB hB
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  have := reflectsColimit_of_reflectsIsomorphisms H (forget AddCommGrpCat)
  refine ⟨isColimitOfReflects (forget AddCommGrpCat) ?_⟩
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨op i, y, hy.symm⟩
  · intro i x y hxy
    change B.ι.app i x = B.ι.app i y at hxy
    have hz : B.ι.app i (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨j, f, hf⟩ := hzero i.unop (x - y) hz
    refine ⟨op j, f.op, ?_⟩
    change H.map f.op x = H.map f.op y
    exact sub_eq_zero.mp (by simpa only [map_sub] using hf)

end AlgebraicGeometry.Etale
