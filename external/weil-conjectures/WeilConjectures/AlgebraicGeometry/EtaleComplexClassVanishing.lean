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
import WeilConjectures.AlgebraicGeometry.EtaleComplexFiltrationDeepening
import WeilConjectures.AlgebraicGeometry.EtaleHypercohomologyFiltration

/-! # Etale complex class vanishing

The vanishing half of the finite spectral-sequence comparison in Stacks Tag 0EZM.
(blueprint: lem-weil-pbc-etale-complex-class-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A stage hypercohomology class vanishing on the limit eventually vanishes.
Source: Stacks Project, Tag 0EZM, proof of lemma-colimit-variant-complexes;
Tag 015J (termwise hypercohomology spectral sequence).
(blueprint: lem-weil-pbc-etale-complex-class-vanishing).

Proof: First choose a directed cofinal reindexing of the filtered opposite
index category (Tag 0032), preserving the scheme limit and complex colimit.
For descent, a representative at a reindexed stage is already an original-stage
representative. For vanishing at an arbitrary original stage i, finality first
supplies an arrow from i to a reindexed stage in the opposite category. Transport
the class there, find its later zero witness in the directed system, and compose
the two arrows back in the original category. Apply 09YQ to the system in each
complex degree and use the functorial first hypercohomology spectral sequences
of 015J. Exact filtered colimits propagate
first-page comparison isomorphisms through the page homology construction.
The vanishing region r >= 0, s >= a gives a uniform stabilization bound in each
bidegree and finite abutment filtrations in total degree p. If a stage class
maps to zero, its leading nonzero graded component becomes zero on the limit
stable page, and thus becomes zero at a later stage. At that stage the class
lies one step deeper in the filtration. Repeat through the finite range
a <= s <= p; after a finite number of transitions it lies in the zero step.
Compose the transitions (filteredness supplies common refinements whenever
needed). Functoriality of the spectral sequence identifies the transition on
abutments with P followed by the map of complexes; hH gives precisely H.map.
The equation hB and the injective isomorphism eB identify the initial vanishing
condition with vanishing in the derived limit abutment. If p < a all stage
abutments are zero, so the identity transition suffices. -/
theorem exists_etale_complex_class_eq_zero
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
    ∀ (i : I) (x : H.obj (op i)), B.ι.app (op i) x = 0 →
      ∃ (j : I) (f : j ⟶ i), H.map f.op x = 0 := by
  intro i x hx
  have hsteps : ∀ n : ℕ, ∃ (j : I) (f : j ⟶ i),
      InEtaleHypercohomologyFiltration (D.obj j) (F j) p (a + n)
        ((eH j).hom (H.map f.op x)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨i, 𝟙 i, ?_⟩
      simp only [Nat.cast_zero, add_zero]
      refine ⟨F i, hbelow i, 𝟙 _, (eH i).hom x, ?_⟩
      simp
    | succ n ih =>
      obtain ⟨j, f, hf⟩ := ih
      have hz : B.ι.app (op j) (H.map f.op x) = 0 := by
        have hn := congrArg (fun t => t x) (B.w f.op)
        change B.ι.app (op j) (H.map f.op x) = B.ι.app (op i) x at hn
        exact hn.trans hx
      have hcanon : ((eH j).hom ≫ P (c.π.app j) (F j) ≫
          (cohomology AddCommGrpCat.{u + 1} c.pt p).map
            (DerivedCategory.Q.map ((eG j).inv ≫ L.ι.app (op j))))
          (H.map f.op x) = 0 := by
        rw [← hB j]
        simpa using congrArg (fun y => eB.hom y) hz
      obtain ⟨k, g, hg⟩ := exists_etale_complex_class_in_next_filtration
        D c hc F φ hidentity hcomposition a hbelow G eG hG p P hP H eH hH L hL
        (a + n) j (H.map f.op x) hf hcanon
      refine ⟨k, g ≫ f, ?_⟩
      simpa only [Nat.cast_succ, ← add_assoc, op_comp, Functor.map_comp,
        AddCommGrpCat.comp_apply] using hg
  obtain ⟨j, f, hf⟩ := hsteps (p - a + 1).toNat
  have hp : p < a + ((p - a + 1).toNat : ℤ) := by omega
  have hz := eq_zero_of_inEtaleHypercohomologyFiltration (D.obj j) (F j) p
    (a + ((p - a + 1).toNat : ℤ)) hp ((eH j).hom (H.map f.op x)) hf
  refine ⟨j, f, ?_⟩
  have h := congrArg (fun y => (eH j).inv y) hz
  simpa using h


end AlgebraicGeometry.Etale
