/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleComplexGradedClassDescent

/-! # Etale complex class descent

The descent half of the finite spectral-sequence comparison in Stacks Tag 0EZM.
(blueprint: lem-weil-pbc-etale-complex-class-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Every limit hypercohomology class has a stage representative.
Source: Stacks Project, Tag 0EZM, proof of lemma-colimit-variant-complexes;
Tag 015J (termwise hypercohomology spectral sequence).
(blueprint: lem-weil-pbc-etale-complex-class-descent).

Proof: First choose a directed cofinal reindexing of the filtered opposite
index category (Tag 0032), preserving the scheme limit and complex colimit.
For descent, a representative at a reindexed stage is already an original-stage
representative. For vanishing at an arbitrary original stage i, finality first
supplies an arrow from i to a reindexed stage in the opposite category. Transport
the class there, find its later zero witness in the directed system, and compose
the two arrows back in the original category. Apply sheaf continuity (09YQ) to
each term of the system.
Choose the functorial
termwise hypercohomology spectral sequences of Tag 015J. Exactness of filtered
colimits of abelian groups propagates the first-page comparison isomorphisms
through kernels modulo images to every subsequent page.
The common region
r >= 0, s >= a bounds the relevant entries in total degree p by a <= s <= p;
therefore their stabilization bounds are independent of the stage. The stable
page comparisons are surjective. Lift a limit class one graded piece at a time
through the finite abutment filtration, subtracting a stage representative at
each step. Filteredness moves the finitely many representatives to one common
stage, where their sum represents the original class. For p < a all abutments
are zero and any stage represents zero. Pullback functoriality identifies the
filtered abutment maps with P followed by the complex maps; hB and eB transport
the resulting representative to the displayed cocone leg. -/
theorem exists_etale_complex_class_rep
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
    ∀ x : B.pt, ∃ (i : I) (y : H.obj (op i)), B.ι.app (op i) y = x := by
  classical
  obtain ⟨S, htop, hbot, _hanti, hgraded⟩ := exists_etale_complex_graded_class_rep
    D c hc F φ hidentity hcomposition a hbelow G eG hG p P hP H eH hH L hL B eB hB
  let N := (p + 1 - a).toNat
  -- Descend through the finite filtration. Two representatives can be added
  -- after moving to a common stage of the filtered opposite category.
  have hstep : ∀ k : ℕ, k ≤ N → ∀ x : B.pt, x ∈ S (N - k) →
      ∃ (i : I) (y : H.obj (op i)), B.ι.app (op i) y = x := by
    intro k
    induction k with
    | zero =>
      intro _ x hx
      have hx0 : x = 0 := by simpa [N, hbot] using hx
      obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
      refine ⟨i, 0, ?_⟩
      rw [hx0]
      exact map_zero (B.ι.app (op i)).hom
    | succ k ih =>
      intro hk x hx
      have hn : N - (k + 1) < N := by omega
      obtain ⟨i, y, hy⟩ := hgraded (N - (k + 1)) hn x hx
      have heq : N - (k + 1) + 1 = N - k := by omega
      rw [heq] at hy
      obtain ⟨j, z, hz⟩ := ih (by omega) (@Sub.sub B.pt inferInstance x (B.ι.app (op i) y)) hy
      let t := IsFiltered.max (op i) (op j)
      let f : op i ⟶ t := IsFiltered.leftToMax (op i) (op j)
      let g : op j ⟶ t := IsFiltered.rightToMax (op i) (op j)
      refine ⟨t.unop, H.map f y + H.map g z, ?_⟩
      have hf : B.ι.app t (H.map f y) = B.ι.app (op i) y :=
        congrArg (fun e : H.obj (op i) ⟶ B.pt ↦ e y) (B.w f)
      have hg : B.ι.app t (H.map g z) = B.ι.app (op j) z :=
        congrArg (fun e : H.obj (op j) ⟶ B.pt ↦ e z) (B.w g)
      change B.ι.app t (H.map f y + H.map g z) = x
      rw [map_add, hf, hg, hz]
      let w : B.pt := B.ι.app (op i) y
      change w + (x - w) = x
      exact add_sub_cancel w x
  intro x
  apply hstep N (le_refl N) x
  simp [htop]

end AlgebraicGeometry.Etale
