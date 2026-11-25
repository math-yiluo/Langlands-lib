/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleComplexFiltrationPageData
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ComplexTermCohomologyColimit

/-! # Termwise continuity on the first hypercohomology page

Source: Stacks Project, Tag 0EZM, invoking Tag 09YQ in every complex degree.
(blueprint: lem-weil-pbc-etale-complex-first-page-continuity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

-- Resolve reflexive page bounds before inspecting the large dependent context.
local macro_rules
  | `(tactic| lia) => `(tactic| first | exact le_refl _ | omega)

-- The dependent first-page and graded-class witnesses are elaborated together.
set_option linter.unusedVariables false in
/-- Sheaf continuity gives the canonical isomorphism on each first-page term.
Only the first-page dictionary is used; no stable-page or abutment assertion
is part of this conclusion.
Source: Stacks Project, Tag 0EZM, proof of Lemma 59.52.1, and Theorem 59.51.3 (09YQ).

Proof: Reindex I.op by a nonempty directed cofinal set. Whiskering preserves the
complex colimit and the opposite scheme limit. Evaluate each complex in degree s;
complex colimits are degreewise, and the coherence equations hG, hidentity and
hcomposition evaluate to the corresponding sheaf-system equations. For r >= 0,
apply sheaf continuity in cohomological degree r.toNat to these sheaves. The
firstIso, first_transition and first_comparison equations identify its diagram
and cocone with the first-page diagram and its canonical cocone. Hence that
cocone is a colimit. For r < 0 all the source terms and target term are zero by
negative and negativeLimit, so the same cocone is a colimit. Cofinality transports
this conclusion back to I.op. Any displayed map from the chosen colimit with the
prescribed legs is the canonical comparison and is therefore an isomorphism.
The lower bound and all stable-page data are irrelevant to this argument.
(blueprint: lem-weil-pbc-etale-complex-first-page-continuity). -/
theorem etale_complex_first_page_continuity
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
    (q : ℤ)
(E : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v : ∀ i : Iᵒᵖ, E.obj i ⟶ E')
      (compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), E.map f ≫ v j = v i)
      (firstIso : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((E.obj (op i)).page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
      (firstIsoLimit : ∀ (r : ℕ) (s : ℤ),
      (E'.page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
      (first_transition : ∀ (i j : I) (f : j ⟶ i) (r : ℕ) (s : ℤ),
      ((E.map f.op).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIso j r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v (op i)).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
          ((eG i).inv ≫ L.ι.app (op i)) r s)
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E.obj i).page 1).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1).X ⟨r, s⟩)) :
    ∀ (r s : ℤ)
      (ψ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
        (fun t ↦ ComplexShape.up' (⟨1 - t, t⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨r, s⟩) ⟶ (E'.page 1).X ⟨r, s⟩),
      (∀ i : Iᵒᵖ, colimit.ι _ i ≫ ψ = ((v i).hom 1).f ⟨r, s⟩) →
        IsIso ψ := by
  intro r s ψ hψ
  let T := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
    (fun t ↦ ComplexShape.up' (⟨1 - t, t⟩ : ℤ × ℤ)) 1 1 (le_refl 1) ⋙
    HomologicalComplex.eval _ _ ⟨r, s⟩
  let B : Cocone T :=
    { pt := (E'.page 1 (le_refl 1)).X ⟨r, s⟩
      ι :=
        { app := fun i ↦ ((v i).hom 1 (le_refl 1)).f ⟨r, s⟩
          naturality := fun i j f ↦ by
            have h := congrArg (fun z ↦ (z.hom 1 (le_refl 1)).f ⟨r, s⟩) (compatible f)
            change ((E.map f).hom 1 (le_refl 1)).f ⟨r, s⟩ ≫ ((v j).hom 1 (le_refl 1)).f ⟨r, s⟩ =
              ((v i).hom 1 (le_refl 1)).f ⟨r, s⟩ ≫ 𝟙 _
            simpa only [Category.comp_id, SpectralSequence.comp_hom,
              HomologicalComplex.comp_f] using h } }
  have hB : Nonempty (IsColimit B) := by
    by_cases hr : r < 0
    · refine ⟨{ desc := ?_, fac := ?_, uniq := ?_ }⟩
      · intro S
        exact 0
      · intro S i
        exact (negative i r s hr).eq_of_src _ _
      · intro S m hm
        exact (negativeLimit r s hr).eq_of_src _ _
    · rcases Int.eq_ofNat_of_zero_le (le_of_not_gt hr) with ⟨n, hn⟩
      subst r
      exact nonempty_isColimit_complex_term_cohomology D c hc F φ hidentity
        hcomposition G eG hG L hL _ s T (fun i ↦ firstIso i _ s)
        (fun i j f ↦ first_transition i j f _ s) B (firstIsoLimit _ s)
        (fun i ↦ first_comparison i _ s)
  have heq : ψ = (colimit.isColimit T).desc B := by
    apply colimit.hom_ext
    intro i
    exact (hψ i).trans ((colimit.isColimit T).fac B i).symm
  rw [heq]
  exact ((colimit.isColimit T).nonempty_isColimit_iff_isIso_desc).mp hB

end AlgebraicGeometry.Etale
