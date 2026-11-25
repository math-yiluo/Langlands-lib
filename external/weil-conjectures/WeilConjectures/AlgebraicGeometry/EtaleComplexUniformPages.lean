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
public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
import WeilConjectures.AlgebraicGeometry.EtaleHypercohomologyUniformBound
import WeilConjectures.AlgebraicGeometry.EtaleComplexPageDiagram
import WeilConjectures.AlgebraicGeometry.EtaleComplexColimitBelow
/-! # Uniform stable pages for a diagram of étale complexes

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-uniform-pages).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent presentation family and its naturality equations.
set_option linter.unusedVariables false in
/-- Uniform pages and natural graded comparisons, before choosing any class representatives.
Source: Stacks Project, Tags 015J and 0EZM, proof of Lemma 59.52.1.

Proof: Use the functorial Cartan--Eilenberg presentations of
`exists_etaleHypercohomology_pullback_functorial`. Give each F_i its bounded-below
structure with bound a. Inverse image is exact, and colimits of complexes are degreewise,
so L.pt has the same lower bound. The identity and composition equations for φ make
its page maps a functor; the equations for G and the cocone make the limit maps compatible.
Swap the two bidegree coordinates to put the resolution degree first. The first-page
identifications and their two naturality equations are the corresponding equations of
the pullback presentations. Their negative resolution degrees vanish. In bidegree
(p-q,q), incoming and outgoing differentials vanish once the page exceeds both the
resolution degree and the distance q-a to the bottom row. This bound depends only on
p,q,a, and therefore works simultaneously for all stages and the limit. Functorial
convergence identifies this page with the q-th graded piece of each presentation's
canonical image filtration. The filtered total maps restrict to all filtration steps;
their inclusion equations identify the abutment maps with P followed by the coefficient
map. Monicity gives the square for successive steps. Naturality of the stable-page
identification gives precisely cokernel.map on the associated graded pieces.
(blueprint: lem-weil-pbc-etale-complex-uniform-pages). -/
theorem exists_etaleComplex_uniform_pages
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
        (firstIso i r s).hom ≫ AddCommGrpCat.ofHom
          ((Sheaf.H.map ((φ f).f s) r).comp (cohomologyMap (D.map f) ((F i).X s) r)))
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v (op i)).hom 1 (le_refl 1)).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ AddCommGrpCat.ofHom
          ((Sheaf.H.map (((eG i).inv ≫ L.ι.app (op i)).f s) r).comp
            (cohomologyMap (c.π.app i) ((F i).X s) r)))
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E.obj i).page 1 (le_refl 1)).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1 (le_refl 1)).X ⟨r, s⟩))
      (hFK : ∀ i : I, CochainComplex.plus
        (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (F i))
      (hLK : CochainComplex.plus
        (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) L.pt)
      (T : ∀ i : I, EtaleTermwiseHypercohomology (D.obj i) ⟨F i, hFK i⟩)
      (T' : EtaleTermwiseHypercohomology c.pt ⟨L.pt, hLK⟩)
      (N : ℤ) (one_le : 1 ≤ N)
      (e : ∀ i : I, ((E.obj (op i)).page N one_le).X ⟨p - q, q⟩ ≅
        ((T i).H p).gradedPiece q)
      (e' : (E'.page N one_le).X ⟨p - q, q⟩ ≅ (T'.H p).gradedPiece q),
      (∀ (i j : I) (f : j ⟶ i),
        ∃ (t : ∀ z : ℤ, (((T i).H p).step z : AddCommGrpCat.{u + 1}) ⟶
            (((T j).H p).step z : AddCommGrpCat.{u + 1}))
          (ht : ∀ z : ℤ, t z ≫ (((T j).H p).step z).arrow =
            (((T i).H p).step z).arrow ≫
              P (D.map f) (F i) ≫
              (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
                (DerivedCategory.Q.map (φ f)))
          (hc : ∀ z : ℤ,
            Subobject.ofLE (((T i).H p).step (z + 1)) (((T i).H p).step z)
                (((T i).H p).antitone_step (Int.le_add_one (le_refl _))) ≫ t z =
              t (z + 1) ≫
                Subobject.ofLE (((T j).H p).step (z + 1)) (((T j).H p).step z)
                  (((T j).H p).antitone_step (Int.le_add_one (le_refl _)))),
          ((E.map f.op).hom N one_le).f ⟨p - q, q⟩ ≫ (e j).hom =
            (e i).hom ≫ cokernel.map _ _ (t (q + 1)) (t q) (hc q)) ∧
      (∀ i : I,
        ∃ (t : ∀ z : ℤ, (((T i).H p).step z : AddCommGrpCat.{u + 1}) ⟶
            ((T'.H p).step z : AddCommGrpCat.{u + 1}))
          (ht : ∀ z : ℤ, t z ≫ ((T'.H p).step z).arrow =
            (((T i).H p).step z).arrow ≫
              P (c.π.app i) (F i) ≫
              (cohomology AddCommGrpCat.{u + 1} c.pt p).map
                (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))))
          (hc : ∀ z : ℤ,
            Subobject.ofLE (((T i).H p).step (z + 1)) (((T i).H p).step z)
                (((T i).H p).antitone_step (Int.le_add_one (le_refl _))) ≫ t z =
              t (z + 1) ≫
                Subobject.ofLE ((T'.H p).step (z + 1)) ((T'.H p).step z)
                  ((T'.H p).antitone_step (Int.le_add_one (le_refl _)))),
          ((v (op i)).hom N one_le).f ⟨p - q, q⟩ ≫ e'.hom =
            (e i).hom ≫ cokernel.map _ _ (t (q + 1)) (t q) (hc q)) := by
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
    simp only [P₀, Functor.map_comp, Category.assoc]
    rfl
  obtain ⟨T₀, M, R, eInf, ⟨hfirst, hfiltered, hid, hcomp⟩, hbound⟩ :=
    exists_etaleHypercohomology_uniform_bound P₀ (by intros; rfl)
  obtain ⟨E, E', v, compatible, firstIso, firstIsoLimit, first_transition,
    first_comparison, negative, negativeLimit, pageIso, pageIsoLimit, hpage, hpageLimit⟩ :=
    exists_etaleComplex_page_diagram D c F φ hidentity hcomposition G eG hG L
      hFK hLK p q T₀ M hfirst (fun X K ↦ (hid X K).1)
        (fun f g K J V t w ↦ (hcomp f g K J V t w).1)
  let N := max 1 (max (q - a + 2) (p - q + 2))
  have one_le : 1 ≤ N := le_max_left _ _
  have hR : ∀ i : I, R (D.obj i) ⟨F i, hFK i⟩ q p ≤ N := by
    intro i
    exact hbound (D.obj i) ⟨F i, hFK i⟩ a q p (hbelow i)
  have hR' : R c.pt ⟨L.pt, hLK⟩ q p ≤ N :=
    hbound c.pt ⟨L.pt, hLK⟩ a q p hlimit
  let e := fun i ↦ pageIso i N one_le ≪≫
    eInf (D.obj i) ⟨F i, hFK i⟩ q p N one_le (hR i)
  let e' := pageIsoLimit N one_le ≪≫ eInf c.pt ⟨L.pt, hLK⟩ q p N one_le hR'
  refine ⟨E, E', v, compatible, firstIso, firstIsoLimit, first_transition,
    first_comparison, negative, negativeLimit, hFK, hLK,
    (fun i ↦ T₀ (D.obj i) ⟨F i, hFK i⟩), T₀ c.pt ⟨L.pt, hLK⟩,
    N, one_le, e, e', ?_, ?_⟩
  · intro i j f
    obtain ⟨t, ht, hc, hs⟩ := hfiltered (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f) p
    refine ⟨t, ?_, hc, ?_⟩
    · intro z
      simpa only [hP₀, Category.assoc] using ht z
    · dsimp only [e, Iso.trans_hom]
      calc
        _ = (pageIso i N one_le).hom ≫
            ((M (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f)).hom N one_le).f
              ⟨q, p - q⟩ ≫ (eInf (D.obj j) ⟨F j, hFK j⟩ q p N one_le (hR j)).hom := by
          rw [← Category.assoc, hpage i j f N one_le, Category.assoc]
        _ = _ := by
          have hh := congrArg ((pageIso i N one_le).hom ≫ ·)
            (hs q N one_le (hR i) (hR j))
          simpa only [Category.assoc] using hh
  · intro i
    obtain ⟨t, ht, hc, hs⟩ := hfiltered (X := D.obj i) (Y := c.pt) (c.π.app i)
      ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩
      ((eG i).inv ≫ L.ι.app (op i)) p
    refine ⟨t, ?_, hc, ?_⟩
    · intro z
      simpa only [hP₀, Category.assoc] using ht z
    · dsimp only [e, e', Iso.trans_hom]
      calc
        _ = (pageIso i N one_le).hom ≫
            ((M (c.π.app i) ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩
              ((eG i).inv ≫ L.ι.app (op i))).hom N one_le).f
                ⟨q, p - q⟩ ≫ (eInf c.pt ⟨L.pt, hLK⟩ q p N one_le hR').hom := by
          rw [← Category.assoc, hpageLimit i N one_le, Category.assoc]
        _ = _ := by
          have hh := congrArg ((pageIso i N one_le).hom ≫ ·)
            (hs q N one_le (hR i) hR')
          simpa only [Category.assoc] using hh


end AlgebraicGeometry.Etale
