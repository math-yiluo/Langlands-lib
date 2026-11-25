/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.FilteredComplexSpectralSequence
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration
import WeilConjectures.CategoryTheory.CartanEilenbergRowPages
import WeilConjectures.CategoryTheory.DegreewiseFilteredStableQuotient

/-! # The second-filtration spectral sequence and its total abutment

Source: blueprint thm-sp-if-e1, proof paragraph 1; Stacks Tags 0130 and 0132.
(blueprint: lem-sp-cartan-eilenberg-second-filtration).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The resolution-degree cohomology spectral sequence converges to the cohomology
of the mapped total complex. Its filtration may be transported to any isomorphic family.
This statement makes no claim that this total computes a derived functor on complexes.
Source: blueprint thm-sp-if-e1, proof paragraph 1; Stacks Tags 0130 and 0132.
(blueprint: lem-sp-cartan-eilenberg-second-filtration).

Proof.
1. Form the filtration by complex degree of the flipped, extended, F-mapped bicomplex.
The total differential preserves or raises complex degree, so these are subcomplexes.
If b bounds I below, the step is the whole object for p at most b and zero for p>n
in total degree n. This proves degreewise finiteness, also for n<b.
2. Apply the filtered-complex construction, retaining its page-zero differential and
cycle/boundary quotient identifications. Its first page is row cohomology, zero in
negative resolution degree. Each augmented row is an injective resolution by hterms
and hrows, so its F-cohomology is the ordinary right derived functor on K^s.
3. The second-filtration differential is (-1)^r times the row-cohomology map induced
by the complex differential (Stacks 0130). Multiply the row identification at (s,r)
by (-1)^(rs). The factors in consecutive complex degrees differ by (-1)^r, giving
the unsigned differential in the statement for all integer s and natural r.
4. In total degree n, the filtration and the adjacent degrees have finite support.
For a sufficiently large page the cycle and boundary subobjects are stationary and
their quotient is the graded piece of the image filtration on total cohomology.
That image filtration is finite. For any given family of isomorphisms c, take images
of its steps along c.hom. An isomorphism preserves top, bottom, inclusions and their
cokernels, so the transported filtration is finite, has the displayed steps, and
its graded pieces are isomorphic to the same stationary spectral-sequence terms. -/
theorem cartanEilenberg_second_filtration
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hterms : ∀ (s : ℤ) (r : ℕ), Injective ((I.X s).X r))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s)) :
    ∃ (L : DecreasingFiltration
        ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
          (ComplexShape.up ℤ)))
      (E : CohomologicalSpectralSequence B 0)
      (e₀ : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (L.gradedPiece p).X (p + q))
      (e₁ : ∀ (r : ℕ) (s : ℤ), (E.page 1).X (s, (r : ℤ)) ≅
        (F.rightDerived r).obj (K.obj.X s)),
      (∀ p n : ℤ, L.complexStep p n =
        ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
          p) ∧
      (∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e₀ p (q + 1)).hom =
        (e₀ p q).hom ≫ (L.gradedPiece p).d (p + q) (p + (q + 1))) ∧
      (∀ (p q t : ℤ) (ht : 1 ≤ t),
        ∃ hBZ : L.complexBoundaries p (p + q) t ≤ L.complexCycles p (p + q) t,
          Nonempty ((E.page t (le_trans (by decide : (0 : ℤ) ≤ 1) ht)).X (p, q) ≅
            cokernel (Subobject.ofLE _ _ hBZ))) ∧
      (∀ (r : ℕ) (s : ℤ),
        (E.page 1).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (e₁ r (s + 1)).hom =
          (e₁ r s).hom ≫ (F.rightDerived r).map (K.obj.d s (s + 1))) ∧
      (∀ p q : ℤ, q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      (∀ (Y : ℤ → B)
        (c : ∀ n : ℤ,
          ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
            (ComplexShape.up ℤ)).homology n ≅ Y n),
        ∃ H : ∀ n : ℤ, DecreasingFiltration (Y n),
          (∀ n : ℤ, (H n).IsFinite) ∧
          (∀ p n : ℤ, (H n).step p =
            (Subobject.«exists» (c n).hom).obj
              (imageSubobject (HomologicalComplex.homologyMap (L.step p).arrow n))) ∧
          (∀ p n : ℤ, ∃ (t : ℤ) (ht : 1 ≤ t), ∀ (r : ℤ) (hr : t ≤ r),
            Nonempty ((E.page r (le_trans (by decide : (0 : ℤ) ≤ 1)
              (le_trans ht hr))).X (p, n - p) ≅ (H n).gradedPiece p))) := by
  classical
  obtain ⟨b, hb⟩ := hbelow
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj I).flip
  have hzero : ∀ i j : ℤ, i < 0 ∨ j < b → IsZero ((J.X i).X j) := by
    intro i j hij
    rcases hij with hi | hj
    · change IsZero
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X j)).extend
          ComplexShape.embeddingUpNat |>.X i)
      exact HomologicalComplex.isZero_extend_X _ _ i (by
        intro r
        change (r : ℤ) ≠ i
        omega)
    · change IsZero
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X j)).extend
          ComplexShape.embeddingUpNat |>.X i)
      exact (HomologicalComplex.eval B (ComplexShape.up ℤ) i).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor B).map_isZero
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero (hb j hj)))
  obtain ⟨L, hL, htop, hbot⟩ := J.boundedBelow_secondFiltration b hzero
  obtain ⟨E, e₀, e₁, hd₀, hpages, hd₁, hneg⟩ :=
    cartanEilenberg_row_pages F K I a ⟨b, hb⟩ hterms hrows L hL
  refine ⟨L, E, e₀, e₁, hL, hd₀, hpages, hd₁, hneg, ?_⟩
  intro Y c
  have hfinite : ∀ n : ℤ, ∃ lo hi : ℤ,
      L.complexStep lo n = ⊤ ∧ L.complexStep hi n = ⊥ :=
    fun n ↦ ⟨b, n + 1, htop n, hbot n⟩
  obtain ⟨H, hfin, hstep, hstable⟩ :=
    degreewiseFiltered_stable_quotient (J.total (ComplexShape.up ℤ)) L hfinite Y c
  refine ⟨H, hfin, hstep, ?_⟩
  intro p n
  obtain ⟨t, ht, htail⟩ := hstable p n
  refine ⟨t, ht, ?_⟩
  intro r hr
  have hpage : ∃ hBZ : L.complexBoundaries p n r ≤ L.complexCycles p n r,
      Nonempty
        ((E.page r (le_trans (by decide : (0 : ℤ) ≤ 1) (le_trans ht hr))).X (p, n - p) ≅
          cokernel (Subobject.ofLE _ _ hBZ)) := by
    have h := hpages p (n - p) r (le_trans ht hr)
    rw [show p + (n - p) = n by omega] at h
    exact h
  obtain ⟨hBZ, he⟩ := hpage
  obtain ⟨hBZ', hf⟩ := htail r hr
  exact ⟨he.some ≪≫ hf.some⟩

end CategoryTheory.Functor
