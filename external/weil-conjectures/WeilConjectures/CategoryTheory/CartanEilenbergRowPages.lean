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
import WeilConjectures.CategoryTheory.SecondFiltrationRowCohomology

/-! # Signed row identifications for the second-filtration spectral sequence

Source: Stacks Project, Tag 0130; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-cartan-eilenberg-row-pages).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The second-filtration pages, with the signed injective-resolution comparison.
This statement asserts no convergence or derived interpretation of total cohomology.
Source: Stacks Project, Tag 0130; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-cartan-eilenberg-row-pages).

Proof.
Construct the spectral sequence of L by the filtered-complex construction, retaining
its connecting-map description of d₁ as well as its page-zero and cycle/boundary
identifications. The second-degree graded complex at s is the F-image of I.X s,
extended by zero and placed in total degrees s+r. Its differential is the row
differential. A row augmentation a.f s is a quasi-isomorphism and all its terms
are injective, so it is an injective resolution of K^s. The canonical comparison
with the ordinary right derived functor identifies row cohomology in degree r with
R^r F(K^s); naturality applies to the square a.comm s (s+1).
For d₁ lift a row cocycle to the quotient L^s/L^(s+2). Its differential has only
the component raising complex degree, with sign (-1)^r, so the connecting map
is (-1)^r times the map of row cohomology. Multiply the comparison at (s,r)
by (-1)^(r*s). This is an automorphism, and the consecutive multipliers differ
by (-1)^r, cancelling the sign. This gives the unsigned naturality equation
for every integer s, including negative s. Extension by zero makes the graded
complex vanish below total degree s; therefore row cohomology, and hence E₁,
vanishes in negative complementary degree. -/
theorem cartanEilenberg_row_pages
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hterms : ∀ (s : ℤ) (r : ℕ), Injective ((I.X s).X r))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p) :
    ∃ (E : CohomologicalSpectralSequence B 0)
      (e₀ : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (L.gradedPiece p).X (p + q))
      (e₁ : ∀ (r : ℕ) (s : ℤ), (E.page 1).X (s, (r : ℤ)) ≅
        (F.rightDerived r).obj (K.obj.X s)),
      (∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e₀ p (q + 1)).hom =
        (e₀ p q).hom ≫ (L.gradedPiece p).d (p + q) (p + (q + 1))) ∧
      (∀ (p q t : ℤ) (ht : 1 ≤ t),
        ∃ hBZ : L.complexBoundaries p (p + q) t ≤ L.complexCycles p (p + q) t,
          Nonempty ((E.page t (le_trans (by decide : (0 : ℤ) ≤ 1) ht)).X (p, q) ≅
            cokernel (Subobject.ofLE _ _ hBZ))) ∧
      (∀ (r : ℕ) (s : ℤ),
        (E.page 1).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (e₁ r (s + 1)).hom =
          (e₁ r s).hom ≫ (F.rightDerived r).map (K.obj.d s (s + 1))) ∧
      (∀ p q : ℤ, q < 0 → IsZero ((E.page 1).X (p, q))) := by
  classical
  let R : ∀ s : ℤ, InjectiveResolution (K.obj.X s) := fun s ↦
    { cocomplex := I.X s
      injective := hterms s
      ι := a.f s
      quasiIso := hrows s }
  obtain ⟨E, e₀, eRow, hd₀, hpages, hdRow, hneg⟩ :=
    secondFiltration_row_cohomology F I hbelow L hL
  let eSigned : ∀ (r : ℕ) (s : ℤ), (E.page 1).X (s, (r : ℤ)) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).homology r :=
    fun r s ↦ ((r : ℤ) * s).negOnePow • eRow r s
  have hdSigned : ∀ (r : ℕ) (s : ℤ),
      (E.page 1).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (eSigned r (s + 1)).hom =
        (eSigned r s).hom ≫ HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))) r := by
    intro r s
    dsimp only [eSigned, Preadditive.smul_iso_hom]
    rw [Linear.comp_units_smul, hdRow r s, Linear.units_smul_comp, smul_smul,
      show (r : ℤ) * (s + 1) = (r : ℤ) * s + (r : ℤ) by rw [mul_add, mul_one],
      Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
  let e₁ : ∀ (r : ℕ) (s : ℤ), (E.page 1).X (s, (r : ℤ)) ≅
      (F.rightDerived r).obj (K.obj.X s) :=
    fun r s ↦ eSigned r s ≪≫ ((R s).isoRightDerivedObj F r).symm
  refine ⟨E, e₀, e₁, hd₀, hpages, ?_, hneg⟩
  intro r s
  have ha : (R s).ι.f 0 ≫ (I.d s (s + 1)).f 0 =
      K.obj.d s (s + 1) ≫ (R (s + 1)).ι.f 0 := by
    have h := congrArg (fun f ↦ f.f 0) (a.comm s (s + 1))
    simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.single₀_map_f_zero] using h
  have hnat := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (K.obj.d s (s + 1)) (R s) (R (s + 1)) (I.d s (s + 1)) ha F r
  change ((R s).isoRightDerivedObj F r).inv ≫
      (F.rightDerived r).map (K.obj.d s (s + 1)) =
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))) r ≫
        ((R (s + 1)).isoRightDerivedObj F r).inv at hnat
  dsimp only [e₁, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hdSigned r s, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ (eSigned r s).hom ≫ f) hnat.symm

end CategoryTheory.Functor
