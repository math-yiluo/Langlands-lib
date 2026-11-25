/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Algebra.Homology.FiniteStripConeGradedMapIsIso
import WeilConjectures.Algebra.Homology.FiniteStripConeGradedMapDifferential

/-! # Three-term comparison for the finite-strip cone filtration

Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), second-variable
variant, refined by the explicit diagonal quotient argument of
lem-sc-finite-strip-cone-filtration, step 3.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

/-- The three-term short complexes of the graded cone and translated row cone agree.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), second-variable variant;
explicit cone refinement in lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-filtration-graded-point)

Proof: Evaluation of cochain complexes preserves cokernels, so evaluate the
cokernel defining the graded piece degreewise. In degree m, quotient the vertical
tail p by the tail p+1. The diagonal
coproduct leaves only K^(m-p,p), together with A.X p when m=p-1. The diagonal
projections induce inverse maps on the quotient: all other summands factor
through the next tail and vanish. To check the inverse on the quotient, cancel
its epic cokernel projection and check on the source and supported diagonal
inclusions generating the step. The p diagonal gives the identity; every larger
vertical index factors through step p+1 and gives zero. The vertical differential
increases its vertical index and therefore vanishes in the quotient. The
horizontal total sign is one. The negative source differential also increases
the vertical index and vanishes; the surviving augmentation block is a p.
The single-complex identifications and hf
identify these blocks with the row cone. Apply these degreewise isomorphisms
at m=n-1,n,n+1. The component differential formulas give the two commuting
squares, hence an isomorphism of short complexes. Zero summands outside the
strip and the single complex are handled by their unique maps, including r=0.
-/
theorem finite_strip_cone_filtration_graded_point
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) : Nonempty ((F.gradedPiece p).sc n ≅
      (CochainComplex.mappingCone (f p)).sc (n - p)) := by
  let g := fun m ↦ finiteStripGradedMap K r hsupport A b f F hsteps p m
  have hg (m : ℤ) : IsIso (g m) :=
    finiteStripGradedMap_isIso K r hsupport A b f F hsteps p m
  have := hg (n - 1)
  have := hg n
  have := hg (n + 1)
  let S : ShortComplex C :=
    (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
      (n - 1 - p) (n - p) (n + 1 - p)).obj (CochainComplex.mappingCone (f p))
  let T : ShortComplex C :=
    (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
      (n - 1) n (n + 1)).obj (F.gradedPiece p)
  have h₁₂ :=
    finiteStripGradedMap_differential K r hsupport A a b hb f hf F hsteps p (n - 1)
  have h₂₃ := finiteStripGradedMap_differential K r hsupport A a b hb f hf F hsteps p n
  have hn : n - 1 + 1 = n := by omega
  rw [hn] at h₁₂
  have e : S ≅ T := ShortComplex.isoMk (asIso (g (n - 1))) (asIso (g n))
    (asIso (g (n + 1))) (by simpa [g, S, T, HomologicalComplex.shortComplexFunctor'] using h₁₂)
    (by simpa [g, S, T, HomologicalComplex.shortComplexFunctor'] using h₂₃)
  simpa [S, T, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    sub_right_comm, sub_add_eq_add_sub] using (show Nonempty (T ≅ S) from ⟨e.symm⟩)

end HomologicalComplex₂
