/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.FinitePresentation

/-!
# Finite-stage models of finitely presented algebras over a filtered colimit

Let `A = colim Aⱼ` be a filtered colimit of commutative rings and let
`B = A[x_σ] ⧸ (r_l)_{l ∈ ι}` be a finitely presented `A`-algebra. The finitely many coefficients
of the relations `r_l` lift to a common stage `λ_B`, giving lifted relations `r_{l,λ_B}` and the
finite-stage model `B_{λ_B} = A_{λ_B}[x_σ] ⧸ (r_{l,λ_B})`, which is finitely presented over
`A_{λ_B}`; its base change `A ⊗_{A_{λ_B}} B_{λ_B}` is canonically isomorphic to `B`.

## Main definitions and results

- `MvPolynomial.quotientSpanTensorAlgEquiv`: for an `R`-algebra `A`, the base change of
  `R[x_σ] ⧸ (r_l)` to `A` is `A[x_σ] ⧸ (r_l)`.
- `CommRingCat.fpDescentStage`, `CommRingCat.fpDescentRelations`: the selected stage `λ_B` and
  the lifted relations.
- `CommRingCat.FPDescent`: the finite-stage model `B_{λ_B}`.
- `CommRingCat.fpDescentEquiv`: the comparison isomorphism `A ⊗_{A_{λ_B}} B_{λ_B} ≃ B`.
-/

@[expose] public section

universe vJ uJ u

open CategoryTheory Limits TensorProduct

namespace MvPolynomial

variable {R : Type*} (A : Type*) [CommRing R] [CommRing A] [Algebra R A] {σ ι : Type*}
  (r : ι → MvPolynomial σ R)

lemma map_span_range_includeRight :
    Ideal.span (Set.range fun l ↦ map (algebraMap R A) (r l)) =
      ((Ideal.span (Set.range r)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := A))).map
        ((algebraTensorAlgEquiv (σ := σ) R A : A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A) :
          A ⊗[R] MvPolynomial σ R →+* MvPolynomial σ A) := by
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 2
  funext l
  simp

/-- The base change of a quotient `R[x_σ] ⧸ (r_l)` of a polynomial ring along `R → A` is the
quotient `A[x_σ] ⧸ (r_l)` by the images of the relations. -/
noncomputable def quotientSpanTensorAlgEquiv :
    A ⊗[R] (MvPolynomial σ R ⧸ Ideal.span (Set.range r)) ≃ₐ[A]
      MvPolynomial σ A ⧸ Ideal.span (Set.range fun l ↦ map (algebraMap R A) (r l)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv A (MvPolynomial σ R) A _).trans
    (Ideal.quotientEquivAlg _ _ (algebraTensorAlgEquiv R A) (map_span_range_includeRight A r))

@[simp]
lemma quotientSpanTensorAlgEquiv_tmul (a : A) (p : MvPolynomial σ R) :
    quotientSpanTensorAlgEquiv A r (a ⊗ₜ Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (a • map (algebraMap R A) p) := by
  simp [quotientSpanTensorAlgEquiv]

end MvPolynomial

namespace CommRingCat

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
  {c : Cocone F} [PreservesColimit F (forget CommRingCat)] (hc : IsColimit c) {σ ι : Type*}
  [Finite ι] (r : ι → MvPolynomial σ c.pt)

include hc in
/-- Finitely many polynomials over a filtered colimit of rings lift to a common stage. -/
lemma exists_lift_relations :
    ∃ (j : J) (r' : ι → MvPolynomial σ (F.obj j)),
      ∀ l, MvPolynomial.map (c.ι.app j).hom (r' l) = r l := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ := exists_forall_mem_range_map_ι_app F c hc (Finset.univ.image r)
  choose r' hr' using fun l ↦ hj (r l) (Finset.mem_image_of_mem r (Finset.mem_univ l))
  exact ⟨j, r', hr'⟩

/-- The selected stage `λ_B` to which the coefficients of the relations `r` of
`B = c.pt[x_σ] ⧸ (r_l)` lift. -/
noncomputable def fpDescentStage : J := (exists_lift_relations hc r).choose

/-- The lifted relations `r_{l,λ_B}` over the selected stage `λ_B = fpDescentStage hc r`. -/
noncomputable def fpDescentRelations : ι → MvPolynomial σ (F.obj (fpDescentStage hc r)) :=
  (exists_lift_relations hc r).choose_spec.choose

@[simp]
lemma map_fpDescentRelations (l : ι) :
    MvPolynomial.map (c.ι.app (fpDescentStage hc r)).hom (fpDescentRelations hc r l) = r l :=
  (exists_lift_relations hc r).choose_spec.choose_spec l

/-- Finite-stage model of a finitely presented affine algebra: for
`B = c.pt[x_σ] ⧸ (r_l)_{l ∈ ι}` over the colimit `c.pt` of a filtered diagram of rings, this is
`B_{λ_B} = A_{λ_B}[x_σ] ⧸ (r_{l,λ_B})`, where `λ_B = fpDescentStage hc r` is the selected stage
and `r_{l,λ_B} = fpDescentRelations hc r l` are the lifted relations. -/
abbrev FPDescent :=
  MvPolynomial σ (F.obj (fpDescentStage hc r)) ⧸ Ideal.span (Set.range (fpDescentRelations hc r))

/-- The finite-stage model `B_{λ_B}` is finitely presented over `A_{λ_B}`. -/
instance finitePresentation_fpDescent [Finite σ] :
    Algebra.FinitePresentation (F.obj (fpDescentStage hc r)) (FPDescent hc r) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

/-- The comparison isomorphism `β_B : A ⊗_{A_{λ_B}} B_{λ_B} ≃ B`, where `A_{λ_B} → A` is the
colimit map `c.ι.app λ_B`. -/
noncomputable def fpDescentEquiv :
    letI : Algebra (F.obj (fpDescentStage hc r)) c.pt :=
      (c.ι.app (fpDescentStage hc r)).hom.toAlgebra
    c.pt ⊗[F.obj (fpDescentStage hc r)] FPDescent hc r ≃ₐ[c.pt]
      MvPolynomial σ c.pt ⧸ Ideal.span (Set.range r) :=
  letI : Algebra (F.obj (fpDescentStage hc r)) c.pt :=
    (c.ι.app (fpDescentStage hc r)).hom.toAlgebra
  (MvPolynomial.quotientSpanTensorAlgEquiv c.pt (fpDescentRelations hc r)).trans
    (Ideal.quotientEquivAlgOfEq c.pt (by
      congr 2
      funext l
      exact map_fpDescentRelations hc r l))

lemma fpDescentEquiv_tmul (a : c.pt) (p : MvPolynomial σ (F.obj (fpDescentStage hc r))) :
    letI : Algebra (F.obj (fpDescentStage hc r)) c.pt :=
      (c.ι.app (fpDescentStage hc r)).hom.toAlgebra
    fpDescentEquiv hc r (a ⊗ₜ Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _
        (a • MvPolynomial.map (algebraMap (F.obj (fpDescentStage hc r)) c.pt) p) := by
  simp [fpDescentEquiv]

end CommRingCat
