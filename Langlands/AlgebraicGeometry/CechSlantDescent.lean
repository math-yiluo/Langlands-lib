import Langlands.AlgebraicGeometry.CechSlant
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-! # Descent of shuffle slant maps to all-sequence Čech cohomology -/

noncomputable section

universe v w u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.Cohomology.Cech.KunnethDetection

section Descent

variable {C : Type*} [Category* C] [Preadditive C]
  (K Q : CochainComplex C ℕ)
  (s : ∀ n, K.X (n + 1) ⟶ Q.X n)
  (hs : ∀ n, K.d (n + 1) (n + 2) ≫ s (n + 1) = -(s n ≫ Q.d n (n + 1)))
  (hs₀ : K.d 0 1 ≫ s 0 = 0)

set_option backward.isDefEq.respectTransparency false in
/-- The degree-lowering map on the short complexes computing homology. -/
def slantShortComplexMap (n : ℕ) : K.sc (n + 1) ⟶ Q.sc n := by
  cases n with
  | zero =>
    refine (K.isoSc' 0 1 2 (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1)).hom ≫
      ?_ ≫ (Q.isoSc' 0 0 1 CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0)).inv
    exact
      { τ₁ := 0
        τ₂ := s 0
        τ₃ := -s 1
        comm₁₂ := by
          change (0 : K.X 0 ⟶ Q.X 0) ≫ Q.d 0 0 = K.d 0 1 ≫ s 0
          simpa only [zero_comp] using hs₀.symm
        comm₂₃ := by
          change s 0 ≫ Q.d 0 1 = K.d 1 2 ≫ (-s 1)
          rw [Preadditive.comp_neg, hs 0, neg_neg] }
  | succ n =>
    refine (K.isoSc' (n + 1) (n + 2) (n + 3) (CochainComplex.prev_nat_succ (n + 1))
      (CochainComplex.next ℕ (n + 2))).hom ≫ ?_ ≫
      (Q.isoSc' n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
        (CochainComplex.next ℕ (n + 1))).inv
    exact
      { τ₁ := -s n
        τ₂ := s (n + 1)
        τ₃ := -s (n + 2)
        comm₁₂ := by
          change (-s n) ≫ Q.d n (n + 1) = K.d (n + 1) (n + 2) ≫ s (n + 1)
          simpa only [Preadditive.neg_comp] using (hs n).symm
        comm₂₃ := by
          change s (n + 1) ≫ Q.d (n + 1) (n + 2) =
            K.d (n + 2) (n + 3) ≫ (-s (n + 2))
          rw [Preadditive.comp_neg, hs (n + 1), neg_neg] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma slantShortComplexMap_τ₂ (n : ℕ) : (slantShortComplexMap K Q s hs hs₀ n).τ₂ = s n := by
  cases n with
  | zero =>
    change 𝟙 (K.X 1) ≫ s 0 ≫ 𝟙 (Q.X 0) = s 0
    simp
  | succ n =>
    change 𝟙 (K.X (n + 2)) ≫ s (n + 1) ≫ 𝟙 (Q.X (n + 1)) = s (n + 1)
    simp

/-- Descent of an anticommuting map of degree minus one to homology. -/
def slantHomologyMap (n : ℕ) [K.HasHomology (n + 1)] [Q.HasHomology n] :
    K.homology (n + 1) ⟶ Q.homology n :=
  ShortComplex.homologyMap (slantShortComplexMap K Q s hs hs₀ n)

set_option backward.isDefEq.respectTransparency false in
lemma slantCyclesMap_i (n : ℕ) [K.HasHomology (n + 1)] [Q.HasHomology n] :
    ShortComplex.cyclesMap (slantShortComplexMap K Q s hs hs₀ n) ≫ Q.iCycles n =
      K.iCycles (n + 1) ≫ s n := by
  change ShortComplex.cyclesMap (slantShortComplexMap K Q s hs hs₀ n) ≫
    (Q.sc n).iCycles = (K.sc (n + 1)).iCycles ≫ s n
  simpa only [slantShortComplexMap_τ₂] using
    ShortComplex.cyclesMap_i (slantShortComplexMap K Q s hs hs₀ n)

lemma slantHomologyMap_homologyπ (n : ℕ) [K.HasHomology (n + 1)] [Q.HasHomology n] :
    K.homologyπ (n + 1) ≫ slantHomologyMap K Q s hs hs₀ n =
      ShortComplex.cyclesMap (slantShortComplexMap K Q s hs hs₀ n) ≫ Q.homologyπ n :=
  ShortComplex.homologyπ_naturality _

end Descent

section Cech

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}}
  {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R} {πP : P ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  [∀ W : P.Opens, Algebra R Γ(P, W)]
  (halgP : ∀ W : P.Opens, algebraMap R Γ(P, W) = (secHom πP W).hom)
  (hπ : p₁ ≫ πX = πP)
  {ι : Type w} [Finite ι] {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)
  (hl : ∀ y : C (ab X.presheaf) U 0, l (d (ab X.presheaf) U 0 y) = 0)

/-- The shuffle slant maps viewed in the category of abelian groups. -/
def LAddHom (n : ℕ) :
    (complex (ab P.presheaf) (prodCover p₁ p₂ U V)).X (n + 1) ⟶
      (complex (ab Y.presheaf) V).X n :=
  AddCommGrpCat.ofHom (LLinearMap hP halgX halgY halgP hπ U hU l V hV n).toAddMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- The shuffle slant operator on the homology of the all-sequence Čech complex. -/
def LHomologyMap (n : ℕ) :
    (complex (ab P.presheaf) (prodCover p₁ p₂ U V)).homology (n + 1) ⟶
      (complex (ab Y.presheaf) V).homology n :=
  slantHomologyMap _ _ (LAddHom hP halgX halgY halgP hπ U V hU hV l)
    (fun n => by
      change (complex (ab P.presheaf) (prodCover p₁ p₂ U V)).d (n + 1) ((n + 1) + 1) ≫
        LAddHom hP halgX halgY halgP hπ U V hU hV l (n + 1) =
          -(LAddHom hP halgX halgY halgP hπ U V hU hV l n ≫
            (complex (ab Y.presheaf) V).d n (n + 1))
      dsimp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      ext c
      exact L_d hP halgX halgY U V hU hV l hl n c)
    (by
      ext c
      exact L_zero_d hP halgX halgY U V hU hV l hl c) n

end Cech

end Langlands.Cohomology.Cech.KunnethDetection
