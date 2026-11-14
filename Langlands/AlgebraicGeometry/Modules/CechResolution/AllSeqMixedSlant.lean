import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqSlantDual
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Shuffle slant of mixed degree-two products -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w w' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.Cohomology.Cech.KunnethDetection

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] {κ : Type w'} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

/-- The full slant formula for a product of axis sums, without normalization of the dual. -/
lemma L_prod_sum (n : ℕ) (z : Fin (n + 2) → C (ab X.presheaf) U 1)
    (y : Fin (n + 2) → C (ab Y.presheaf) V 1) (hz : ∀ k, d (ab X.presheaf) U 1 (z k) = 0)
    (hy : ∀ k, d (ab Y.presheaf) V 1 (y k) = 0) :
    L hP halgX halgY U V hU hV l (n + 1) (prod P.presheaf (prodCover p₁ p₂ U V) (n + 2)
        (fun k => pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 (z k) +
          pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 (y k))) =
      fun b => ∑ s : Fin (n + 2), (-1 : ℤ) ^ (s : ℕ) •
        (HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l (z s))
          (prod Y.presheaf V (n + 1) (y ∘ s.succAbove) b)) := by
  funext b
  rw [L_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  exact (DFunLike.congr_arg _ (funext fun σ => res_prod_path U V z y hz hy s σ b)).trans
    (slant_mul hP halgX halgY U hU l (inter V b) (hV (n + 1) b) (z s) _)

/-- Slant of a degree-two cup of axis sums. -/
lemma L_cup_pull_add
    (z₀ z₁ : C (ab X.presheaf) U 1) (y₀ y₁ : C (ab Y.presheaf) V 1)
    (hz₀ : d (ab X.presheaf) U 1 z₀ = 0) (hz₁ : d (ab X.presheaf) U 1 z₁ = 0)
    (hy₀ : d (ab Y.presheaf) V 1 y₀ = 0) (hy₁ : d (ab Y.presheaf) V 1 y₁ = 0) :
    L hP halgX halgY U V hU hV l 1
      (cup₁ P.presheaf (prodCover p₁ p₂ U V)
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z₀ +
          pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y₀)
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z₁ +
          pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y₁)) =
      fun b => HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l z₀) (y₁ b) -
        HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l z₁) (y₀ b) := by
  have h := L_prod_sum hP halgX halgY U V hU hV l 0 ![z₀, z₁] ![y₀, y₁]
    (by intro k; fin_cases k <;> assumption) (by intro k; fin_cases k <;> assumption)
  rw [prod_succ, prod_one] at h
  simpa [Fin.sum_univ_two, prod_one, Fin.tail, sub_eq_add_neg] using h

/-- Slant evaluates a mixed cup by the first-factor functional. -/
lemma L_cup_pull_left_right
    (z : C (ab X.presheaf) U 1) (y : C (ab Y.presheaf) V 1)
    (hz : d (ab X.presheaf) U 1 z = 0) (hy : d (ab Y.presheaf) V 1 y = 0) :
    L hP halgX halgY U V hU hV l 1
      (cup₁ P.presheaf (prodCover p₁ p₂ U V)
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z)
        (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y)) =
      fun b => HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l z) (y b) := by
  have h := L_cup_pull_add hP halgX halgY U V hU hV l z 0 0 y hz
    (map_zero _) (map_zero _) hy
  simpa only [map_zero, add_zero, zero_add, zero_smul, sub_zero] using h

/-- Slant kills a cup with both factors on the first axis. -/
lemma L_cup_pull_left_left
    (z z' : C (ab X.presheaf) U 1)
    (hz : d (ab X.presheaf) U 1 z = 0) (hz' : d (ab X.presheaf) U 1 z' = 0) :
    L hP halgX halgY U V hU hV l 1
      (cup₁ P.presheaf (prodCover p₁ p₂ U V)
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z)
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z')) = 0 := by
  have h := L_cup_pull_add hP halgX halgY U V hU hV l z z' 0 0 hz hz'
    (map_zero _) (map_zero _)
  simp only [map_zero, add_zero] at h
  refine h.trans ?_
  funext b
  change HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l z) 0 -
    HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l z') 0 = 0
  simp only [smul_zero, sub_zero]

/-- Slant kills a cup with both factors on the second axis. -/
lemma L_cup_pull_right_right
    (y y' : C (ab Y.presheaf) V 1)
    (hy : d (ab Y.presheaf) V 1 y = 0) (hy' : d (ab Y.presheaf) V 1 y' = 0) :
    L hP halgX halgY U V hU hV l 1
      (cup₁ P.presheaf (prodCover p₁ p₂ U V)
        (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y)
        (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y')) = 0 := by
  have h := L_cup_pull_add hP halgX halgY U V hU hV l 0 0 y y'
    (map_zero _) (map_zero _) hy hy'
  simp only [map_zero, zero_add, zero_smul, sub_zero] at h
  refine h.trans ?_
  funext b
  rfl

end Langlands.Cohomology.Cech.KunnethDetection


namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech Cech.KunnethDetection DerivedSections
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open scoped TensorProduct

/-- Canonical pullback on actual structure-sheaf cohomology, with the unit comparison. -/
abbrev unitCohomologyPullbackLinear {R : CommRingCat.{u}} {X Y : Over (Spec R)}
    (f : Y ⟶ X) (n : ℕ) :
    (relativeCohomology X.hom n).obj (unitModule X.left) →ₗ[R]
      (relativeCohomology Y.hom n).obj (unitModule Y.left) :=
  (relativeCohomologyPullback f (unitModule X.left) n ≫
    (relativeCohomology Y.hom n).map (Langlands.Scheme.Modules.pullbackUnitIso f.left).hom).hom

variable {K : Type u} [Field K] {X Y P : Over (Spec (CommRingCat.of K))}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
  (hP : IsPullback p₁.left p₂.left X.hom Y.hom)
  [IsSeparated X.hom] [IsSeparated Y.hom] [IsSeparated P.hom]
  [∀ W : X.left.Opens, Algebra (CommRingCat.of K) Γ(X.left, W)]
  (halgX : ∀ W : X.left.Opens,
    algebraMap (CommRingCat.of K) Γ(X.left, W) = (secHom X.hom W).hom)
  [∀ W : Y.left.Opens, Algebra (CommRingCat.of K) Γ(Y.left, W)]
  (halgY : ∀ W : Y.left.Opens,
    algebraMap (CommRingCat.of K) Γ(Y.left, W) = (secHom Y.hom W).hom)
  [∀ W : P.left.Opens, Algebra (CommRingCat.of K) Γ(P.left, W)]
  (halgP : ∀ W : P.left.Opens,
    algebraMap (CommRingCat.of K) Γ(P.left, W) = (secHom P.hom W).hom)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (hUtop : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (hVtop : ⨆ j, V j = ⊤) (hVa : ∀ j, IsAffineOpen (V j))
  (hUVtop : ⨆ j, prodCover p₁.left p₂.left U V j = ⊤)
  (hUVa : ∀ j, IsAffineOpen (prodCover p₁.left p₂.left U V j))

/-- The mixed cup on actual first cohomology of the two factors. -/
def mixedCup :
    (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K]
      (relativeCohomology Y.hom 1).obj (unitModule Y.left) →ₗ[K]
        (relativeCohomology P.hom 2).obj (unitModule P.left) :=
  (cupCanonical P.hom (prodCover p₁.left p₂.left U V) hUVtop hUVa).compl₁₂
    (unitCohomologyPullbackLinear p₁ 1) (unitCohomologyPullbackLinear p₂ 1)

omit [IsSeparated X.hom] [IsSeparated Y.hom]
  [∀ W : X.left.Opens, Algebra (CommRingCat.of K) Γ(X.left, W)]
  [∀ W : Y.left.Opens, Algebra (CommRingCat.of K) Γ(Y.left, W)]
  [∀ W : P.left.Opens, Algebra (CommRingCat.of K) Γ(P.left, W)] in
lemma mixedCup_apply (x y) :
    mixedCup p₁ p₂ U V hUVtop hUVa x y =
      cupCanonical P.hom (prodCover p₁.left p₂.left U V) hUVtop hUVa
        (unitCohomologyPullbackLinear p₁ 1 x) (unitCohomologyPullbackLinear p₂ 1 y) := rfl

/-- The mixed tensor-to-cohomology map induced by the actual two-axis cup. -/
def mixedTensor :
    (relativeCohomology X.hom 1).obj (unitModule X.left) ⊗[K]
      (relativeCohomology Y.hom 1).obj (unitModule Y.left) →ₗ[K]
        (relativeCohomology P.hom 2).obj (unitModule P.left) :=
  TensorProduct.lift (mixedCup p₁ p₂ U V hUVtop hUVa)

omit [IsSeparated X.hom] [IsSeparated Y.hom]
  [∀ W : X.left.Opens, Algebra (CommRingCat.of K) Γ(X.left, W)]
  [∀ W : Y.left.Opens, Algebra (CommRingCat.of K) Γ(Y.left, W)]
  [∀ W : P.left.Opens, Algebra (CommRingCat.of K) Γ(P.left, W)] in
lemma mixedTensor_tmul (x y) :
    mixedTensor p₁ p₂ U V hUVtop hUVa (x ⊗ₜ[K] y) =
      mixedCup p₁ p₂ U V hUVtop hUVa x y := rfl

/-- Slant by any actual H1 dual evaluates the first factor of a mixed cup. -/
lemma slantByH1Dual_mixedCup
    (ell : (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K] K)
    (x : (relativeCohomology X.hom 1).obj (unitModule X.left))
    (y : (relativeCohomology Y.hom 1).obj (unitModule Y.left)) :
    slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa hUVtop hUVa ell 1
        (mixedCup p₁ p₂ U V hUVtop hUVa x y) = ell x • y := by
  obtain ⟨z, rfl⟩ := canonicalClass_surjective X.hom U hUtop hUa 0 x
  obtain ⟨w, rfl⟩ := canonicalClass_surjective Y.hom V hVtop hVa 0 y
  rw [mixedCup_apply]
  dsimp only [unitCohomologyPullbackLinear]
  rw [pull_canonicalClass p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
      (fun _ => inf_le_left) hUtop hUVtop hUa hUVa,
    pull_canonicalClass p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
      (fun _ => inf_le_right) hVtop hUVtop hVa hUVa,
    cupCanonical_canonicalClass]
  unfold slantByH1Dual
  rw [slantCanonical_canonicalClass, ← map_smul]
  apply congrArg (canonicalClass Y.hom V hVtop hVa 0)
  apply Subtype.ext
  apply (cochainSecEquiv Y.hom V halgY 1).injective
  simp only [Submodule.coe_smul]
  rw [map_smul]
  change L hP halgX halgY U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 1
      (cup₁ P.left.presheaf (prodCover p₁.left p₂.left U V)
        ((unitCochainMap p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
          (fun _ => inf_le_left)).f 1 z.1)
        ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
          (fun _ => inf_le_right)).f 1 w.1)) = _
  rw [unitCochainMap_eq_pull, unitCochainMap_eq_pull]
  have hz : Cech.d (ab X.left.presheaf) U 1 (z.1 : C (ab X.left.presheaf) U 1) = 0 := by
    rw [← dCochain_unit X.hom U 1 z.1]
    exact z.2
  have hw : Cech.d (ab Y.left.presheaf) V 1 (w.1 : C (ab Y.left.presheaf) V 1) = 0 := by
    rw [← dCochain_unit Y.hom V 1 w.1]
    exact w.2
  rw [L_cup_pull_left_right hP halgX halgY U V hU hV _ _ _ hz hw]
  have hdual := h1DualCochainFunctional_cocycle X.hom U hUtop hUa halgX ell z
  change h1DualCochainFunctional X.hom U hUtop hUa halgX ell
    (z.1 : C (ab X.left.presheaf) U 1) = _ at hdual
  rw [hdual]
  funext b
  rfl

/-- On an arbitrary mixed tensor, slant is contraction of its first factor. -/
lemma slantByH1Dual_mixedTensor
    (ell : (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K] K)
    (t : (relativeCohomology X.hom 1).obj (unitModule X.left) ⊗[K]
      (relativeCohomology Y.hom 1).obj (unitModule Y.left)) :
    slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa hUVtop hUVa ell 1
        (mixedTensor p₁ p₂ U V hUVtop hUVa t) =
      TensorProduct.lid K _ (ell.rTensor _ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [mixedTensor_tmul, slantByH1Dual_mixedCup p₁ p₂ hP halgX halgY halgP U V
      hUtop hUa hU hV hVtop hVa hUVtop hUVa, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

include hP halgX halgY halgP hUtop hUa hU hV hVtop hVa in
/-- The actual mixed tensor-to-cohomology map is injective over every field. -/
theorem mixedTensor_injective :
    Function.Injective (mixedTensor p₁ p₂ U V hUVtop hUVa) := by
  intro s t h
  let b := Module.Free.chooseBasis K ((relativeCohomology X.hom 1).obj (unitModule X.left))
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply,
    TensorProduct.equivFinsuppOfBasisLeft_apply,
    ← slantByH1Dual_mixedTensor p₁ p₂ hP halgX halgY halgP U V hUtop hUa hU hV
      hVtop hVa hUVtop hUVa (b.coord i) s,
    ← slantByH1Dual_mixedTensor p₁ p₂ hP halgX halgY halgP U V hUtop hUa hU hV
      hVtop hVa hUVtop hUVa (b.coord i) t, h]

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
