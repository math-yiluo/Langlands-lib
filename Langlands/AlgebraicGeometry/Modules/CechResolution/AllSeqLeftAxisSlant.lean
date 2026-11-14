import Langlands.AlgebraicGeometry.CechSlantLeftCup
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqMixedSlant
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCreation
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityProof

/-! # Slant of a left-axis creation on actual cohomology -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech Cech.KunnethDetection DerivedSections
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

section Canonical

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) [IsSeparated π]
  {ι : Type u} [Fintype ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hUa : ∀ i, IsAffineOpen (U i))

/-- Two cocycles differing by a coboundary have the same actual cohomology class. -/
lemma canonicalClass_eq_of_sub_eq_dCochain (n : ℕ)
    (a b : LinearMap.ker (dCochain π U (unitModule X) (n + 1)))
    (y : cochain π U (unitModule X) n)
    (h : (a : cochain π U (unitModule X) (n + 1)) - b = dCochain π U (unitModule X) n y) :
    canonicalClass π U hU hUa n a = canonicalClass π U hU hUa n b := by
  rw [← sub_eq_zero, ← map_sub]
  have hz : classMap π U (unitModule X) n (a - b) = 0 :=
    (classMap_eq_zero_iff π U (unitModule X) n (a - b)).2 ⟨y, h.symm⟩
  simp only [canonicalClass, LinearMap.comp_apply, hz, map_zero]

end Canonical

section LeftAxis

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
  (eX : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) (iY : Y ⟶ P)
  (h₁ : iY.left ≫ p₁.left = Y.hom ≫ eX.left) (h₂ : iY.left ≫ p₂.left = 𝟙 Y.left)
  (hglob : Function.Surjective (secHom X.hom ⊤).hom)

include hP halgX halgY halgP hU hV hVa h₁ h₂ hglob in
/-- **The left-axis slant formula.** Let `P` be the fibre product of `X` and `Y` over a field,
with a rational point `eX` of `X` and the axis `iY = (eX, id) : Y ⟶ P`, and suppose the global
functions of `X` are constants. For every actual class `x ∈ H¹(X, 𝒪)` and every
`e ∈ Hⁿ⁺¹(P, 𝒪)`, the shuffle slant by an actual dual `ell` of the creation `p₁^* x ∪ e` is
`ell x` times the axis pullback `iY^* e`. -/
theorem slantByH1Dual_creation_pull_left
    (ell : (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K] K)
    (x : (relativeCohomology X.hom 1).obj (unitModule X.left)) (n : ℕ)
    (e : (relativeCohomology P.hom (n + 1)).obj (unitModule P.left)) :
    slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa hUVtop hUVa ell
        (n + 1)
        (creationCanonical P.hom (prodCover p₁.left p₂.left U V) hUVtop hUVa (n + 1)
          (unitCohomologyPullbackLinear p₁ 1 x) e) =
      ell x • unitCohomologyPullbackLinear iY (n + 1) e := by
  obtain ⟨i₀, hi₀⟩ := exists_top_le_preimage (Field.toIsField K) eX.left hUtop.ge
  have hx₀ : eX.left ≫ X.hom = 𝟙 _ := by simp
  obtain ⟨z, rfl⟩ := canonicalClass_surjective X.hom U hUtop hUa 0 x
  obtain ⟨w, rfl⟩ := canonicalClass_surjective P.hom (prodCover p₁.left p₂.left U V)
    hUVtop hUVa n e
  have hz : Cech.d (ab X.left.presheaf) U 1 (z.1 : C (ab X.left.presheaf) U 1) = 0 := by
    rw [← dCochain_unit X.hom U 1 z.1]
    exact z.2
  have hw : Cech.d (ab P.left.presheaf) (prodCover p₁.left p₂.left U V) (n + 1)
      (w.1 : C (ab P.left.presheaf) (prodCover p₁.left p₂.left U V) (n + 1)) = 0 := by
    rw [← dCochain_unit P.hom (prodCover p₁.left p₂.left U V) (n + 1) w.1]
    exact w.2
  set l := h1DualCochainFunctional X.hom U hUtop hUa halgX ell with hl
  obtain ⟨ν, hν⟩ := exists_dual_correction halgX U eX.left hx₀ i₀ hi₀ hUtop.ge hglob l
    (z.1 : C (ab X.left.presheaf) U 1)
  have hdual := h1DualCochainFunctional_cocycle X.hom U hUtop hUa halgX ell z
  change l (z.1 : C (ab X.left.presheaf) U 1) = _ at hdual
  have hmain := L_cup_pull_left_eq hP halgX halgY U V hU hV l eX.left hx₀ iY.left h₁ h₂ i₀ hi₀
    n (z.1 : C (ab X.left.presheaf) U 1) hz
    (w.1 : C (ab P.left.presheaf) (prodCover p₁.left p₂.left U V) (n + 1)) hw ν hν
  dsimp only [unitCohomologyPullbackLinear]
  rw [pull_canonicalClass p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
      (fun _ => inf_le_left) hUtop hUVtop hUa hUVa,
    pull_canonicalClass iY (prodCover p₁.left p₂.left U V) V (fun k => (i₀, k))
      (axis_le_prodCover U V eX.left iY.left h₁ h₂ i₀ hi₀) hUVtop hVtop hUVa hVa,
    creationCanonical_canonicalClass]
  unfold slantByH1Dual
  rw [slantCanonical_canonicalClass, ← map_smul]
  refine canonicalClass_eq_of_sub_eq_dCochain Y.hom V hVtop hVa n _ _
    (show cochain Y.hom V (unitModule Y.left) n from
      L hP halgX halgY U V hU hV ν n
        (w.1 : C (ab P.left.presheaf) (prodCover p₁.left p₂.left U V) (n + 1))) ?_
  have key : HSub.hSub (α := ∀ b : Fin (n + 2) → κ, Γ(Y.left, inter V b))
      (β := ∀ b : Fin (n + 2) → κ, Γ(Y.left, inter V b))
      (L hP halgX halgY U V hU hV l (n + 1)
        (cup₁ P.left.presheaf (prodCover p₁.left p₂.left U V)
          ((unitCochainMap p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
            (fun _ => inf_le_left)).f 1 z.1) w.1))
      (HSMul.hSMul (α := CommRingCat.of K) (β := ∀ b : Fin (n + 2) → κ, Γ(Y.left, inter V b))
        (ell (canonicalClass X.hom U hUtop hUa 0 z))
        ((unitCochainMap iY (prodCover p₁.left p₂.left U V) V (fun k => (i₀, k))
          (axis_le_prodCover U V eX.left iY.left h₁ h₂ i₀ hi₀)).f (n + 1) w.1)) =
      dCochain Y.hom V (unitModule Y.left) n
        (L hP halgX halgY U V hU hV ν n
          (w.1 : C (ab P.left.presheaf) (prodCover p₁.left p₂.left U V) (n + 1))) := by
    rw [unitCochainMap_eq_pull, unitCochainMap_eq_pull, hmain, dCochain_unit, ← hdual]
    funext b
    rw [Pi.sub_apply]
    exact add_sub_cancel_left _ _
  apply (cochainSecEquiv Y.hom V halgY (n + 1)).injective
  rw [map_sub, Submodule.coe_smul, map_smul]
  exact key

end LeftAxis

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
