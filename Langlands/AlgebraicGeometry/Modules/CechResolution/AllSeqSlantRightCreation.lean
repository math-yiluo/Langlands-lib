import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCreation
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqMixedSlant
import Langlands.AlgebraicGeometry.CechSlantRightCup

/-! # Right-axis creation and shuffle slant on actual cohomology -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech Cech.KunnethDetection DerivedSections
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

private lemma homologyMap_eq_of_middle {C : Type*} [Category* C] [Preadditive C]
    {S T : ShortComplex C} [S.HasHomology] [T.HasHomology] (f g : S ⟶ T)
    (h : f.τ₂ = g.τ₂) : ShortComplex.homologyMap f = ShortComplex.homologyMap g := by
  apply (cancel_epi S.homologyπ).mp
  apply (cancel_mono T.homologyι).mp
  simp only [Category.assoc, ShortComplex.π_homologyMap_ι, h]

variable {R : CommRingCat.{u}} {X Y P : Over (Spec R)}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
  (hP : IsPullback p₁.left p₂.left X.hom Y.hom)
  [∀ W : X.left.Opens, Algebra R Γ(X.left, W)]
  (halgX : ∀ W : X.left.Opens, algebraMap R Γ(X.left, W) = (secHom X.hom W).hom)
  [∀ W : Y.left.Opens, Algebra R Γ(Y.left, W)]
  (halgY : ∀ W : Y.left.Opens, algebraMap R Γ(Y.left, W) = (secHom Y.hom W).hom)
  [∀ W : P.left.Opens, Algebra R Γ(P.left, W)]
  (halgP : ∀ W : P.left.Opens, algebraMap R Γ(P.left, W) = (secHom P.hom W).hom)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X.left, inter U σ)) →ₗ[R] R)
  (hl : ∀ y : C (ab X.left.presheaf) U 0, l (Cech.d (ab X.left.presheaf) U 0 y) = 0)

/-- The right-axis cup creator on the scalar-linear ordered Cech homology. -/
def rightAxisCreationH (n : ℕ) :
    (cochainComplex Y.hom V (unitModule Y.left)).homology 1 →ₗ[R]
      (cochainComplex P.hom (prodCover p₁.left p₂.left U V) (unitModule P.left)).homology n →ₗ[R]
        (cochainComplex P.hom (prodCover p₁.left p₂.left U V) (unitModule P.left)).homology (n + 1) :=
  (creationH P.hom (prodCover p₁.left p₂.left U V) n).comp
    (HomologicalComplex.homologyMap
      (unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
        (fun _ => inf_le_right)) 1).hom

lemma slantCochainMap_right_creation
    (z : LinearMap.ker (dCochain Y.hom V (unitModule Y.left) 1)) (n : ℕ) :
    creationCochainMap P.hom (prodCover p₁.left p₂.left U V)
        ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
          (fun _ => inf_le_right)).f 1 z.1) (n + 1) ≫
        slantCochainMap hP halgX halgY halgP p₁.w U V hU hV l (n + 1) =
      -(slantCochainMap hP halgX halgY halgP p₁.w U V hU hV l n ≫
        creationCochainMap Y.hom V z.1 n) := by
  ext e
  change slantCochainMap hP halgX halgY halgP p₁.w U V hU hV l (n + 1)
      (creationCochainMap P.hom (prodCover p₁.left p₂.left U V)
        ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
          (fun _ => inf_le_right)).f 1 z.1) (n + 1) e) =
    -(creationCochainMap Y.hom V z.1 n
      (slantCochainMap hP halgX halgY halgP p₁.w U V hU hV l n e))
  apply (cochainSecEquiv Y.hom V halgY (n + 1)).injective
  rw [map_neg]
  change L hP halgX halgY U V hU hV l (n + 1)
      (cup₁ P.left.presheaf (prodCover p₁.left p₂.left U V)
        ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
          (fun _ => inf_le_right)).f 1 z.1) e) =
    -cup₁ Y.left.presheaf V z.1 (L hP halgX halgY U V hU hV l n e)
  rw [unitCochainMap_eq_pull]
  exact L_cup_pull_right hP halgX halgY U hU l V hV n z.1
    (by rw [← dCochain_unit Y.hom V 1 z.1]; exact z.2) e

include hl in
lemma slantH_right_creationByCocycle
    (z : LinearMap.ker (dCochain Y.hom V (unitModule Y.left) 1)) (n : ℕ) :
    creationByCocycle P.hom (prodCover p₁.left p₂.left U V)
        ⟨_, chainMap_mem_ker V (prodCover p₁.left p₂.left U V)
          (unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
            (fun _ => inf_le_right)) 0 z⟩ (n + 1) ≫
        slantH hP halgX halgY halgP p₁.w U V hU hV l hl (n + 1) =
      -(slantH hP halgX halgY halgP p₁.w U V hU hV l hl n ≫
        creationByCocycle Y.hom V z n) := by
  unfold creationByCocycle slantH creationHomologyMap slantHomologyMap
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    ← ShortComplex.homologyMap_neg]
  apply homologyMap_eq_of_middle
  simpa only [ShortComplex.comp_τ₂, ShortComplex.neg_τ₂, creationShortComplexMap_τ₂,
    slantShortComplexMap_τ₂] using
    slantCochainMap_right_creation p₁ p₂ hP halgX halgY halgP U V hU hV l z n

include hl in
/-- Shuffle slant anticommutes with right-axis creation in every degree. -/
lemma slantH_rightAxisCreationH (n : ℕ)
    (y : (cochainComplex Y.hom V (unitModule Y.left)).homology 1)
    (e : (cochainComplex P.hom (prodCover p₁.left p₂.left U V)
      (unitModule P.left)).homology (n + 1)) :
    slantH hP halgX halgY halgP p₁.w U V hU hV l hl (n + 1)
        (rightAxisCreationH p₁ p₂ U V (n + 1) y e) =
      -creationH Y.hom V n y
        (slantH hP halgX halgY halgP p₁.w U V hU hV l hl n e) := by
  obtain ⟨z, rfl⟩ := classMap_surjective Y.hom V (unitModule Y.left) 0 y
  unfold rightAxisCreationH
  simp only [LinearMap.comp_apply]
  rw [homologyMap_classMap _ 0 _ (chainMap_mem_ker V _ _ 0 z),
    creationH_classMap, creationH_classMap]
  exact congrArg (fun f => f e)
    (slantH_right_creationByCocycle p₁ p₂ hP halgX halgY halgP U V hU hV l hl z n)

section Canonical

variable [IsSeparated Y.hom] [IsSeparated P.hom]
  (hVtop : ⨆ j, V j = ⊤) (hVa : ∀ j, IsAffineOpen (V j))
  (hUVtop : ⨆ j, prodCover p₁.left p₂.left U V j = ⊤)
  (hUVa : ∀ j, IsAffineOpen (prodCover p₁.left p₂.left U V j))

/-- Creation on actual cohomology by a class pulled back from the right factor. -/
def rightAxisCreationCanonical (n : ℕ) :
    (relativeCohomology Y.hom 1).obj (unitModule Y.left) →ₗ[R]
      (relativeCohomology P.hom n).obj (unitModule P.left) →ₗ[R]
        (relativeCohomology P.hom (n + 1)).obj (unitModule P.left) :=
  (creationCanonical P.hom (prodCover p₁.left p₂.left U V) hUVtop hUVa n).comp
    (unitCohomologyPullbackLinear p₂ 1)

include hl in
/-- Right-axis creation anticommutes with actual shuffle slant in every degree. -/
theorem slantCanonical_rightAxisCreationCanonical (n : ℕ)
    (y : (relativeCohomology Y.hom 1).obj (unitModule Y.left))
    (e : (relativeCohomology P.hom (n + 1)).obj (unitModule P.left)) :
    slantCanonical hP halgX halgY halgP p₁.w U V hU hV l hl hVtop hVa hUVtop hUVa
        (n + 1) (rightAxisCreationCanonical p₁ p₂ U V hUVtop hUVa (n + 1) y e) =
      -creationCanonical Y.hom V hVtop hVa n y
        (slantCanonical hP halgX halgY halgP p₁.w U V hU hV l hl
          hVtop hVa hUVtop hUVa n e) := by
  obtain ⟨y', rfl⟩ := (cohomologyEquiv Y.hom V hVtop hVa 1).surjective y
  obtain ⟨e', rfl⟩ :=
    (cohomologyEquiv P.hom (prodCover p₁.left p₂.left U V) hUVtop hUVa (n + 1)).surjective e
  unfold rightAxisCreationCanonical unitCohomologyPullbackLinear
  simp only [LinearMap.comp_apply]
  rw [pull_cohomologyEquiv p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
    (fun _ => inf_le_right) hVtop hUVtop hVa hUVa]
  simp only [creationCanonical_apply, slantCanonical_apply,
    LinearEquiv.symm_apply_apply]
  simpa only [rightAxisCreationH, LinearMap.comp_apply, map_neg] using
    congrArg (cohomologyEquiv Y.hom V hVtop hVa (n + 1))
      (slantH_rightAxisCreationH p₁ p₂ hP halgX halgY halgP U V hU hV l hl n y' e')

end Canonical

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
