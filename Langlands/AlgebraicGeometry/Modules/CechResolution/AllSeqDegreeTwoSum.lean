import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqAxisSlant
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCompositionProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackIdentityProof
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingProof

/-! # Injectivity of the actual degree-two sum map -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open DerivedSections

section PullbackLaws

variable {R : CommRingCat.{u}}

lemma unitCohomologyPullback_id (X : Over (Spec R)) (n : ℕ) :
    unitCohomologyPullbackLinear (𝟙 X) n = LinearMap.id := by
  unfold unitCohomologyPullbackLinear
  rw [← ModuleCat.hom_id]
  congr 1
  rw [show (Langlands.Scheme.Modules.pullbackUnitIso (𝟙 X : X ⟶ X).left).hom =
      (Scheme.Modules.pullbackId X.left).hom.app (unitModule X.left) from
    Langlands.Scheme.Modules.pullbackUnitIdentity X.left]
  exact relativeCohomologyPullback_identity _ n

lemma unitCohomologyPullback_comp {X Y Z : Over (Spec R)} (f : Y ⟶ X) (g : Z ⟶ Y)
    (n : ℕ) : unitCohomologyPullbackLinear (g ≫ f) n =
      (unitCohomologyPullbackLinear g n).comp (unitCohomologyPullbackLinear f n) := by
  unfold unitCohomologyPullbackLinear
  rw [← ModuleCat.hom_comp]
  congr 1
  have hc : (Scheme.Modules.pullbackComp g.left f.left).hom.app (unitModule X.left) ≫
      (Langlands.Scheme.Modules.pullbackUnitIso (g ≫ f).left).hom =
      (Scheme.Modules.pullback g.left).map (Langlands.Scheme.Modules.pullbackUnitIso f.left).hom ≫
        (Langlands.Scheme.Modules.pullbackUnitIso g.left).hom :=
    Langlands.Scheme.Modules.pullbackUnitComposition Z.left Y.left X.left g.left f.left
  rw [← relativeCohomologyPullback_comp f g]
  simp only [Category.assoc, ← Functor.map_comp, hc]
  rw [Functor.map_comp, relativeCohomologyPullback_naturality_assoc]

/-- Positive-degree pullback to the affine base is zero. -/
lemma unitCohomologyPullback_to_base {Y : Over (Spec R)}
    (e : Over.mk (𝟙 (Spec R)) ⟶ Y) (n : ℕ) :
    unitCohomologyPullbackLinear e (n + 1) = 0 := by
  have hzero := (affineQuasicoherentCohomologyVanishing (Spec R) inferInstance
    (unitModule (Spec R)) inferInstance n).2 R (𝟙 (Spec R))
  exact congrArg ModuleCat.Hom.hom (hzero.eq_of_tgt
    (relativeCohomologyPullback e (unitModule Y.left) (n + 1) ≫
      (relativeCohomology (𝟙 (Spec R)) (n + 1)).map
        (Langlands.Scheme.Modules.pullbackUnitIso e.left).hom) 0)

/-- Pullback through the affine base vanishes in every positive degree. -/
lemma unitCohomologyPullback_base {X Y : Over (Spec R)}
    (e : Over.mk (𝟙 (Spec R)) ⟶ Y) (n : ℕ) :
    unitCohomologyPullbackLinear (Over.homMk X.hom ≫ e) (n + 1) = 0 := by
  rw [unitCohomologyPullback_comp, unitCohomologyPullback_to_base, LinearMap.comp_zero]

/-- Axis restrictions distinguish the two positive-degree projection summands. -/
lemma axisPullbacks_eq_zero {X Y P : Over (Spec R)} (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
    (eX : Over.mk (𝟙 (Spec R)) ⟶ X) (eY : Over.mk (𝟙 (Spec R)) ⟶ Y)
    (iX : X ⟶ P) (iY : Y ⟶ P)
    (hXX : iX ≫ p₁ = 𝟙 X) (hXY : iX ≫ p₂ = Over.homMk X.hom ≫ eY)
    (hYX : iY ≫ p₁ = Over.homMk Y.hom ≫ eX) (hYY : iY ≫ p₂ = 𝟙 Y)
    (n : ℕ) (x : (relativeCohomology X.hom (n + 1)).obj (unitModule X.left))
    (y : (relativeCohomology Y.hom (n + 1)).obj (unitModule Y.left))
    (h : unitCohomologyPullbackLinear p₁ (n + 1) x +
      unitCohomologyPullbackLinear p₂ (n + 1) y = 0) : x = 0 ∧ y = 0 := by
  constructor
  · have hi := congrArg (unitCohomologyPullbackLinear iX (n + 1)) h
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← unitCohomologyPullback_comp, ← unitCohomologyPullback_comp, hXX, hXY,
      unitCohomologyPullback_id, unitCohomologyPullback_base] at hi
    simpa only [LinearMap.id_apply, LinearMap.zero_apply, add_zero, map_zero] using hi
  · have hi := congrArg (unitCohomologyPullbackLinear iY (n + 1)) h
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← unitCohomologyPullback_comp, ← unitCohomologyPullback_comp, hYX, hYY,
      unitCohomologyPullback_id, unitCohomologyPullback_base] at hi
    simpa only [LinearMap.id_apply, LinearMap.zero_apply, zero_add, map_zero] using hi

end PullbackLaws

open Langlands.Cohomology Cech Cech.KunnethDetection
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open scoped TensorProduct

section DegreeTwoSum

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

/-- The actual degree-two sum of the two axis pullbacks and the mixed cup. -/
def degreeTwoSum :
    (relativeCohomology X.hom 2).obj (unitModule X.left) ×
      ((relativeCohomology X.hom 1).obj (unitModule X.left) ⊗[K]
        (relativeCohomology Y.hom 1).obj (unitModule Y.left)) ×
      (relativeCohomology Y.hom 2).obj (unitModule Y.left) →ₗ[K]
        (relativeCohomology P.hom 2).obj (unitModule P.left) where
  toFun s := unitCohomologyPullbackLinear p₁ 2 s.1 +
    mixedTensor p₁ p₂ U V hUVtop hUVa s.2.1 + unitCohomologyPullbackLinear p₂ 2 s.2.2
  map_add' s t := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c s := by
    change unitCohomologyPullbackLinear p₁ 2 (c • s.1) +
      mixedTensor p₁ p₂ U V hUVtop hUVa (c • s.2.1) +
        unitCohomologyPullbackLinear p₂ 2 (c • s.2.2) = _
    simp only [map_smul, smul_add, RingHom.id_apply]

omit [IsSeparated X.hom] [IsSeparated Y.hom]
  [∀ W : X.left.Opens, Algebra (CommRingCat.of K) Γ(X.left, W)]
  [∀ W : Y.left.Opens, Algebra (CommRingCat.of K) Γ(Y.left, W)]
  [∀ W : P.left.Opens, Algebra (CommRingCat.of K) Γ(P.left, W)] in
lemma degreeTwoSum_apply (x t y) :
    degreeTwoSum p₁ p₂ U V hUVtop hUVa (x, t, y) =
      unitCohomologyPullbackLinear p₁ 2 x + mixedTensor p₁ p₂ U V hUVtop hUVa t +
        unitCohomologyPullbackLinear p₂ 2 y := rfl

include hP halgX halgY halgP hUtop hUa hU hV hVtop hVa in
/-- A vanishing degree-two sum has vanishing mixed tensor. -/
lemma mixedTensor_eq_zero_of_degreeTwoSum
    (x : (relativeCohomology X.hom 2).obj (unitModule X.left))
    (t : (relativeCohomology X.hom 1).obj (unitModule X.left) ⊗[K]
      (relativeCohomology Y.hom 1).obj (unitModule Y.left))
    (y : (relativeCohomology Y.hom 2).obj (unitModule Y.left))
    (h : degreeTwoSum p₁ p₂ U V hUVtop hUVa (x, t, y) = 0) : t = 0 := by
  let b := Module.Free.chooseBasis K ((relativeCohomology X.hom 1).obj (unitModule X.left))
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  have hi := congrArg
    (slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa
      hUVtop hUVa (b.coord i) 1) h
  rw [degreeTwoSum_apply, map_add, map_add,
    slantByH1Dual_pull_left p₁ p₂ hP halgX halgY halgP U V hUtop hUa hU hV
      hVtop hVa hUVtop hUVa,
    slantByH1Dual_pull_right p₁ p₂ hP halgX halgY halgP U V hUtop hUa hU hV
      hVtop hVa hUVtop hUVa,
    slantByH1Dual_mixedTensor p₁ p₂ hP halgX halgY halgP U V hUtop hUa hU hV
      hVtop hVa hUVtop hUVa] at hi
  simpa only [zero_add, add_zero, map_zero] using hi

include hP halgX halgY halgP hUtop hUa hU hV hVtop hVa in
/-- With rational axes, the actual degree-two sum map is injective. -/
theorem degreeTwoSum_injective
    (eX : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)
    (eY : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Y)
    (iX : X ⟶ P) (iY : Y ⟶ P)
    (hXX : iX ≫ p₁ = 𝟙 X) (hXY : iX ≫ p₂ = Over.homMk X.hom ≫ eY)
    (hYX : iY ≫ p₁ = Over.homMk Y.hom ≫ eX) (hYY : iY ≫ p₂ = 𝟙 Y) :
    Function.Injective (degreeTwoSum p₁ p₂ U V hUVtop hUVa) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, t, y⟩ h
  have ht := mixedTensor_eq_zero_of_degreeTwoSum p₁ p₂ hP halgX halgY halgP U V
    hUtop hUa hU hV hVtop hVa hUVtop hUVa x t y h
  subst t
  rw [degreeTwoSum_apply, map_zero, add_zero] at h
  obtain ⟨hx, hy⟩ := axisPullbacks_eq_zero p₁ p₂ eX eY iX iY hXX hXY hYX hYY 1 x y h
  subst x
  subst y
  rfl

include hP halgX halgY halgP hUtop hUa hU hV hVtop hVa in
/-- Rational points supply the axes in every actual fibre product. -/
theorem degreeTwoSum_injective_of_points
    (eX : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)
    (eY : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Y) :
    Function.Injective (degreeTwoSum p₁ p₂ U V hUVtop hUVa) := by
  obtain ⟨jX, hjXX, hjXY⟩ := hP.exists_lift (𝟙 X.left) (X.hom ≫ eY.left)
    (by simp only [Category.assoc, eY.w, Over.mk_hom, Category.comp_id, Category.id_comp])
  obtain ⟨jY, hjYX, hjYY⟩ := hP.exists_lift (Y.hom ≫ eX.left) (𝟙 Y.left)
    (by simp only [Category.assoc, eX.w, Over.mk_hom, Category.comp_id, Category.id_comp])
  let iX : X ⟶ P := Over.homMk jX (by
    rw [← p₁.w, ← Category.assoc, hjXX, Category.id_comp])
  let iY : Y ⟶ P := Over.homMk jY (by
    rw [← p₂.w, ← Category.assoc, hjYY, Category.id_comp])
  exact degreeTwoSum_injective p₁ p₂ hP halgX halgY halgP U V hUtop hUa hU hV
    hVtop hVa hUVtop hUVa eX eY iX iY
      (Over.OverMorphism.ext hjXX) (Over.OverMorphism.ext hjXY)
      (Over.OverMorphism.ext hjYX) (Over.OverMorphism.ext hjYY)

end DegreeTwoSum

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
