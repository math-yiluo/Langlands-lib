import Langlands.AlgebraicGeometry.Modules.BiCech.Cup
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.ProductCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

/-!
# The cup map on products of affine opens is bijective

Let `P` be a fibre product of `πX : X ⟶ Spec R` and `πY : Y ⟶ Spec R` with projections `p₁`,
`p₂`, and `πP = p₁ ≫ πX`. Sections are `R`-modules through the structure morphisms
(`OModulePresheaf.ofModules`). The cup map induces an `R`-linear map
`cupLin : L(U) ⊗[R] M(V) → (p₁^* L ⊗ p₂^* M)(p₁⁻¹ U ∩ p₂⁻¹ V)`.

If `U` and `V` are affine and carry frames `e` of `L` and `e'` of `M`, then `cupLin` is
bijective: under the identifications `Γ(X, U) ≅ L(U)`, `a ↦ a • e`, and
`Γ(Y, V) ≅ M(V)`, `b ↦ b • e'`, it becomes the bijection
`Γ(X, U) ⊗[R] Γ(Y, V) ≅ Γ(P, p₁⁻¹ U ∩ p₂⁻¹ V)` of `FieldTwoAxisH1Injectivity.tensorSec`
followed by multiplication with the frame `cup e e'`. The finite-family version
`cupFam` is bijective by the same argument after `TensorProduct.piLeft` and `piRight`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
  Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof Scheme.Modules
  OModulePresheaf

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {πP : P ⟶ Spec R} (hπ : p₁ ≫ πX = πP) (hP : IsPullback p₁ p₂ πX πY)
  {L : X.Modules} {M : Y.Modules}

section Linear

variable (L M)

include hπ in
lemma appLE_algebraMap_left (U : X.Opens) {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U) (r : R) :
    p₁.appLE U W hW ((Scheme.TwoAffineOpenCover.algebraOfHom πX U).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom πP W).algebraMap r := by
  subst hπ
  have h := Scheme.Hom.appLE_comp_appLE p₁ πX ⊤ U W (le_top.trans_eq πX.preimage_top.symm) hW
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  exact congrArg (fun φ => (ConcreteCategory.hom φ) ((Scheme.ΓSpecIso (.of R)).inv.hom r)) h

include hπ hP in
lemma appLE_algebraMap_right (V : Y.Opens) {W : P.Opens} (hW : W ≤ p₂ ⁻¹ᵁ V) (r : R) :
    p₂.appLE V W hW ((Scheme.TwoAffineOpenCover.algebraOfHom πY V).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom πP W).algebraMap r := by
  have hπ' : p₂ ≫ πY = πP := hP.w.symm.trans hπ
  subst hπ'
  have h := Scheme.Hom.appLE_comp_appLE p₂ πY ⊤ V W (le_top.trans_eq πY.preimage_top.symm) hW
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  exact congrArg (fun φ => (ConcreteCategory.hom φ) ((Scheme.ΓSpecIso (.of R)).inv.hom r)) h

include hπ hP in
/-- The cup map as an `R`-bilinear map. -/
def cupBilin {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) :
    (ofModules πX L).obj U →ₗ[R] (ofModules πY M).obj V →ₗ[R]
      (ofModules πP (extTensor p₁ p₂ L M)).obj W :=
  LinearMap.mk₂ R (fun l m => cup hW l m) (fun l l' m => cup_add_left hW l l' m)
    (fun r l m => by
      refine (cup_smul_left hW ((Scheme.TwoAffineOpenCover.algebraOfHom πX U).algebraMap r)
        l m).trans ?_
      rw [appLE_algebraMap_left hπ]
      rfl)
    (fun l m m' => cup_add_right hW l m m')
    (fun r l m => by
      refine (cup_smul_right hW ((Scheme.TwoAffineOpenCover.algebraOfHom πY V).algebraMap r)
        l m).trans ?_
      rw [appLE_algebraMap_right hπ hP]
      rfl)

include hπ hP in
/-- The cup map as an `R`-linear map on the tensor product. -/
def cupLin {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) :
    (ofModules πX L).obj U ⊗[R] (ofModules πY M).obj V →ₗ[R]
      (ofModules πP (extTensor p₁ p₂ L M)).obj W :=
  TensorProduct.lift (cupBilin hπ hP L M hW)

lemma cupLin_tmul {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    (l : (ofModules πX L).obj U) (m : (ofModules πY M).obj V) :
    cupLin hπ hP L M hW (l ⊗ₜ m) = cup hW l m :=
  TensorProduct.lift.tmul _ _

end Linear

section Bijective

variable {Z : Scheme.{u}} {πZ : Z ⟶ Spec R} {N : Z.Modules}

lemma isFrameOn_self_bijective {U : Z.Opens} {e : Γ(N, U)} (he : IsFrameOn e U) :
    Function.Bijective fun a : Γ(Z, U) => a • e := by
  have h := he (le_refl U) (le_refl U)
  have hid : N.presheaf.map (homOfLE (le_refl U)).op e = e := by
    rw [show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl, N.presheaf.map_id]
    rfl
  rwa [hid] at h

/-- For a frame `e` of `N` on `U`, the `R`-linear bijection `Γ(Z, U) → N(U)`, `a ↦ a • e`. -/
def frameEquiv {U : Z.Opens} {e : Γ(N, U)} (he : IsFrameOn e U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ U
    Γ(Z, U) ≃ₗ[R] (ofModules πZ N).obj U :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ U
  LinearEquiv.ofBijective
    ({ toFun := fun a => (a • e : Γ(N, U))
       map_add' := fun a b => add_smul a b e
       map_smul' := fun r a => by
        change ((Scheme.TwoAffineOpenCover.algebraOfHom πZ U).algebraMap r * a) • e =
          (Scheme.TwoAffineOpenCover.algebraOfHom πZ U).algebraMap r • (a • e)
        rw [mul_smul] } : Γ(Z, U) →ₗ[R] (ofModules πZ N).obj U)
    (isFrameOn_self_bijective he)

lemma frameEquiv_apply {U : Z.Opens} {e : Γ(N, U)} (he : IsFrameOn e U) (a : Γ(Z, U)) :
    frameEquiv (πZ := πZ) he a = (a • e : Γ(N, U)) :=
  rfl

include hπ hP in
/-- On a product of affine opens carrying frames, the cup map is bijective. -/
theorem cupLin_bijective {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {e : Γ(L, U)} {e' : Γ(M, V)} (he : IsFrameOn e U) (he' : IsFrameOn e' V) :
    Function.Bijective (cupLin hπ hP L M (le_refl (prodOpen p₁ p₂ U V))) := by
  let _ : ∀ W : X.Opens, Algebra R Γ(X, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom πX W
  let _ : ∀ W : Y.Opens, Algebra R Γ(Y, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom πY W
  have halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom := fun W => rfl
  have halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom := fun W => rfl
  set W := prodOpen p₁ p₂ U V
  let eL := frameEquiv (πZ := πX) he
  let eM := frameEquiv (πZ := πY) he'
  have hε := isFrameOn_cup (le_refl W) he he'
  have hθ := isFrameOn_self_bijective hε
  have key : ∀ t, cupLin hπ hP L M (le_refl W) (TensorProduct.congr eL eM t) =
      (tensorSec halgX halgY hP U V).hom t • cup (le_refl W) e e' := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [TensorProduct.congr_tmul, cupLin_tmul, frameEquiv_apply, frameEquiv_apply,
        cup_smul_left, cup_smul_right, smul_smul, tensorSec_tmul]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, add_smul]
      rfl
  have hcomp : ⇑(cupLin hπ hP L M (le_refl W)) =
      ((fun c : Γ(P, W) => c • cup (le_refl W) e e') ∘ (tensorSec halgX halgY hP U V).hom) ∘
        (TensorProduct.congr eL eM).symm := by
    funext x
    obtain ⟨t, rfl⟩ := (TensorProduct.congr eL eM).surjective x
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    exact key t
  rw [hcomp]
  exact (hθ.comp (tensorSec_bijective halgX halgY hP hU hV)).comp
    (TensorProduct.congr eL eM).symm.bijective

end Bijective

end Langlands.AlgebraicGeometry.Modules.BiCech
