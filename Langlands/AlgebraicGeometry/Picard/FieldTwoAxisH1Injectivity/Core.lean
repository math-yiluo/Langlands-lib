import Langlands.Algebra.TensorDegreeOneKunneth
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.ProductCover

/-!
# Degree-one Čech cocycles on a product cover over a field

Let `P` be a fibre product of `X ⟶ Spec R` and `Y ⟶ Spec R` over a field `R`, with projections
`p₁` and `p₂`. Cover `P` by the opens `p₁⁻¹ U i ⊓ p₂⁻¹ V j`, where `U` and `V` are finite covers
of `X` and `Y` by affine opens with affine pairwise intersections, and suppose that all global
functions on `X` and on `Y` come from `R`. Let `x₀` and `y₀` be `R`-points of `X` and `Y`, and
let `i₁ : X ⟶ P` and `i₂ : Y ⟶ P` be the axes through `y₀` and `x₀`. A Čech `1`-cocycle `z` of
the structure sheaf of `P` on this cover whose pullbacks along `i₁` and `i₂` are Čech
coboundaries is itself a Čech coboundary.

The proof identifies the horizontal part `(i, j), (k, j)` and the vertical part
`(k, j), (k, l)` of `z` with elements of tensor products of Čech cochains of `X` and `Y`, and
applies the degree-one Künneth lemma
`Langlands.Algebra.TensorDegreeOneKunneth.exists_eq_of_degreeOne`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

section Restriction

lemma map_map_apply {Z : Scheme.{u}} {V W W' : Z.Opens} (h₁ : V ≤ W) (h₂ : W ≤ W')
    (x : Γ(Z, W')) :
    (Z.presheaf.map (homOfLE h₁).op).hom ((Z.presheaf.map (homOfLE h₂).op).hom x) =
      (Z.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma map_self_apply {Z : Scheme.{u}} {V : Z.Opens} (h : V ≤ V) (x : Γ(Z, V)) :
    (Z.presheaf.map (homOfLE h).op).hom x = x := by
  change (Z.presheaf.map (𝟙 (op V))).hom x = x
  rw [Z.presheaf.map_id]
  rfl

lemma map_app_apply {Z Z' : Scheme.{u}} (f : Z ⟶ Z') {W : Z'.Opens} {V : Z.Opens}
    (e : V ≤ f ⁻¹ᵁ W) (x : Γ(Z', W)) :
    (Z.presheaf.map (homOfLE e).op).hom ((f.app W).hom x) = (f.appLE W V e).hom x :=
  rfl

lemma appLE_map_apply {Z Z' : Scheme.{u}} (f : Z ⟶ Z') {W W' : Z'.Opens} {V : Z.Opens}
    (h : W ≤ W') (e : V ≤ f ⁻¹ᵁ W) (x : Γ(Z', W')) :
    (f.appLE W V e).hom ((Z'.presheaf.map (homOfLE h).op).hom x) =
      (f.appLE W' V (e.trans (f.preimage_mono h))).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end Restriction

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y}

lemma prodOpen_mono {U U' : X.Opens} {V V' : Y.Opens} (hU : U ≤ U') (hV : V ≤ V') :
    prodOpen p₁ p₂ U V ≤ prodOpen p₁ p₂ U' V' :=
  inf_le_inf (p₁.preimage_mono hU) (p₂.preimage_mono hV)

lemma prodOpen_inf (U U' : X.Opens) (V V' : Y.Opens) :
    prodOpen p₁ p₂ U V ⊓ prodOpen p₁ p₂ U' V' = prodOpen p₁ p₂ (U ⊓ U') (V ⊓ V') :=
  inf_inf_inf_comm _ _ _ _

variable (p₁ p₂) in
/-- The cover of the fibre product by the opens `p₁⁻¹ U a ⊓ p₂⁻¹ V b`. -/
abbrev prodCover {α β : Type*} (U : α → X.Opens) (V : β → Y.Opens) (ab : α × β) : P.Opens :=
  prodOpen p₁ p₂ (U ab.1) (V ab.2)

variable [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)

include halgX halgY in
/-- Over a field `R`, a Čech `1`-cocycle of the structure sheaf of `P = X ×_R Y` on the product
cover `p₁⁻¹ U i ⊓ p₂⁻¹ V j` whose pullbacks along the two axes `i₁` and `i₂` are coboundaries is
a coboundary. -/
theorem exists_coboundary_of_axes (hR : IsField R) (hP : IsPullback p₁ p₂ πX πY)
    {I J : Type*} [Finite I] [Finite J] (U : I → X.Opens) (V : J → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUU : ∀ i k, IsAffineOpen (U i ⊓ U k))
    (hV : ∀ j, IsAffineOpen (V j)) (hVV : ∀ j l, IsAffineOpen (V j ⊓ V l))
    (hcovU : ⊤ ≤ iSup U) (hcovV : ⊤ ≤ iSup V)
    (hglobX : Function.Surjective (secHom πX ⊤).hom)
    (hglobY : Function.Surjective (secHom πY ⊤).hom)
    (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (i₀ : I) (hi₀ : ⊤ ≤ x₀ ⁻¹ᵁ U i₀)
    (y₀ : Spec R ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) (j₀ : J) (hj₀ : ⊤ ≤ y₀ ⁻¹ᵁ V j₀)
    (i₁ : X ⟶ P) (h₁₁ : i₁ ≫ p₁ = 𝟙 X) (h₁₂ : i₁ ≫ p₂ = πX ≫ y₀)
    (i₂ : Y ⟶ P) (h₂₁ : i₂ ≫ p₁ = πY ≫ x₀) (h₂₂ : i₂ ≫ p₂ = 𝟙 Y)
    (z : ∀ a b, Γ(P, prodCover p₁ p₂ U V a ⊓ prodCover p₁ p₂ U V b))
    (hz : ∀ (a b c : I × J) {O : P.Opens}
      (h₁ : O ≤ prodCover p₁ p₂ U V a ⊓ prodCover p₁ p₂ U V b)
      (h₂ : O ≤ prodCover p₁ p₂ U V b ⊓ prodCover p₁ p₂ U V c)
      (h₃ : O ≤ prodCover p₁ p₂ U V a ⊓ prodCover p₁ p₂ U V c),
      (P.presheaf.map (homOfLE h₁).op).hom (z a b) +
          (P.presheaf.map (homOfLE h₂).op).hom (z b c) =
        (P.presheaf.map (homOfLE h₃).op).hom (z a c))
    (hz₁ : ∃ g : ∀ a, Γ(X, i₁ ⁻¹ᵁ prodCover p₁ p₂ U V a), ∀ a b,
      (i₁.app (prodCover p₁ p₂ U V a ⊓ prodCover p₁ p₂ U V b)).hom (z a b) =
        (X.presheaf.map (homOfLE (i₁.preimage_mono inf_le_right)).op).hom (g b) -
          (X.presheaf.map (homOfLE (i₁.preimage_mono inf_le_left)).op).hom (g a))
    (hz₂ : ∃ g : ∀ a, Γ(Y, i₂ ⁻¹ᵁ prodCover p₁ p₂ U V a), ∀ a b,
      (i₂.app (prodCover p₁ p₂ U V a ⊓ prodCover p₁ p₂ U V b)).hom (z a b) =
        (Y.presheaf.map (homOfLE (i₂.preimage_mono inf_le_right)).op).hom (g b) -
          (Y.presheaf.map (homOfLE (i₂.preimage_mono inf_le_left)).op).hom (g a)) :
    ∃ y : ∀ a, Γ(P, prodCover p₁ p₂ U V a), ∀ a b,
      z a b = (P.presheaf.map (homOfLE inf_le_right).op).hom (y b) -
        (P.presheaf.map (homOfLE inf_le_left).op).hom (y a) := by
  have hHle : ∀ (ik : I × I) (j : J), prodOpen p₁ p₂ (U ik.1 ⊓ U ik.2) (V j) ≤
      prodCover p₁ p₂ U V (ik.1, j) ⊓ prodCover p₁ p₂ U V (ik.2, j) := fun _ _ ↦
    le_inf (prodOpen_mono inf_le_left le_rfl) (prodOpen_mono inf_le_right le_rfl)
  have hVle : ∀ (i : I) (jl : J × J), prodOpen p₁ p₂ (U i) (V jl.1 ⊓ V jl.2) ≤
      prodCover p₁ p₂ U V (i, jl.1) ⊓ prodCover p₁ p₂ U V (i, jl.2) := fun _ _ ↦
    le_inf (prodOpen_mono le_rfl inf_le_left) (prodOpen_mono le_rfl inf_le_right)
  -- The horizontal and vertical parts of `z` as tensors of Čech cochains.
  obtain ⟨h, hh⟩ := (tensorFam_bijective halgX halgY hP (fun ik : I × I ↦ U ik.1 ⊓ U ik.2) V
    (fun ik ↦ hUU ik.1 ik.2) hV).2 fun ik j ↦
      (P.presheaf.map (homOfLE (hHle ik j)).op).hom (z (ik.1, j) (ik.2, j))
  obtain ⟨v, hv⟩ := (tensorFam_bijective halgX halgY hP U (fun jl : J × J ↦ V jl.1 ⊓ V jl.2)
    hU (fun jl ↦ hVV jl.1 jl.2)).2 fun i jl ↦
      (P.presheaf.map (homOfLE (hVle i jl)).op).hom (z (i, jl.1) (i, jl.2))
  have hh' : ∀ ik j, tensorFam halgX halgY hP (fun ik : I × I ↦ U ik.1 ⊓ U ik.2) V h ik j =
      (P.presheaf.map (homOfLE (hHle ik j)).op).hom (z (ik.1, j) (ik.2, j)) :=
    fun ik j ↦ congr_fun (congr_fun hh ik) j
  have hv' : ∀ i jl, tensorFam halgX halgY hP U (fun jl : J × J ↦ V jl.1 ⊓ V jl.2) v i jl =
      (P.presheaf.map (homOfLE (hVle i jl)).op).hom (z (i, jl.1) (i, jl.2)) :=
    fun i jl ↦ congr_fun (congr_fun hv i) jl
  -- The mixed cocycle condition.
  have hhv : (cechD πY halgY V).lTensor _ h = (cechD πX halgX U).rTensor _ v := by
    apply (tensorFam_bijective halgX halgY hP (fun ik : I × I ↦ U ik.1 ⊓ U ik.2)
      (fun jl : J × J ↦ V jl.1 ⊓ V jl.2) (fun ik ↦ hUU ik.1 ik.2) (fun jl ↦ hVV jl.1 jl.2)).1
    funext ik jl
    rw [cechD, cechD, LinearMap.lTensor_sub, LinearMap.rTensor_sub, LinearMap.sub_apply,
      LinearMap.sub_apply, map_sub, map_sub, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply,
      Pi.sub_apply, tensorFam_lTensor_resPi, tensorFam_lTensor_resPi, tensorFam_rTensor_resPi,
      tensorFam_rTensor_resPi, hh', hh', hv', hv']
    simp only [map_map_apply]
    have e₁ := hz (ik.1, jl.1) (ik.2, jl.1) (ik.2, jl.2)
      (O := prodOpen p₁ p₂ (U ik.1 ⊓ U ik.2) (V jl.1 ⊓ V jl.2))
      (le_inf (prodOpen_mono inf_le_left inf_le_left) (prodOpen_mono inf_le_right inf_le_left))
      (le_inf (prodOpen_mono inf_le_right inf_le_left)
        (prodOpen_mono inf_le_right inf_le_right))
      (le_inf (prodOpen_mono inf_le_left inf_le_left) (prodOpen_mono inf_le_right inf_le_right))
    have e₂ := hz (ik.1, jl.1) (ik.1, jl.2) (ik.2, jl.2)
      (O := prodOpen p₁ p₂ (U ik.1 ⊓ U ik.2) (V jl.1 ⊓ V jl.2))
      (le_inf (prodOpen_mono inf_le_left inf_le_left) (prodOpen_mono inf_le_left inf_le_right))
      (le_inf (prodOpen_mono inf_le_left inf_le_right)
        (prodOpen_mono inf_le_right inf_le_right))
      (le_inf (prodOpen_mono inf_le_left inf_le_left) (prodOpen_mono inf_le_right inf_le_right))
    linear_combination e₂ - e₁
  -- The restriction of the vertical part to the axis `i₂` is a boundary.
  have hvrange : TensorProduct.lid R _
      (((evalSec halgX x₀ hx₀ (U i₀) hi₀).toLinearMap ∘ₗ LinearMap.proj i₀).rTensor _ v) ∈
        LinearMap.range (cechD πY halgY V) := by
    obtain ⟨g, hg⟩ := hz₂
    refine LinearMap.mem_range.2 ⟨fun j ↦ (Y.presheaf.map (homOfLE
      (le_preimage_axis₂ x₀ i₂ h₂₁ h₂₂ (U i₀) hi₀ (V j))).op).hom (g (i₀, j)), ?_⟩
    funext jl
    rw [cechD_apply, ← appLE_axis₂_tensorFam halgX halgY hP U (fun jl : J × J ↦ V jl.1 ⊓ V jl.2)
      x₀ hx₀ i₂ h₂₁ h₂₂ i₀ hi₀ v jl, hv', appLE_map_apply, map_map_apply, map_map_apply]
    have e := congrArg (Y.presheaf.map (homOfLE
      ((le_preimage_axis₂ x₀ i₂ h₂₁ h₂₂ (U i₀) hi₀ (V jl.1 ⊓ V jl.2)).trans
        (i₂.preimage_mono (hVle i₀ jl)))).op).hom (hg (i₀, jl.1) (i₀, jl.2))
    rw [map_app_apply, map_sub, map_map_apply, map_map_apply] at e
    exact e.symm
  -- The restriction of the horizontal part to the axis `i₁` is a boundary.
  have hhrange : TensorProduct.rid R _
      (((evalSec halgY y₀ hy₀ (V j₀) hj₀).toLinearMap ∘ₗ LinearMap.proj j₀).lTensor _ h) ∈
        LinearMap.range (cechD πX halgX U) := by
    obtain ⟨g, hg⟩ := hz₁
    refine LinearMap.mem_range.2 ⟨fun i ↦ (X.presheaf.map (homOfLE
      (le_preimage_axis₁ y₀ i₁ h₁₁ h₁₂ (U i) (V j₀) hj₀)).op).hom (g (i, j₀)), ?_⟩
    funext ik
    rw [cechD_apply, ← appLE_axis₁_tensorFam halgX halgY hP (fun ik : I × I ↦ U ik.1 ⊓ U ik.2)
      V y₀ hy₀ i₁ h₁₁ h₁₂ j₀ hj₀ h ik, hh', appLE_map_apply, map_map_apply, map_map_apply]
    have e := congrArg (X.presheaf.map (homOfLE
      ((le_preimage_axis₁ y₀ i₁ h₁₁ h₁₂ (U ik.1 ⊓ U ik.2) (V j₀) hj₀).trans
        (i₁.preimage_mono (hHle ik j₀)))).op).hom (hg (ik.1, j₀) (ik.2, j₀))
    rw [map_app_apply, map_sub, map_map_apply, map_map_apply] at e
    exact e.symm
  have hC : ∀ x, cechD πX halgX U x = 0 → ∃ r : R, x = r • 1 :=
    fun x hx ↦ exists_eq_smul_one_of_cechD_eq_zero πX halgX U hcovU hglobX x hx
  have hD : ∀ x, cechD πY halgY V x = 0 → ∃ r : R, x = r • 1 :=
    fun x hx ↦ exists_eq_smul_one_of_cechD_eq_zero πY halgY V hcovV hglobY x hx
  have hεC : ((evalSec halgX x₀ hx₀ (U i₀) hi₀).toLinearMap ∘ₗ LinearMap.proj i₀)
      (1 : ∀ i, Γ(X, U i)) = 1 := by
    rw [LinearMap.comp_apply, LinearMap.proj_apply, Pi.one_apply, AlgHom.toLinearMap_apply,
      map_one]
  have hεD : ((evalSec halgY y₀ hy₀ (V j₀) hj₀).toLinearMap ∘ₗ LinearMap.proj j₀)
      (1 : ∀ j, Γ(Y, V j)) = 1 := by
    rw [LinearMap.comp_apply, LinearMap.proj_apply, Pi.one_apply, AlgHom.toLinearMap_apply,
      map_one]
  -- The degree-one Künneth lemma.
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : (∀ i, Γ(X, U i)) ⊗[R] (∀ j, Γ(Y, V j)),
      (cechD πX halgX U).rTensor _ w = h ∧ (cechD πY halgY V).lTensor _ w = v := by
    let _ : Field R := hR.toField
    exact Langlands.Algebra.TensorDegreeOneKunneth.exists_eq_of_degreeOne
      (cechD πX halgX U) (cechD πY halgY V) 1 1 _ _ hC hD (cechD_one πY halgY V) hεC hεD h v
      hhv hvrange hhrange
  refine ⟨fun a ↦ tensorFam halgX halgY hP U V w a.1 a.2, ?_⟩
  rintro ⟨i, j⟩ ⟨k, l⟩
  dsimp only
  have e₁ := congr_fun (congr_fun (congrArg
    (tensorFam halgX halgY hP (fun ik : I × I ↦ U ik.1 ⊓ U ik.2) V) hw₁) (i, k)) j
  rw [cechD, LinearMap.rTensor_sub, LinearMap.sub_apply, map_sub, Pi.sub_apply, Pi.sub_apply,
    tensorFam_rTensor_resPi, tensorFam_rTensor_resPi, hh'] at e₁
  have e₂ := congr_fun (congr_fun (congrArg
    (tensorFam halgX halgY hP U (fun jl : J × J ↦ V jl.1 ⊓ V jl.2)) hw₂) k) (j, l)
  rw [cechD, LinearMap.lTensor_sub, LinearMap.sub_apply, map_sub, Pi.sub_apply, Pi.sub_apply,
    tensorFam_lTensor_resPi, tensorFam_lTensor_resPi, hv'] at e₂
  have hO₁ : prodCover p₁ p₂ U V (i, j) ⊓ prodCover p₁ p₂ U V (k, l) ≤
      prodOpen p₁ p₂ (U i ⊓ U k) (V j) :=
    (prodOpen_inf (U i) (U k) (V j) (V l)).le.trans (prodOpen_mono le_rfl inf_le_left)
  have hO₂ : prodCover p₁ p₂ U V (i, j) ⊓ prodCover p₁ p₂ U V (k, l) ≤
      prodOpen p₁ p₂ (U k) (V j ⊓ V l) :=
    (prodOpen_inf (U i) (U k) (V j) (V l)).le.trans (prodOpen_mono inf_le_right le_rfl)
  have f₁ := congrArg (P.presheaf.map (homOfLE hO₁).op).hom e₁
  have f₂ := congrArg (P.presheaf.map (homOfLE hO₂).op).hom e₂
  simp only [map_sub, map_map_apply] at f₁ f₂
  have c := hz (i, j) (k, j) (k, l)
    (O := prodCover p₁ p₂ U V (i, j) ⊓ prodCover p₁ p₂ U V (k, l))
    (hO₁.trans (hHle (i, k) j)) (hO₂.trans (hVle k (j, l))) le_rfl
  rw [map_self_apply] at c
  linear_combination -c - f₁ - f₂

end Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
