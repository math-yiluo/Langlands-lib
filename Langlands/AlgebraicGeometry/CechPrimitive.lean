import Langlands.AlgebraicGeometry.CechPullback
import Langlands.AlgebraicGeometry.Modules.CechShift
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityProof

/-!
# Primitivity of degree-one Čech cocycles for a multiplication with two-sided unit

Let `P` be the fibre product of `πX : X ⟶ Spec R` with itself over a field `R`, with
projections `p₁` and `p₂`, and let `m : P ⟶ X` be a morphism such that the two axes
`i₁ = (id, e)` and `i₂ = (e, id)` through an `R`-point `e` satisfy `i₁ ≫ m = 𝟙` and
`i₂ ≫ m = 𝟙`. Let `U` be a finite cover of `X` by affine opens with affine pairwise
intersections, and assume that all global functions on `X` come from `R`. For a Čech
`1`-cocycle `z` of `𝒪_X` on `U`, the pullback `m^* z` and the sum `p₁^* z + p₂^* z` become
cohomologous on the cover `p₁⁻¹ U a ⊓ p₂⁻¹ U b ⊓ m⁻¹ U c` of `P`
(`exists_pull_sub_refine_eq_d`).

The difference is first moved to a cocycle `w'` on the product cover `p₁⁻¹ U a ⊓ p₂⁻¹ U b`
(degree-one refinement surjectivity). Its pullbacks along both axes are coboundaries because
`m`, `p₁` and `p₂` restrict on each axis to the identity or to a map through the point `e`.
The Library two-axis theorem `FieldTwoAxisH1Injectivity.exists_coboundary_of_axes` then shows
that `w'` is a coboundary.
-/

universe w w' w'' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.Cohomology.Cech

section PullRefine

variable {X Y : Scheme.{u}} {ι : Type w} {ι' : Type w'} {ι'' : Type w''}

lemma pull_congr {f f' : X ⟶ Y} (h : f = f') {U : ι → Y.Opens} {U' : ι' → X.Opens}
    {α : ι' → ι} (hα : ∀ i, U' i ≤ f ⁻¹ᵁ U (α i)) (hα' : ∀ i, U' i ≤ f' ⁻¹ᵁ U (α i)) (p : ℕ)
    (c : C (ab Y.presheaf) U p) : pull f U U' α hα p c = pull f' U U' α hα' p c := by
  subst h
  rfl

variable (f : X ⟶ Y)

lemma refine_pull {U : ι → Y.Opens} {U' : ι' → X.Opens} {U'' : ι'' → X.Opens} {α : ι' → ι}
    (hα : ∀ i, U' i ≤ f ⁻¹ᵁ U (α i)) {δ : ι'' → ι'} (hδ : ∀ j, U'' j ≤ U' (δ j)) (p : ℕ)
    (c : C (ab Y.presheaf) U p) :
    refine (ab X.presheaf) U' U'' δ hδ p (pull f U U' α hα p c) =
      pull f U U'' (α ∘ δ) (fun j => (hδ j).trans (hα (δ j))) p c := by
  funext σ
  rw [refine_apply, pull_apply, res_appLE, pull_apply]
  rfl

lemma pull_refine {U : ι → Y.Opens} {V : ι' → Y.Opens} {U' : ι'' → X.Opens} {β : ι' → ι}
    (hβ : ∀ j, V j ≤ U (β j)) {γ : ι'' → ι'} (hγ : ∀ i, U' i ≤ f ⁻¹ᵁ V (γ i)) (p : ℕ)
    (c : C (ab Y.presheaf) U p) :
    pull f V U' γ hγ p (refine (ab Y.presheaf) U V β hβ p c) =
      pull f U U' (β ∘ γ) (fun i => (hγ i).trans (f.preimage_mono (hβ (γ i)))) p c := by
  funext σ
  rw [pull_apply, refine_apply, appLE_res, pull_apply]
  rfl

/-- Pulling back a `1`-cocycle with a constant index map gives `0`. -/
lemma pull_const_eq_zero {U : ι → Y.Opens} {U' : ι' → X.Opens} {z : C (ab Y.presheaf) U 1}
    (hz : d (ab Y.presheaf) U 1 z = 0) (i₀ : ι) (hα : ∀ i, U' i ≤ f ⁻¹ᵁ U i₀) :
    pull f U U' (fun _ => i₀) hα 1 z = 0 := by
  funext σ
  have h0 : z ((fun _ : ι' => i₀) ∘ σ) = 0 := cocycle_apply_const hz i₀
  rw [pull_apply, h0, map_zero]
  rfl

end PullRefine

section Pair

variable {P : Scheme.{u}} {κ : Type w} {V : κ → P.Opens}

lemma inter_one (σ : Fin 1 → κ) : inter V σ = V (σ 0) :=
  le_antisymm (inter_le_apply σ 0) (le_iInf fun i => by rw [Fin.fin_one_eq_zero i])

/-- The values of a Čech `1`-cochain of `𝒪_P` on the pairwise intersections `V a ⊓ V b`. -/
def pair (w : C (ab P.presheaf) V 1) (a b : κ) : Γ(P, V a ⊓ V b) :=
  res (P := ab P.presheaf) (inter_two a b).ge (w ![a, b])

/-- The cocycle identity of `pair w` for a `1`-cocycle `w`, in the form used by the Library
two-axis theorem. -/
lemma pair_cocycle {w : C (ab P.presheaf) V 1} (hw : d (ab P.presheaf) V 1 w = 0) (a b c : κ)
    {O : P.Opens} (h₁ : O ≤ V a ⊓ V b) (h₂ : O ≤ V b ⊓ V c) (h₃ : O ≤ V a ⊓ V c) :
    (P.presheaf.map (homOfLE h₁).op).hom (pair w a b) +
        (P.presheaf.map (homOfLE h₂).op).hom (pair w b c) =
      (P.presheaf.map (homOfLE h₃).op).hom (pair w a c) := by
  have h := cocycle_add hw a b c (h₁.trans (inter_two a b).ge) (h₂.trans (inter_two b c).ge)
    (h₃.trans (inter_two a c).ge)
  change res (P := ab P.presheaf) h₁ (res _ (w ![a, b])) +
      res (P := ab P.presheaf) h₂ (res _ (w ![b, c])) =
    res (P := ab P.presheaf) h₃ (res _ (w ![a, c]))
  rw [res_res, res_res, res_res]
  exact h

/-- A `1`-cochain whose values on pairs are differences `y b - y a` is a coboundary. -/
lemma exists_d_eq_of_pair {w : C (ab P.presheaf) V 1} (y : ∀ a, Γ(P, V a))
    (hy : ∀ a b, pair w a b = (P.presheaf.map (homOfLE inf_le_right).op).hom (y b) -
      (P.presheaf.map (homOfLE inf_le_left).op).hom (y a)) :
    ∃ y' : C (ab P.presheaf) V 0, d (ab P.presheaf) V 0 y' = w := by
  let y' : C (ab P.presheaf) V 0 := fun σ => res (P := ab P.presheaf) (inter_le_apply σ 0) (y (σ 0))
  refine ⟨y', funext fun τ => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, τ = ![a, b] := ⟨τ 0, τ 1, by funext i; fin_cases i <;> rfl⟩
  have ha : inter V ![a, b] ≤ inter V (fun _ : Fin 1 => a) :=
    (inter_le_apply ![a, b] 0).trans (inter_const_one a).ge
  have hb : inter V ![a, b] ≤ inter V (fun _ : Fin 1 => b) :=
    (inter_le_apply ![a, b] 1).trans (inter_const_one b).ge
  have e := res_d_zero_pair (P := ab P.presheaf) y' a b le_rfl ha hb
  rw [res_self] at e
  have hw : w ![a, b] = res (P := ab P.presheaf) (inter_two a b).le (pair w a b) := by
    rw [pair, res_res, res_self]
  rw [e, hw, hy a b]
  change _ = res (P := ab P.presheaf) _ (res (P := ab P.presheaf) inf_le_right (y b) -
    res (P := ab P.presheaf) inf_le_left (y a))
  rw [map_sub, res_res, res_res, res_res, res_res]

/-- If the pullback of a `1`-cochain `w` along `i` is a coboundary for the cover `i⁻¹ V`, then
`w` satisfies the axis hypothesis of the Library two-axis theorem for `i`. -/
lemma exists_axis_of_d_eq {X : Scheme.{u}} (i : X ⟶ P) {w : C (ab P.presheaf) V 1}
    {y : C (ab X.presheaf) (fun a => i ⁻¹ᵁ V a) 0}
    (hy : d (ab X.presheaf) (fun a => i ⁻¹ᵁ V a) 0 y =
      pull i V (fun a => i ⁻¹ᵁ V a) id (fun _ => le_rfl) 1 w) :
    ∃ g : ∀ a, Γ(X, i ⁻¹ᵁ V a), ∀ a b,
      (i.app (V a ⊓ V b)).hom (pair w a b) =
        (X.presheaf.map (homOfLE (i.preimage_mono inf_le_right)).op).hom (g b) -
          (X.presheaf.map (homOfLE (i.preimage_mono inf_le_left)).op).hom (g a) := by
  refine ⟨fun a => res (P := ab X.presheaf) (inter_const_one a).ge (y (fun _ => a)),
    fun a b => ?_⟩
  have hO : i ⁻¹ᵁ (V a ⊓ V b) ≤ inter (fun a => i ⁻¹ᵁ V a) ![a, b] := by
    rw [inter_two]
    exact le_rfl
  have ha : i ⁻¹ᵁ (V a ⊓ V b) ≤ inter (fun a => i ⁻¹ᵁ V a) (fun _ : Fin 1 => a) :=
    hO.trans ((inter_le_apply (U := fun a => i ⁻¹ᵁ V a) ![a, b] 0).trans
      (inter_const_one (U := fun a => i ⁻¹ᵁ V a) a).ge)
  have hb : i ⁻¹ᵁ (V a ⊓ V b) ≤ inter (fun a => i ⁻¹ᵁ V a) (fun _ : Fin 1 => b) :=
    hO.trans ((inter_le_apply (U := fun a => i ⁻¹ᵁ V a) ![a, b] 1).trans
      (inter_const_one (U := fun a => i ⁻¹ᵁ V a) b).ge)
  have e := res_d_zero_pair (P := ab X.presheaf) y a b hO ha hb
  rw [hy, pull_apply, res_appLE] at e
  rw [Scheme.Hom.app_eq_appLE, pair, appLE_res]
  refine e.trans ?_
  change _ = res (P := ab X.presheaf) _ (res (P := ab X.presheaf) _ (y (fun _ => b))) -
    res (P := ab X.presheaf) _ (res (P := ab X.presheaf) _ (y (fun _ => a)))
  rw [res_res, res_res]

end Pair

section Primitive

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {X P : Scheme.{u}} {πX : X ⟶ Spec R}

/-- On an axis `i` with `i ≫ m = 𝟙`, `i ≫ q = 𝟙` and `i ≫ q'` factoring through a point, the
pullback of `m^* z - (q^* z + q'^* z)` is a coboundary. -/
lemma exists_pull_axis_eq_d {e : Spec R ⟶ X} (i : X ⟶ P) {m q q' : P ⟶ X} (hm : i ≫ m = 𝟙 X)
    (hq : i ≫ q = 𝟙 X) (hq' : i ≫ q' = πX ≫ e) {ι : Type w} {U : ι → X.Opens} {i₀ : ι}
    (hi₀ : ⊤ ≤ e ⁻¹ᵁ U i₀) {κ : Type w'} {W : κ → P.Opens} {c a a' : κ → ι}
    (hc : ∀ j, W j ≤ m ⁻¹ᵁ U (c j)) (ha : ∀ j, W j ≤ q ⁻¹ᵁ U (a j))
    (ha' : ∀ j, W j ≤ q' ⁻¹ᵁ U (a' j)) {z : C (ab X.presheaf) U 1}
    (hz : d (ab X.presheaf) U 1 z = 0) :
    ∃ y : C (ab X.presheaf) (fun j => i ⁻¹ᵁ W j) 0,
      pull i W (fun j => i ⁻¹ᵁ W j) id (fun _ => le_rfl) 1
          (pull m U W c hc 1 z - (pull q U W a ha 1 z + pull q' U W a' ha' 1 z)) =
        d (ab X.presheaf) (fun j => i ⁻¹ᵁ W j) 0 y := by
  have hc' : ∀ j, i ⁻¹ᵁ W j ≤ (𝟙 X) ⁻¹ᵁ U (c j) := fun j => by
    rw [← hm]
    exact i.preimage_mono (hc j)
  have ha₁ : ∀ j, i ⁻¹ᵁ W j ≤ (𝟙 X) ⁻¹ᵁ U (a j) := fun j => by
    rw [← hq]
    exact i.preimage_mono (ha j)
  have ha₂ : ∀ j, i ⁻¹ᵁ W j ≤ (πX ≫ e) ⁻¹ᵁ U (a' j) := fun j => by
    rw [← hq']
    exact i.preimage_mono (ha' j)
  have h₀ : ∀ j, i ⁻¹ᵁ W j ≤ (πX ≫ e) ⁻¹ᵁ U i₀ := fun j x _ => hi₀ (show πX x ∈ ⊤ from trivial)
  have e₁ : pull i W (fun j => i ⁻¹ᵁ W j) id (fun _ => le_rfl) 1 (pull m U W c hc 1 z) =
      pull (𝟙 X) U (fun j => i ⁻¹ᵁ W j) c hc' 1 z := by
    rw [pull_comp]
    exact pull_congr hm _ hc' 1 z
  have e₂ : pull i W (fun j => i ⁻¹ᵁ W j) id (fun _ => le_rfl) 1 (pull q U W a ha 1 z) =
      pull (𝟙 X) U (fun j => i ⁻¹ᵁ W j) a ha₁ 1 z := by
    rw [pull_comp]
    exact pull_congr hq _ ha₁ 1 z
  have e₃ : pull i W (fun j => i ⁻¹ᵁ W j) id (fun _ => le_rfl) 1 (pull q' U W a' ha' 1 z) =
      pull (πX ≫ e) U (fun j => i ⁻¹ᵁ W j) a' ha₂ 1 z := by
    rw [pull_comp]
    exact pull_congr hq' _ ha₂ 1 z
  refine ⟨indexChange (𝟙 X) U _ hc' ha₁ z - indexChange (πX ≫ e) U _ ha₂ h₀ z, ?_⟩
  rw [map_sub, map_add, e₁, e₂, e₃, map_sub, ← pull_sub_pull_eq_d (𝟙 X) hc' ha₁ hz,
    ← pull_sub_pull_eq_d (πX ≫ e) ha₂ h₀ hz, pull_const_eq_zero (πX ≫ e) hz i₀ h₀]
  abel

variable {p₁ p₂ : P ⟶ X}

variable (p₁ p₂) in
/-- The cover of `P` by the opens `p₁⁻¹ U a ⊓ p₂⁻¹ U b ⊓ m⁻¹ U c`. -/
abbrev primCover (m : P ⟶ X) {ι : Type w} (U : ι → X.Opens) (j : (ι × ι) × ι) : P.Opens :=
  prodCover p₁ p₂ U U j.1 ⊓ m ⁻¹ᵁ U j.2

lemma iSup_primCover {m : P ⟶ X} {ι : Type w} {U : ι → X.Opens} (hcov : ⊤ ≤ iSup U) :
    ⊤ ≤ iSup (primCover p₁ p₂ m U) := by
  intro x _
  obtain ⟨ab, hab⟩ := Opens.mem_iSup.1
    (iSup_prodOpen_eq_top (p₁ := p₁) (p₂ := p₂) hcov hcov (Set.mem_univ x))
  obtain ⟨c, hc⟩ := Opens.mem_iSup.1 (hcov (Set.mem_univ (m x)))
  exact Opens.mem_iSup.2 ⟨(ab, c), hab, hc⟩

/-- Primitivity of degree-one Čech cocycles: over a field, if `m : X ×_R X ⟶ X` has the
`R`-point `e` as a two-sided unit, then for a `1`-cocycle `z` on a finite cover by affine opens
with affine pairwise intersections, `m^* z - (p₁^* z + p₂^* z)` is a coboundary on the cover
`p₁⁻¹ U a ⊓ p₂⁻¹ U b ⊓ m⁻¹ U c`. -/
theorem exists_pull_sub_refine_eq_d (hR : IsField R) (hP : IsPullback p₁ p₂ πX πX)
    (hglob : Function.Surjective (secHom πX ⊤).hom) (m : P ⟶ X) (e : Spec R ⟶ X)
    (he : e ≫ πX = 𝟙 _) (i₁ : X ⟶ P) (h₁₁ : i₁ ≫ p₁ = 𝟙 X) (h₁₂ : i₁ ≫ p₂ = πX ≫ e)
    (hm₁ : i₁ ≫ m = 𝟙 X) (i₂ : X ⟶ P) (h₂₁ : i₂ ≫ p₁ = πX ≫ e) (h₂₂ : i₂ ≫ p₂ = 𝟙 X)
    (hm₂ : i₂ ≫ m = 𝟙 X) {ι : Type w} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUU : ∀ i k, IsAffineOpen (U i ⊓ U k))
    (hcov : ⊤ ≤ iSup U) {z : C (ab X.presheaf) U 1} (hz : d (ab X.presheaf) U 1 z = 0) :
    ∃ g : C (ab P.presheaf) (primCover p₁ p₂ m U) 0,
      pull m U (primCover p₁ p₂ m U) Prod.snd (fun _ => inf_le_right) 1 z -
          refine (ab P.presheaf) (prodCover p₁ p₂ U U) (primCover p₁ p₂ m U) Prod.fst
            (fun _ => inf_le_left) 1
            (pull p₁ U (prodCover p₁ p₂ U U) Prod.fst (fun _ => inf_le_left) 1 z +
              pull p₂ U (prodCover p₁ p₂ U U) Prod.snd (fun _ => inf_le_right) 1 z) =
        d (ab P.presheaf) (primCover p₁ p₂ m U) 0 g := by
  classical
  let _ : ∀ W : X.Opens, Algebra R Γ(X, W) := fun W ↦ (secHom πX W).hom.toAlgebra
  have hβ : ∀ j, primCover p₁ p₂ m U j ≤ prodCover p₁ p₂ U U j.1 := fun _ => inf_le_left
  have hWcov : ⊤ ≤ iSup (primCover p₁ p₂ m U) := iSup_primCover hcov
  -- The difference cocycle on the fine cover, written with pullbacks only.
  have hsum : refine (ab P.presheaf) (prodCover p₁ p₂ U U) (primCover p₁ p₂ m U) Prod.fst hβ 1
      (pull p₁ U (prodCover p₁ p₂ U U) Prod.fst (fun _ => inf_le_left) 1 z +
        pull p₂ U (prodCover p₁ p₂ U U) Prod.snd (fun _ => inf_le_right) 1 z) =
      pull p₁ U (primCover p₁ p₂ m U) (Prod.fst ∘ Prod.fst)
          (fun j => (hβ j).trans inf_le_left) 1 z +
        pull p₂ U (primCover p₁ p₂ m U) (Prod.snd ∘ Prod.fst)
          (fun j => (hβ j).trans inf_le_right) 1 z := by
    rw [map_add, refine_pull, refine_pull]
  set w := pull m U (primCover p₁ p₂ m U) Prod.snd (fun _ => inf_le_right) 1 z -
    refine (ab P.presheaf) (prodCover p₁ p₂ U U) (primCover p₁ p₂ m U) Prod.fst hβ 1
      (pull p₁ U (prodCover p₁ p₂ U U) Prod.fst (fun _ => inf_le_left) 1 z +
        pull p₂ U (prodCover p₁ p₂ U U) Prod.snd (fun _ => inf_le_right) 1 z) with hwdef
  have hw : d (ab P.presheaf) (primCover p₁ p₂ m U) 1 w = 0 := by
    simp only [hwdef, map_sub, map_add, d_pull, d_refine, hz, map_zero, add_zero, sub_zero]
  -- Move the difference to the product cover.
  have hM : Langlands.AlgebraicGeometry.Modules.AffineVanishing.IsCechAcyclic
      (SheafOfModules.unit P.ringCatSheaf) :=
    @Langlands.AlgebraicGeometry.Modules.AffineVanishing.isCechAcyclic_of_isQuasicoherent _ _
      (Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit P)
  have hV1 : ∀ σ : Fin 1 → ι × ι, IsAffineOpen (inter (prodCover p₁ p₂ U U) σ) := fun σ => by
    rw [inter_one]
    exact isAffineOpen_prodOpen hP (hU _) (hU _)
  obtain ⟨w', hw'', g, hg'⟩ : ∃ w' : C (ab P.presheaf) (prodCover p₁ p₂ U U) 1,
      d (ab P.presheaf) (prodCover p₁ p₂ U U) 1 w' = 0 ∧
        ∃ g : C (ab P.presheaf) (primCover p₁ p₂ m U) 0,
          refine (ab P.presheaf) (prodCover p₁ p₂ U U) (primCover p₁ p₂ m U) Prod.fst hβ 1 w' -
            w = d (ab P.presheaf) (primCover p₁ p₂ m U) 0 g :=
    Langlands.AlgebraicGeometry.Modules.CechShift.exists_refine_sub_eq_d
      (M := SheafOfModules.unit P.ringCatSheaf) hβ hM hV1 hWcov (w := w) hw
  obtain ⟨i₀, hi₀⟩ := exists_top_le_preimage hR e hcov
  -- The axis conditions.
  have axis : ∀ (i : X ⟶ P), i ≫ m = 𝟙 X →
      (∃ y : C (ab X.presheaf) (fun j => i ⁻¹ᵁ primCover p₁ p₂ m U j) 0,
        pull i (primCover p₁ p₂ m U) (fun j => i ⁻¹ᵁ primCover p₁ p₂ m U j) id
          (fun _ => le_rfl) 1 w = d (ab X.presheaf) _ 0 y) →
      ∃ y : C (ab X.presheaf) (fun a => i ⁻¹ᵁ prodCover p₁ p₂ U U a) 0,
        d (ab X.presheaf) (fun a => i ⁻¹ᵁ prodCover p₁ p₂ U U a) 0 y =
          pull i (prodCover p₁ p₂ U U) (fun a => i ⁻¹ᵁ prodCover p₁ p₂ U U a) id
            (fun _ => le_rfl) 1 w' := by
    intro i _ ⟨y, hy⟩
    have hiβ : ∀ j, i ⁻¹ᵁ primCover p₁ p₂ m U j ≤ i ⁻¹ᵁ prodCover p₁ p₂ U U j.1 :=
      fun j => i.preimage_mono (hβ j)
    have hicov : ⊤ ≤ iSup (fun j => i ⁻¹ᵁ primCover p₁ p₂ m U j) := by
      intro x _
      obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hWcov (Set.mem_univ (i x)))
      exact Opens.mem_iSup.2 ⟨j, hj⟩
    have hcz : d (ab X.presheaf) (fun a => i ⁻¹ᵁ prodCover p₁ p₂ U U a) 1
        (pull i (prodCover p₁ p₂ U U) (fun a => i ⁻¹ᵁ prodCover p₁ p₂ U U a) id
          (fun _ => le_rfl) 1 w') = 0 := by
      rw [d_pull, hw'', map_zero]
    refine Cech.exists_d_eq_of_refine_eq_d
      ((Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic.toAbSheaf X).obj
        (SheafOfModules.unit X.ringCatSheaf)) (U := fun a => i ⁻¹ᵁ prodCover p₁ p₂ U U a)
      (U' := fun j => i ⁻¹ᵁ primCover p₁ p₂ m U j) (β := Prod.fst)
      hiβ hicov hcz
      (c := pull i (primCover p₁ p₂ m U) (fun j => i ⁻¹ᵁ primCover p₁ p₂ m U j) id
        (fun _ => le_rfl) 0 g + y) ?_
    have e₁ := congrArg (pull i (primCover p₁ p₂ m U) (fun j => i ⁻¹ᵁ primCover p₁ p₂ m U j) id
      (fun _ => le_rfl) 1) (sub_eq_iff_eq_add.1 hg')
    rw [pull_refine, map_add, hy, ← d_pull] at e₁
    change refine (ab X.presheaf) _ _ Prod.fst hiβ 1 (pull i (prodCover p₁ p₂ U U) _ id _ 1 w') =
      d (ab X.presheaf) _ 0 _
    rw [refine_pull, map_add]
    exact e₁
  have hz₁ := axis i₁ hm₁ (by
    obtain ⟨y, hy⟩ := exists_pull_axis_eq_d (W := primCover p₁ p₂ m U) i₁ hm₁ h₁₁ h₁₂ hi₀
      (c := Prod.snd) (a := Prod.fst ∘ Prod.fst) (a' := Prod.snd ∘ Prod.fst)
      (fun _ => inf_le_right) (fun j => (hβ j).trans inf_le_left)
      (fun j => (hβ j).trans inf_le_right) hz
    exact ⟨y, by rw [hwdef, hsum]; exact hy⟩)
  have hz₂ := axis i₂ hm₂ (by
    obtain ⟨y, hy⟩ := exists_pull_axis_eq_d (W := primCover p₁ p₂ m U) i₂ hm₂ h₂₂ h₂₁ hi₀
      (c := Prod.snd) (a := Prod.snd ∘ Prod.fst) (a' := Prod.fst ∘ Prod.fst)
      (fun _ => inf_le_right) (fun j => (hβ j).trans inf_le_right)
      (fun j => (hβ j).trans inf_le_left) hz
    have hsum' : pull p₁ U (primCover p₁ p₂ m U) (Prod.fst ∘ Prod.fst)
          (fun j => (hβ j).trans inf_le_left) 1 z +
        pull p₂ U (primCover p₁ p₂ m U) (Prod.snd ∘ Prod.fst)
          (fun j => (hβ j).trans inf_le_right) 1 z =
        pull p₂ U (primCover p₁ p₂ m U) (Prod.snd ∘ Prod.fst)
          (fun j => (hβ j).trans inf_le_right) 1 z +
        pull p₁ U (primCover p₁ p₂ m U) (Prod.fst ∘ Prod.fst)
          (fun j => (hβ j).trans inf_le_left) 1 z := add_comm _ _
    exact ⟨y, by rw [hwdef, hsum, hsum']; exact hy⟩)
  obtain ⟨y₁, hy₁⟩ := hz₁
  obtain ⟨y₂, hy₂⟩ := hz₂
  obtain ⟨y, hy⟩ := exists_coboundary_of_axes (fun _ ↦ rfl) (fun _ ↦ rfl) hR hP U U hU hUU hU hUU
    hcov hcov hglob hglob e he i₀ hi₀ e he i₀ hi₀ i₁ h₁₁ h₁₂ i₂ h₂₁ h₂₂ (pair w')
    (fun a b c O h₁ h₂ h₃ => pair_cocycle hw'' a b c h₁ h₂ h₃) (exists_axis_of_d_eq i₁ hy₁)
    (exists_axis_of_d_eq i₂ hy₂)
  obtain ⟨y', hy'⟩ := exists_d_eq_of_pair y hy
  refine ⟨refine (ab P.presheaf) (prodCover p₁ p₂ U U) (primCover p₁ p₂ m U) Prod.fst hβ 0 y' - g,
    ?_⟩
  rw [map_sub, d_refine, hy', ← hg', sub_sub_cancel]

end Primitive

end Langlands.Cohomology.Cech
