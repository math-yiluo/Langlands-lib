import Langlands.AlgebraicGeometry.CechPrimitive
import Langlands.AlgebraicGeometry.CechKunnethStatement
import Langlands.AlgebraicGeometry.Modules.CechTheta
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Products of independent degree-one classes and the bound for `H¹`

Let `k` be a field and `X` a scheme over `Spec k` with all global functions constant, with a
multiplication `m : X ×_k X ⟶ X` having a `k`-point `e` as two-sided unit. Let `U` be a finite
cover of `X` by affine opens all of whose finite intersections are affine. Assuming the Čech
Künneth detection statement `Cech.KunnethDetectionStatement`, the Čech product of `n + 1`
cocycles representing linearly independent classes of `H¹(X, 𝒪_X)` is not a Čech coboundary
(`not_exists_prod_eq_d`). If moreover the Čech complex of `𝒪_X` for `U` is exact in degree
`g + 1`, then `H¹(X, 𝒪_X)` is finite-dimensional of dimension at most `g` (`finrank_le`).
-/

universe w w₁ w₂ u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.Cohomology.Cech

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Modules

section Affine

variable {X : Scheme.{u}} {ι : Type w} {U : ι → X.Opens}

/-- If finite intersections of affine opens are affine, so are all `inter U σ`. -/
lemma isAffineOpen_inter
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
    (hU : ∀ i, IsAffineOpen (U i)) : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), IsAffineOpen (inter U σ)
  | 0, σ => by
    rw [inter_one]
    exact hU _
  | n + 1, σ => by
    have e : inter U σ = U (σ 0) ⊓ inter U (fun i => σ i.succ) := by
      refine le_antisymm (le_inf (inter_le_apply σ 0)
        (le_iInf fun i => inter_le_apply σ i.succ)) (le_iInf fun a => ?_)
      refine Fin.cases inf_le_left (fun i => inf_le_right.trans (inter_le_apply _ i)) a
    rw [e]
    exact hinf _ _ (hU _) (isAffineOpen_inter hinf hU n _)

variable {Y P : Scheme.{u}} {R : CommRingCat.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {κ : Type w} {V : κ → Y.Opens}

lemma inter_prodCover {n : ℕ} (τ : Fin n → ι × κ) :
    inter (prodCover p₁ p₂ U V) τ =
      prodOpen p₁ p₂ (inter U (Prod.fst ∘ τ)) (inter V (Prod.snd ∘ τ)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_inter] at hx
    refine ⟨?_, ?_⟩
    · show p₁ x ∈ inter U (Prod.fst ∘ τ)
      rw [mem_inter]
      exact fun a => (hx a).1
    · show p₂ x ∈ inter V (Prod.snd ∘ τ)
      rw [mem_inter]
      exact fun a => (hx a).2
  · intro x hx
    rw [mem_inter]
    intro a
    obtain ⟨h₁, h₂⟩ := hx
    have h₁' : p₁ x ∈ inter U (Prod.fst ∘ τ) := h₁
    have h₂' : p₂ x ∈ inter V (Prod.snd ∘ τ) := h₂
    rw [mem_inter] at h₁' h₂'
    exact ⟨h₁' a, h₂' a⟩

lemma isAffineOpen_inter_prodCover (hP : IsPullback p₁ p₂ πX πY)
    (hU : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), IsAffineOpen (inter U σ))
    (hV : ∀ (n : ℕ) (σ : Fin (n + 1) → κ), IsAffineOpen (inter V σ)) (n : ℕ)
    (τ : Fin (n + 1) → ι × κ) : IsAffineOpen (inter (prodCover p₁ p₂ U V) τ) := by
  rw [inter_prodCover]
  exact isAffineOpen_prodOpen hP (hU n _) (hV n _)

end Affine

section Bound

variable {k : Type u} [Field k] {X P : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of k)}
  [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} k)]

/-- The `k`-linear functional on `1`-cochains extending `μ ∘ Θ`: it kills coboundaries and takes
the value `μ x` on every cocycle representing `x`. -/
lemma exists_functional {ι : Type w} [Finite ι] (U : ι → X.Opens) (hcov : ⊤ ≤ iSup U)
    (μ : (DerivedSections.relativeCohomology πX 1).obj (SheafOfModules.unit X.ringCatSheaf) →ₗ[k]
      k) :
    let _ : ∀ W : X.Opens, Algebra k Γ(X, W) := fun W ↦ (secHom πX W).hom.toAlgebra
    ∃ l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[k] k,
      (∀ y : C (ab X.presheaf) U 0, l (d (ab X.presheaf) U 0 y) = 0) ∧
      ∀ (z : C (ab X.presheaf) U 1) x, d (ab X.presheaf) U 1 z = 0 →
        CechTheta.Rep πX (SheafOfModules.unit X.ringCatSheaf) U z x → l z = μ x := by
  intro _
  have hsmul : ∀ (c : k) (z : ∀ σ : Fin 2 → ι, Γ(X, inter U σ)),
      c • z = CechTheta.smulC πX U c (N := SheafOfModules.unit X.ringCatSheaf) (p := 1) z :=
    fun c z => funext fun σ => rfl
  let Z : Submodule k (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) :=
    { carrier := {z | d (ab X.presheaf) U 1 z = 0}
      add_mem' := fun {a b} ha hb => by
        change d (ab X.presheaf) U 1 (a + b) = 0
        rw [map_add, show d (ab X.presheaf) U 1 a = 0 from ha,
          show d (ab X.presheaf) U 1 b = 0 from hb, add_zero]
      zero_mem' := map_zero _
      smul_mem' := fun c z hz => by
        change d (ab X.presheaf) U 1 (c • z) = 0
        have h0 : d (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)) U 1 z = 0 :=
          hz
        rw [hsmul]
        exact (CechTheta.d_smulC (N := SheafOfModules.unit X.ringCatSheaf) (V := U) πX c 1 z).trans
          ((congrArg (CechTheta.smulC πX U c) h0).trans (CechTheta.smulC_zero πX c)) }
  have hrep : ∀ z : Z, ∃ x, CechTheta.Rep πX (SheafOfModules.unit X.ringCatSheaf) U z.1 x :=
    fun z => CechTheta.exists_rep hcov z.2
  let Θ : Z →ₗ[k] (DerivedSections.relativeCohomology πX 1).obj
      (SheafOfModules.unit X.ringCatSheaf) :=
    { toFun := fun z => Classical.choose (hrep z)
      map_add' := fun z z' => CechTheta.rep_unique hcov (Classical.choose_spec (hrep (z + z')))
        (CechTheta.rep_add (Classical.choose_spec (hrep z)) (Classical.choose_spec (hrep z')))
      map_smul' := fun c z => by
        refine CechTheta.rep_unique hcov (Classical.choose_spec (hrep (c • z))) ?_
        have h := CechTheta.rep_smul c (Classical.choose_spec (hrep z))
        rw [← hsmul] at h
        exact h }
  have hΘ : ∀ (z : Z) x, CechTheta.Rep πX (SheafOfModules.unit X.ringCatSheaf) U z.1 x →
      Θ z = x := fun z x h => CechTheta.rep_unique hcov (Classical.choose_spec (hrep z)) h
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (μ ∘ₗ Θ)
  have hlZ : ∀ z : Z, l z = μ (Θ z) := fun z => congrArg (fun F => F z) hl
  refine ⟨l, fun y => ?_, fun z x hz h => ?_⟩
  · have hdy : d (ab X.presheaf) U 1 (d (ab X.presheaf) U 0 y) = 0 := d_d _ _ 0 y
    rw [hlZ ⟨d (ab X.presheaf) U 0 y, hdy⟩, hΘ _ 0 (CechTheta.rep_d (f := πX)
      (M := SheafOfModules.unit X.ringCatSheaf) (V := U) y), map_zero]
  · rw [hlZ ⟨z, hz⟩, hΘ _ x h]

omit [HasDerivedCategory.{w₂} (ModuleCat.{u} k)] in
/-- A coordinate functional for the first member of a linearly independent family. -/
lemma exists_dual {M : Type*} [AddCommGroup M] [Module k M] {n : ℕ} (x : Fin (n + 1) → M)
    (hx : LinearIndependent k x) :
    ∃ μ : M →ₗ[k] k, μ (x 0) = 1 ∧ ∀ r : Fin n, μ (x r.succ) = 0 := by
  let b := Module.Basis.span hx
  obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (b.coord 0)
  have h : ∀ r, μ (x r) = b.coord 0 (b r) := fun r => by
    rw [← hμ, LinearMap.comp_apply, Module.Basis.span_apply]
    rfl
  refine ⟨μ, ?_, fun r => ?_⟩
  · rw [h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  · rw [h, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [Fin.succ_ne_zero]

end Bound

section Main

variable {k : Type u} [Field k] {X P : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of k)}
  [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} k)]
  {p₁ p₂ : P ⟶ X}

/-- The Čech product of `N + 1` cocycles representing linearly independent classes of
`H¹(X, 𝒪_X)` is not a Čech coboundary. -/
theorem not_exists_prod_eq_d (hK : KunnethDetectionStatement.{w, w, u})
    (hP : IsPullback p₁ p₂ πX πX) (hglob : Function.Surjective (secHom πX ⊤).hom)
    (m : P ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ πX = 𝟙 _)
    (i₁ : X ⟶ P) (h₁₁ : i₁ ≫ p₁ = 𝟙 X) (h₁₂ : i₁ ≫ p₂ = πX ≫ e) (hm₁ : i₁ ≫ m = 𝟙 X)
    (i₂ : X ⟶ P) (h₂₁ : i₂ ≫ p₁ = πX ≫ e) (h₂₂ : i₂ ≫ p₂ = 𝟙 X) (hm₂ : i₂ ≫ m = 𝟙 X)
    {ι : Type w} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), IsAffineOpen (inter U σ)) (hcov : ⊤ ≤ iSup U) :
    ∀ (N : ℕ) (x : Fin (N + 1) →
        (DerivedSections.relativeCohomology πX 1).obj (SheafOfModules.unit X.ringCatSheaf))
      (z : Fin (N + 1) → C (ab X.presheaf) U 1), LinearIndependent k x →
      (∀ r, d (ab X.presheaf) U 1 (z r) = 0) →
      (∀ r, CechTheta.Rep πX (SheafOfModules.unit X.ringCatSheaf) U (z r) (x r)) →
      ¬ ∃ c, prod X.presheaf U (N + 1) z = d (ab X.presheaf) U N c := by
  have hR : IsField (CommRingCat.of k) := Field.toIsField k
  have hU1 : ∀ i, IsAffineOpen (U i) := fun i => by
    have h := hU 0 (fun _ => i)
    rwa [inter_const_one] at h
  have hUU : ∀ i j, IsAffineOpen (U i ⊓ U j) := fun i j => by
    have h := hU 1 ![i, j]
    rwa [inter_two] at h
  have hM : AffineVanishing.IsCechAcyclic (SheafOfModules.unit P.ringCatSheaf) :=
    @AffineVanishing.isCechAcyclic_of_isQuasicoherent _ _
      (CechDegreeOne.isQuasicoherent_unit P)
  have hβ : ∀ j, primCover p₁ p₂ m U j ≤ prodCover p₁ p₂ U U j.1 := fun _ => inf_le_left
  intro N
  induction N with
  | zero =>
    rintro x z hx hz hrep ⟨c, hc⟩
    have hc' : z 0 = d (ab X.presheaf) U 0 c := (prod_one z).symm.trans hc
    have h0 : CechTheta.Rep πX (SheafOfModules.unit X.ringCatSheaf) U
        (d (ab X.presheaf) U 0 c) (x 0) := hc' ▸ hrep 0
    exact hx.ne_zero 0 (CechTheta.rep_eq_zero_of_d (M := SheafOfModules.unit X.ringCatSheaf)
      (y := c) hcov h0)
  | succ N ih =>
    rintro x z hx hz hrep ⟨c, hc⟩
    let _ : ∀ W : X.Opens, Algebra k Γ(X, W) := fun W ↦ (secHom πX W).hom.toAlgebra
    obtain ⟨μ, hμ0, hμs⟩ := exists_dual x hx
    obtain ⟨l, hl, hlz⟩ := exists_functional U hcov μ
    have hl0 : l (z 0) = 1 := by rw [hlz (z 0) (x 0) (hz 0) (hrep 0), hμ0]
    have hls : ∀ r : Fin (N + 1), l (z r.succ) = 0 := fun r => by
      rw [hlz _ _ (hz _) (hrep _), hμs]
    choose g hg using fun r => exists_pull_sub_refine_eq_d hR hP hglob m e he i₁ h₁₁ h₁₂ hm₁
      i₂ h₂₁ h₂₂ hm₂ U hU1 hUU hcov (hz r)
    let s : Fin (N + 1 + 1) → C (ab P.presheaf) (prodCover p₁ p₂ U U) 1 := fun r =>
      pull p₁ U (prodCover p₁ p₂ U U) Prod.fst (fun _ => inf_le_left) 1 (z r) +
        pull p₂ U (prodCover p₁ p₂ U U) Prod.snd (fun _ => inf_le_right) 1 (z r)
    have hs : ∀ r, d (ab P.presheaf) (prodCover p₁ p₂ U U) 1 (s r) = 0 := fun r => by
      simp only [s, map_add, d_pull, hz r, map_zero, add_zero]
    obtain ⟨c'', hc''⟩ := prod_sub_eq_d (R := P.presheaf) (U := primCover p₁ p₂ m U) (N + 1)
      (fun r => pull m U (primCover p₁ p₂ m U) Prod.snd (fun _ => inf_le_right) 1 (z r))
      (fun r => refine (ab P.presheaf) (prodCover p₁ p₂ U U) (primCover p₁ p₂ m U) Prod.fst hβ 1
        (s r))
      (fun r => by rw [d_pull, hz r, map_zero])
      (fun r => by rw [d_refine, hs r, map_zero])
      (fun r => -g r)
      (fun r => by rw [map_neg, ← hg r, neg_sub])
    have hW : refine (ab P.presheaf) (prodCover p₁ p₂ U U) (primCover p₁ p₂ m U) Prod.fst hβ
        (N + 1 + 1) (prod P.presheaf (prodCover p₁ p₂ U U) (N + 1 + 1) s) =
        d (ab P.presheaf) (primCover p₁ p₂ m U) (N + 1)
          (c'' + pull m U (primCover p₁ p₂ m U) Prod.snd (fun _ => inf_le_right) (N + 1) c) := by
      rw [refine_prod, map_add, d_pull, ← hc, pull_prod, ← hc'', sub_add_cancel]
    obtain ⟨c₀, hc₀⟩ := Langlands.AlgebraicGeometry.Modules.CechShift.exists_d_eq_of_refine
      (V := prodCover p₁ p₂ U U) (W := primCover p₁ p₂ m U) (β := Prod.fst) hβ
      (isAffineOpen_inter_prodCover hP hU hU) (iSup_primCover hcov) (N + 1)
      (SheafOfModules.unit P.ringCatSheaf) hM (prod P.presheaf (prodCover p₁ p₂ U U) (N + 1 + 1) s)
      (prod_cocycle _ s hs) _ hW
    obtain ⟨c', hc'⟩ := hK hP (fun _ => rfl) (fun _ => rfl) U U (hU 1) hU l hl N z z hz hz hl0
      hls c₀ hc₀.symm
    exact ih (Fin.tail x) (Fin.tail z) (hx.comp _ (Fin.succ_injective _)) (fun r => hz _)
      (fun r => hrep _) ⟨c', hc'⟩

/-- If the Čech complex of `𝒪_X` for `U` is exact in degree `g + 1`, then `H¹(X, 𝒪_X)` is
finite-dimensional of dimension at most `g`. -/
theorem finiteDimensional_and_finrank_le (hK : KunnethDetectionStatement.{w, w, u})
    (hP : IsPullback p₁ p₂ πX πX) (hglob : Function.Surjective (secHom πX ⊤).hom)
    (m : P ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ πX = 𝟙 _)
    (i₁ : X ⟶ P) (h₁₁ : i₁ ≫ p₁ = 𝟙 X) (h₁₂ : i₁ ≫ p₂ = πX ≫ e) (hm₁ : i₁ ≫ m = 𝟙 X)
    (i₂ : X ⟶ P) (h₂₁ : i₂ ≫ p₁ = πX ≫ e) (h₂₂ : i₂ ≫ p₂ = 𝟙 X) (hm₂ : i₂ ≫ m = 𝟙 X)
    {ι : Type w} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), IsAffineOpen (inter U σ)) (hcov : ⊤ ≤ iSup U)
    {g : ℕ} (hvan : ExactAt (ab X.presheaf) U g) :
    FiniteDimensional k
        ((DerivedSections.relativeCohomology πX 1).obj (SheafOfModules.unit X.ringCatSheaf)) ∧
      Module.finrank k
        ((DerivedSections.relativeCohomology πX 1).obj (SheafOfModules.unit X.ringCatSheaf)) ≤
        g := by
  have hMX : AffineVanishing.IsCechAcyclic (SheafOfModules.unit X.ringCatSheaf) :=
    @AffineVanishing.isCechAcyclic_of_isQuasicoherent _ _
      (CechDegreeOne.isQuasicoherent_unit X)
  have key : ∀ s : Finset
      ((DerivedSections.relativeCohomology πX 1).obj (SheafOfModules.unit X.ringCatSheaf)),
      LinearIndependent k (fun i : s => (i : ↑((DerivedSections.relativeCohomology πX 1).obj
        (SheafOfModules.unit X.ringCatSheaf)))) → s.card ≤ g := by
    intro s hs
    by_contra hlt
    rw [not_le] at hlt
    let emb : Fin (g + 1) ↪ s := (Fin.castLEEmb hlt).trans s.equivFin.symm.toEmbedding
    let x := fun r : Fin (g + 1) => ((emb r : s) : ↑((DerivedSections.relativeCohomology πX 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    have hx : LinearIndependent k x := hs.comp emb emb.injective
    choose z hz hrep using fun r => CechTheta.exists_cocycle_rep (f := πX)
      (M := SheafOfModules.unit X.ringCatSheaf) (V := U) hMX (hU 0) (x r)
    obtain ⟨c, hc⟩ := hvan (prod X.presheaf U (g + 1) z) (prod_cocycle _ z hz)
    exact not_exists_prod_eq_d hK hP hglob m e he i₁ h₁₁ h₁₂ hm₁ i₂ h₂₁ h₂₂ hm₂ U hU hcov g x z
      hx hz hrep ⟨c, hc.symm⟩
  have hrank := rank_le key
  exact ⟨Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0),
    Module.finrank_le_of_rank_le hrank⟩

end Main

end Langlands.Cohomology.Cech
