import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqMixedSlant

/-! # Degree-two normalization and slant of axis pullbacks -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.Cohomology.Cech

section Normalization

variable {T : TopCat.{u}} {P : TopCat.Presheaf AddCommGrpCat.{v} T} {ι : Type w}
  {U : ι → Opens T}

/-- The repeated first edge of a two-cocycle is its constant first-vertex face. -/
lemma twoCocycle_face_left (e : C P U 2) (he : d P U 2 e = 0) (σ : Fin 2 → ι) :
    face e σ ![0, 0, 1] = face e σ (fun _ => 0) := by
  have h := face_d 2 e σ (![0, 0, 0, 1] : Fin 4 → Fin 2)
  have hc : ∀ k : Fin 4, (![0, 0, 0, 1] : Fin 4 → Fin 2) ∘ k.succAbove =
      if k = 3 then (fun _ => 0) else ![0, 0, 1] := by
    intro k
    fin_cases k <;> funext a <;> fin_cases a <;> rfl
  rw [he, face_zero] at h
  simp only [hc, Fin.sum_univ_succ] at h
  norm_num at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h.symm)

/-- The repeated last edge of a two-cocycle is its constant last-vertex face. -/
lemma twoCocycle_face_right (e : C P U 2) (he : d P U 2 e = 0) (σ : Fin 2 → ι) :
    face e σ ![0, 1, 1] = face e σ (fun _ => 1) := by
  have h := face_d 2 e σ (![0, 1, 1, 1] : Fin 4 → Fin 2)
  have hc : ∀ k : Fin 4, (![0, 1, 1, 1] : Fin 4 → Fin 2) ∘ k.succAbove =
      if k = 0 then (fun _ => 1) else ![0, 1, 1] := by
    intro k
    fin_cases k <;> funext a <;> fin_cases a <;> rfl
  rw [he, face_zero] at h
  simp only [hc, Fin.sum_univ_succ] at h
  norm_num at h
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h.symm)).symm

/-- A one-cochain removing the degenerate faces of a two-cocycle. -/
def twoCorrection (e : C P U 2) : C P U 1 := fun σ => face e σ (fun _ => 0)

lemma face_twoCorrection {n : ℕ} (e : C P U 2) (τ : Fin n → ι) (θ : Fin 2 → Fin n) :
    face (twoCorrection e) τ θ = face e τ (fun _ => θ 0) := by
  exact res_face e τ θ (fun _ => 0)

/-- The cohomologous two-cochain with adjacent repeated indices removed. -/
def normalizeTwo (e : C P U 2) : C P U 2 := e - d P U 1 (twoCorrection e)

lemma normalizeTwo_closed (e : C P U 2) (he : d P U 2 e = 0) :
    d P U 2 (normalizeTwo e) = 0 := by
  rw [normalizeTwo, map_sub, he, d_d, sub_self]

lemma normalizeTwo_face_left (e : C P U 2) (he : d P U 2 e = 0) (σ : Fin 2 → ι) :
    face (normalizeTwo e) σ ![0, 0, 1] = 0 := by
  rw [normalizeTwo, face_sub, twoCocycle_face_left e he, face_d, Fin.sum_univ_three]
  simp only [face_twoCorrection]
  have h₀ : ((![0, 0, 1] : Fin 3 → Fin 2) ∘ (0 : Fin 3).succAbove) 0 = 0 := rfl
  have h₁ : ((![0, 0, 1] : Fin 3 → Fin 2) ∘ (1 : Fin 3).succAbove) 0 = 0 := rfl
  have h₂ : ((![0, 0, 1] : Fin 3 → Fin 2) ∘ (2 : Fin 3).succAbove) 0 = 0 := rfl
  simp only [h₀, h₁, h₂, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    neg_one_sq, one_smul, neg_smul]
  abel

lemma normalizeTwo_face_right (e : C P U 2) (he : d P U 2 e = 0) (σ : Fin 2 → ι) :
    face (normalizeTwo e) σ ![0, 1, 1] = 0 := by
  rw [normalizeTwo, face_sub, twoCocycle_face_right e he, face_d, Fin.sum_univ_three]
  simp only [face_twoCorrection]
  have h₀ : ((![0, 1, 1] : Fin 3 → Fin 2) ∘ (0 : Fin 3).succAbove) 0 = 1 := rfl
  have h₁ : ((![0, 1, 1] : Fin 3 → Fin 2) ∘ (1 : Fin 3).succAbove) 0 = 0 := rfl
  have h₂ : ((![0, 1, 1] : Fin 3 → Fin 2) ∘ (2 : Fin 3).succAbove) 0 = 0 := rfl
  simp only [h₀, h₁, h₂, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    neg_one_sq, one_smul, neg_smul]
  abel

end Normalization

end Langlands.Cohomology.Cech


namespace Langlands.Cohomology.Cech.KunnethDetection

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] {κ : Type v} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

/-- An axis pullback whose first-factor face is zero has zero shuffle evaluation. -/
lemma ev_pull_left_zero {m r : ℕ} (e : C (ab X.presheaf) U m)
    (b : Fin (r + 1) → κ) (ε : Fin (m + 1) → Fin 2) (β : Fin (m + 1) → Fin (r + 1))
    (he : ∀ σ : Fin 2 → ι, face e σ ε = 0) :
    ev hP halgX halgY U V hU hV l
      (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) m e) b ε β = 0 := by
  rw [ev]
  trans slant hP halgX halgY U hU l (inter V b) (hV r b) 0
  · congr 1
    funext σ
    have hf : res (P := ab P.presheaf) (le_inter_prodCover U V σ b ε β)
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) m e
          (fun j => (σ (ε j), b (β j)))) =
        (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) (inter V b)) inf_le_left).hom
          (face e σ ε) := by
      rw [pull_apply, res_appLE, face, appLE_res]
      rfl
    rw [hf, he, map_zero]
    rfl
  · exact map_zero _

/-- An axis pullback whose second-factor face is zero has zero shuffle evaluation. -/
lemma ev_pull_right_zero {m r : ℕ} (e : C (ab Y.presheaf) V m)
    (b : Fin (r + 1) → κ) (ε : Fin (m + 1) → Fin 2) (β : Fin (m + 1) → Fin (r + 1))
    (he : face e b β = 0) :
    ev hP halgX halgY U V hU hV l
      (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) m e) b ε β = 0 := by
  rw [ev]
  trans slant hP halgX halgY U hU l (inter V b) (hV r b) 0
  · congr 1
    funext σ
    have hf : res (P := ab P.presheaf) (le_inter_prodCover U V σ b ε β)
        (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) m e
          (fun j => (σ (ε j), b (β j)))) =
        (p₂.appLE (inter V b) (prodOpen p₁ p₂ (inter U σ) (inter V b)) inf_le_right).hom
          (face e b β) := by
      rw [pull_apply, res_appLE, face, appLE_res]
      rfl
    rw [hf, he, map_zero]
    rfl
  · exact map_zero _

/-- Shuffle slant kills a normalized degree-two cocycle pulled from the first axis. -/
lemma L_pull_left_normalizeTwo (e : C (ab X.presheaf) U 2)
    (he : d (ab X.presheaf) U 2 e = 0) :
    L hP halgX halgY U V hU hV l 1
      (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 2 (normalizeTwo e)) = 0 := by
  funext b
  rw [L_apply]
  apply Finset.sum_eq_zero
  intro s _
  rw [ev_pull_left_zero hP halgX halgY U V hU hV l]
  · exact smul_zero _
  · intro σ
    fin_cases s
    · have hs : (step (0 + 1) : Fin 3 → Fin 2) = ![0, 1, 1] := by
        funext a; fin_cases a <;> rfl
      rw [hs]
      exact normalizeTwo_face_right e he σ
    · have hs : (step (1 + 1) : Fin 3 → Fin 2) = ![0, 0, 1] := by
        funext a; fin_cases a <;> rfl
      rw [hs]
      exact normalizeTwo_face_left e he σ

/-- Shuffle slant kills a normalized degree-two cocycle pulled from the second axis. -/
lemma L_pull_right_normalizeTwo (e : C (ab Y.presheaf) V 2)
    (he : d (ab Y.presheaf) V 2 e = 0) :
    L hP halgX halgY U V hU hV l 1
      (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 2 (normalizeTwo e)) = 0 := by
  funext b
  rw [L_apply]
  apply Finset.sum_eq_zero
  intro s _
  rw [ev_pull_right_zero hP halgX halgY U V hU hV l]
  · exact smul_zero _
  · fin_cases s
    · have hs : (degen 0 : Fin 3 → Fin 2) = ![0, 0, 1] := by
        funext a; fin_cases a <;> rfl
      rw [hs]
      exact normalizeTwo_face_left e he b
    · have hs : (degen 1 : Fin 3 → Fin 2) = ![0, 1, 1] := by
        funext a; fin_cases a <;> rfl
      rw [hs]
      exact normalizeTwo_face_right e he b

end Langlands.Cohomology.Cech.KunnethDetection

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech Cech.KunnethDetection DerivedSections
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

section NormalizeClass

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of K))
  {ι : Type u} [Fintype ι] (U : ι → X.Opens)

/-- The normalized cocycle representing the same actual degree-two class. -/
def normalizeTwoZ (z : LinearMap.ker (dCochain π U (unitModule X) 2)) :
    LinearMap.ker (dCochain π U (unitModule X) 2) :=
  ⟨normalizeTwo (z.1 : C (ab X.presheaf) U 2), by
    rw [LinearMap.mem_ker, dCochain_unit]
    apply normalizeTwo_closed
    rw [← dCochain_unit π U 2 z.1]
    exact z.2⟩

variable [IsSeparated π] (hUtop : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))

lemma canonicalClass_normalizeTwoZ (z : LinearMap.ker (dCochain π U (unitModule X) 2)) :
    canonicalClass π U hUtop hUa 1 (normalizeTwoZ π U z) =
      canonicalClass π U hUtop hUa 1 z := by
  rw [← canonicalClassExtension_cocycle, ← canonicalClassExtension_cocycle]
  change canonicalClassExtension π U hUtop hUa 1
    (z.1 - dCochain π U (unitModule X) 1
      (show cochain π U (unitModule X) 1 from twoCorrection
        (z.1 : C (ab X.presheaf) U 2))) = _
  rw [map_sub, canonicalClassExtension_dCochain, sub_zero]

end NormalizeClass

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

/-- Slant by any actual H1 dual kills every degree-two pullback from the first axis. -/
lemma slantByH1Dual_pull_left
    (ell : (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K] K)
    (x : (relativeCohomology X.hom 2).obj (unitModule X.left)) :
    slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa hUVtop hUVa ell 1
      (unitCohomologyPullback p₁ 2 x) = 0 := by
  obtain ⟨z, rfl⟩ := canonicalClass_surjective X.hom U hUtop hUa 1 x
  rw [← canonicalClass_normalizeTwoZ X.hom U hUtop hUa z]
  dsimp only [unitCohomologyPullback]
  rw [pull_canonicalClass p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
      (fun _ => inf_le_left) hUtop hUVtop hUa hUVa]
  unfold slantByH1Dual
  rw [slantCanonical_canonicalClass]
  have hzero : slantCochainMap hP halgX halgY halgP p₁.w U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 1
      ((unitCochainMap p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
        (fun _ => inf_le_left)).f 2 (normalizeTwoZ X.hom U z).1) = 0 := by
    apply (cochainSecEquiv Y.hom V halgY 1).injective
    rw [map_zero]
    change L hP halgX halgY U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 1
      ((unitCochainMap p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
        (fun _ => inf_le_left)).f 2 (normalizeTwoZ X.hom U z).1) = 0
    rw [unitCochainMap_eq_pull]
    apply L_pull_left_normalizeTwo
    rw [← dCochain_unit X.hom U 2 z.1]
    exact z.2
  rw [show (⟨_, _⟩ : LinearMap.ker (dCochain Y.hom V (unitModule Y.left) 1)) = 0 from
    Subtype.ext hzero, map_zero]

/-- Slant by any actual H1 dual kills every degree-two pullback from the second axis. -/
lemma slantByH1Dual_pull_right
    (ell : (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K] K)
    (y : (relativeCohomology Y.hom 2).obj (unitModule Y.left)) :
    slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa hUVtop hUVa ell 1
      (unitCohomologyPullback p₂ 2 y) = 0 := by
  obtain ⟨z, rfl⟩ := canonicalClass_surjective Y.hom V hVtop hVa 1 y
  rw [← canonicalClass_normalizeTwoZ Y.hom V hVtop hVa z]
  dsimp only [unitCohomologyPullback]
  rw [pull_canonicalClass p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
      (fun _ => inf_le_right) hVtop hUVtop hVa hUVa]
  unfold slantByH1Dual
  rw [slantCanonical_canonicalClass]
  have hzero : slantCochainMap hP halgX halgY halgP p₁.w U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 1
      ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
        (fun _ => inf_le_right)).f 2 (normalizeTwoZ Y.hom V z).1) = 0 := by
    apply (cochainSecEquiv Y.hom V halgY 1).injective
    rw [map_zero]
    change L hP halgX halgY U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 1
      ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
        (fun _ => inf_le_right)).f 2 (normalizeTwoZ Y.hom V z).1) = 0
    rw [unitCochainMap_eq_pull]
    apply L_pull_right_normalizeTwo
    rw [← dCochain_unit Y.hom V 2 z.1]
    exact z.2
  rw [show (⟨_, _⟩ : LinearMap.ker (dCochain Y.hom V (unitModule Y.left) 1)) = 0 from
    Subtype.ext hzero, map_zero]

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
