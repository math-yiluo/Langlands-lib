import Langlands.AlgebraicGeometry.AffineCechDeRhamSquareZeroHomotopy

/-! # Čech–de Rham pullback from local lifts over a square-zero extension -/

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}

/-- The section algebra on the intersection indexed by a tuple of charts. -/
abbrev tupleSections (f : X ⟶ Spec (CommRingCat.of R)) (U : Scheme.AffineOpenCover.{u} X)
    {p : ℕ} (σ : Fin (p + 1) → U.I₀) : CommAlgCat.{u} R :=
  (sectionAlgebras f).obj (op (inter (coverOpens U) σ))

/-- Restrict sections from the intersection of selected charts to the full intersection. -/
def restrictSections (f : X ⟶ Spec (CommRingCat.of R)) (U : Scheme.AffineOpenCover.{u} X)
    {p q : ℕ} (τ : Fin (q + 1) → U.I₀) (θ : Fin (p + 1) → Fin (q + 1)) :
    tupleSections f U (τ ∘ θ) →ₐ[R] tupleSections f U τ :=
  ((sectionAlgebras f).map (homOfLE (inter_le_comp τ θ)).op).hom

/-- Restrict the cochain on a selected subtuple to the full intersection. -/
abbrev restrictCochain (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) {p q : ℕ}
    (a : Cochains U P p) (τ : Fin (q + 1) → U.I₀) (θ : Fin (p + 1) → Fin (q + 1)) :
    P.obj (op (inter (coverOpens U) τ)) :=
  P.map (homOfLE (inter_le_comp τ θ)).op (a (τ ∘ θ))

private abbrev vertex {n : ℕ} (i : Fin n) : Fin (0 + 1) → Fin n := fun _ => i

private lemma restrictCochain_restrict {p q r : ℕ}
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (a : Cochains U P p)
    (τ : Fin (r + 1) → U.I₀) (θ : Fin (q + 1) → Fin (r + 1))
    (ψ : Fin (p + 1) → Fin (q + 1)) :
    P.map (homOfLE (inter_le_comp τ θ)).op (restrictCochain P a (τ ∘ θ) ψ) =
      restrictCochain P a τ (θ ∘ ψ) := by
  unfold restrictCochain
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

private lemma cechD_zero_apply (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (a : Cochains U P 0) (τ : Fin (1 + 1) → U.I₀) :
    cechD U P 0 a τ = restrictCochain P a τ (vertex 1) - restrictCochain P a τ (vertex 0) := by
  have h0 : (0 : Fin (0 + 2)).succAbove = vertex 1 := funext fun i => by fin_cases i; rfl
  have h1 : (1 : Fin (0 + 2)).succAbove = vertex 0 := funext fun i => by fin_cases i; rfl
  rw [cechD_apply, Fin.sum_univ_two]
  change (1 : ℤ) • restrictCochain P a τ (0 : Fin 2).succAbove +
    (-1 : ℤ) • restrictCochain P a τ (1 : Fin 2).succAbove = _
  rw [h0, h1, one_smul, neg_one_smul, sub_eq_add_neg]

private lemma cechD_one_apply (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (a : Cochains U P 1) (τ : Fin (2 + 1) → U.I₀) :
    cechD U P 1 a τ = restrictCochain P a τ (0 : Fin 3).succAbove -
      restrictCochain P a τ (1 : Fin 3).succAbove +
      restrictCochain P a τ (2 : Fin 3).succAbove := by
  rw [cechD_apply, Fin.sum_univ_three]
  change (1 : ℤ) • restrictCochain P a τ (0 : Fin 3).succAbove +
    (-1 : ℤ) • restrictCochain P a τ (1 : Fin 3).succAbove +
    (1 : ℤ) • restrictCochain P a τ (2 : Fin 3).succAbove = _
  rw [one_smul, neg_one_smul, one_smul, sub_eq_add_neg]

/-- Pullbacks to every overlap, indexed by the chart supplying the local lift.
They commute with restrictions for a fixed chart and agree modulo the base ideal. -/
structure LocalPullbacks (I : Ideal R) (β : U.I₀ → V.I₀) where
  sections : ∀ {p : ℕ} (σ : Fin (p + 1) → U.I₀), Fin (p + 1) →
    tupleSections g V (β ∘ σ) →ₐ[R] tupleSections f U σ
  restrict_sections : ∀ {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1)),
    (restrictSections f U τ θ).comp (sections (τ ∘ θ) i) =
      (sections τ (θ i)).comp (restrictSections g V (β ∘ τ) θ)
  congruent : ∀ {p : ℕ} (σ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1))
    (a : tupleSections g V (β ∘ σ)),
    sections σ i a - sections σ j a ∈ I.map (algebraMap R (tupleSections f U σ))

namespace LocalPullbacks

open RelativeForms

variable {I : Ideal R} {β : U.I₀ → V.I₀}
  (L : LocalPullbacks (f := f) (g := g) (U := U) (V := V) I β) (hI : I * I = ⊥)

private lemma restrictSections_apply {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1))
    (a : tupleSections g V ((β ∘ τ) ∘ θ)) :
    restrictSections f U τ θ (L.sections (τ ∘ θ) i a) =
      L.sections τ (θ i) (restrictSections g V (β ∘ τ) θ a) :=
  DFunLike.congr_fun (L.restrict_sections τ θ i) a

private lemma restrictOne_apply {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1))
    (a : Ω[(tupleSections g V ((β ∘ τ) ∘ θ))⁄R]) :
    mapOne (restrictSections f U τ θ) (mapOne (L.sections (τ ∘ θ) i) a) =
      mapOne (L.sections τ (θ i)) (mapOne (restrictSections g V (β ∘ τ) θ) a) := by
  rw [← mapOne_comp, L.restrict_sections, mapOne_comp]
  rfl

/-- The contraction of the difference between two local pullbacks on a tuple intersection. -/
abbrev contraction {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1)) :=
  contractDifferenceOne (L.sections τ i) (L.sections τ j) hI (L.congruent τ i j)

private lemma restrictSections_contract (M : LocalPullbacks (f := f) (g := g) I β)
    (hLM : ∀ {p : ℕ} (σ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1))
      (a : tupleSections g V (β ∘ σ)),
      L.sections σ i a - M.sections σ j a ∈ I.map (algebraMap R (tupleSections f U σ)))
    {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i j : Fin (p + 1))
    (ω : Ω[(tupleSections g V ((β ∘ τ) ∘ θ))⁄R]) :
    restrictSections f U τ θ
      (contractDifferenceOne (L.sections (τ ∘ θ) i) (M.sections (τ ∘ θ) j)
        hI (hLM (τ ∘ θ) i j) ω) =
      contractDifferenceOne (L.sections τ (θ i)) (M.sections τ (θ j)) hI (hLM τ (θ i) (θ j))
        (mapOne (restrictSections g V (β ∘ τ) θ) ω) := by
  let resX := restrictSections f U τ θ
  let resY := restrictSections g V (β ∘ τ) θ
  have hc (a : tupleSections g V ((β ∘ τ) ∘ θ)) :
      (resX.comp (L.sections (τ ∘ θ) i)) a - (resX.comp (M.sections (τ ∘ θ) j)) a ∈
        I.map (algebraMap R (tupleSections f U τ)) := by
    change resX (L.sections (τ ∘ θ) i a) - resX (M.sections (τ ∘ θ) j a) ∈ _
    rw [← map_sub]
    exact map_mem_extendedIdeal resX (hLM (τ ∘ θ) i j a)
  rw [← contractDifferenceOne_postcomp (L.sections (τ ∘ θ) i) (M.sections (τ ∘ θ) j)
    hI (hLM (τ ∘ θ) i j) resX hc]
  refine (contractDifferenceOne_congr _ _ hI hc _ _
    (fun a => hLM τ (θ i) (θ j) (resY a))
    (L.restrict_sections τ θ i) (M.restrict_sections τ θ j) _).trans ?_
  exact contractDifferenceOne_precomp _ _ hI (hLM τ (θ i) (θ j)) resY _ _

private lemma restrictSections_contraction {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i j : Fin (p + 1))
    (ω : Ω[(tupleSections g V ((β ∘ τ) ∘ θ))⁄R]) :
    restrictSections f U τ θ (L.contraction hI (τ ∘ θ) i j ω) =
      L.contraction hI τ (θ i) (θ j) (mapOne (restrictSections g V (β ∘ τ) θ) ω) :=
  L.restrictSections_contract hI L L.congruent τ θ i j ω

private def restrictAlongBase {A B M N : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    [Module R M] [Module R N] [IsScalarTower R A M] [IsScalarTower R B N]
    {a : A →ₐ[R] B} (F : M →ₛₗ[a.toRingHom] N) : M →ₗ[R] N where
  toFun := F
  map_add' := F.map_add
  map_smul' r m := by
    change F (r • m) = r • F m
    rw [← IsScalarTower.algebraMap_smul A, F.map_smulₛₗ]
    exact (congrArg (· • F m) (a.commutes r)).trans (IsScalarTower.algebraMap_smul B _ _)

/-- Pull back functions on individual charts. -/
def cochainZero : C0 g V →ₗ[R] C0 f U :=
  LinearMap.pi fun τ => (L.sections τ 0).toLinearMap.comp (LinearMap.proj (β ∘ τ))

/-- Pull back the local one-forms and correct the function cochain on each pair
by the contraction of the difference between the two local pullbacks. -/
def cochainOne : C1 g V →ₗ[R] C1 f U :=
  (LinearMap.pi fun τ =>
    ((L.sections τ 0).toLinearMap.comp (LinearMap.proj (β ∘ τ))).comp (LinearMap.fst _ _ _) +
      ((restrictAlongBase (L.contraction hI τ 1 0)).comp
        (((oneForms g).map (homOfLE (inter_le_comp (β ∘ τ) (vertex 1))).op).hom.comp
          (LinearMap.proj (β ∘ τ ∘ vertex 1)))).comp (LinearMap.snd _ _ _)).prod
    (LinearMap.pi fun τ => ((restrictAlongBase (mapOne (L.sections τ 0))).comp
      (LinearMap.proj (β ∘ τ))).comp (LinearMap.snd _ _ _))

@[simp]
lemma cochainZero_apply (a : C0 g V) (τ : Fin (0 + 1) → U.I₀) :
    L.cochainZero a τ = L.sections τ 0 (a (β ∘ τ)) := rfl

@[simp]
lemma cochainOne_fst (a : C1 g V) (τ : Fin (1 + 1) → U.I₀) :
    (L.cochainOne hI a).1 τ = L.sections τ 0 (a.1 (β ∘ τ)) +
      L.contraction hI τ 1 0 (restrictCochain (oneForms g) a.2 (β ∘ τ) (vertex 1)) := rfl

@[simp]
lemma cochainOne_snd (a : C1 g V) (τ : Fin (0 + 1) → U.I₀) :
    (L.cochainOne hI a).2 τ = mapOne (L.sections τ 0) (a.2 (β ∘ τ)) := rfl

/-- The corrected pullback sends a total boundary to the boundary of the
pullback of the degree-zero cochain. -/
lemma cochainOne_D0 (a : C0 g V) :
    L.cochainOne hI (D0 g V a) = D0 f U (L.cochainZero a) := by
  refine Prod.ext (funext fun τ => ?_) (funext fun τ => ?_)
  · let y₁ := restrictCochain (functions g) a (β ∘ τ) (vertex 1)
    let y₀ := restrictCochain (functions g) a (β ∘ τ) (vertex 0)
    simp only [cochainOne_fst, D0_apply, cechD_zero_apply]
    change L.sections τ 0 (y₁ - y₀) + L.contraction hI τ 1 0
      (mapOne (restrictSections g V (β ∘ τ) (vertex 1))
        (KaehlerDifferential.D R _ (a (β ∘ τ ∘ vertex 1)))) =
      restrictSections f U τ (vertex 1) (L.sections (τ ∘ vertex 1) 0 (a (β ∘ τ ∘ vertex 1))) -
        restrictSections f U τ (vertex 0) (L.sections (τ ∘ vertex 0) 0 (a (β ∘ τ ∘ vertex 0)))
    rw [mapOne_d, contractDifferenceOne_d,
      L.restrictSections_apply τ (vertex 1) 0, L.restrictSections_apply τ (vertex 0) 0, map_sub]
    change L.sections τ 0 y₁ - L.sections τ 0 y₀ + (L.sections τ 1 y₁ - L.sections τ 0 y₁) =
      L.sections τ 1 y₁ - L.sections τ 0 y₀
    abel
  · simp only [cochainOne_snd, D0_apply, cochainMap_apply]
    exact mapOne_d (L.sections τ 0) (a (β ∘ τ))

private lemma cocycle_conditions (a : cocycles g V) :
    cechD V (functions g) 1 a.val.1 = 0 ∧
      cechD V (oneForms g) 0 a.val.2 = cochainMap V (exteriorD0 g) 1 a.val.1 ∧
      cochainMap V (exteriorD1 g) 0 a.val.2 = 0 := by
  have ha := a.property
  change D1 g V a.val = 0 at ha
  rw [D1_apply] at ha
  exact ⟨congrArg Prod.fst ha, sub_eq_zero.mp (congrArg (fun p => p.2.1) ha),
    congrArg (fun p => p.2.2) ha⟩

private lemma cochainOne_closed_oneForms (a : cocycles g V) (τ : Fin (0 + 1) → U.I₀) :
    cochainMap U (exteriorD1 f) 0 (L.cochainOne hI a.val).2 τ = 0 := by
  have ha := congrFun (cocycle_conditions a).2.2 (β ∘ τ)
  change dOne R _ (a.val.2 (β ∘ τ)) = 0 at ha
  rw [cochainMap_apply, cochainOne_snd]
  change dOne R _ (mapOne (L.sections τ 0) (a.val.2 (β ∘ τ))) = 0
  rw [dOne_natural, ha, map_zero]

private lemma cochainOne_dZero_eq_cechD (a : cocycles g V) (τ : Fin (1 + 1) → U.I₀) :
    cochainMap U (exteriorD0 f) 1 (L.cochainOne hI a.val).1 τ =
      cechD U (oneForms f) 0 (L.cochainOne hI a.val).2 τ := by
  let A := tupleSections g V (β ∘ τ)
  let x : A := a.val.1 (β ∘ τ)
  let w₁ : Ω[(tupleSections g V ((β ∘ τ) ∘ vertex 1))⁄R] := a.val.2 (β ∘ τ ∘ vertex 1)
  let w₀ : Ω[(tupleSections g V ((β ∘ τ) ∘ vertex 0))⁄R] := a.val.2 (β ∘ τ ∘ vertex 0)
  let y₁ : Ω[A⁄R] := restrictCochain (oneForms g) a.val.2 (β ∘ τ) (vertex 1)
  let y₀ : Ω[A⁄R] := restrictCochain (oneForms g) a.val.2 (β ∘ τ) (vertex 0)
  have ha := congrFun (cocycle_conditions a).2.1 (β ∘ τ)
  rw [cechD_zero_apply, cochainMap_apply] at ha
  change y₁ - y₀ = dZero R A x at ha
  have hb : dOne R _ w₁ = 0 := congrFun (cocycle_conditions a).2.2 (β ∘ τ ∘ vertex 1)
  have hy₁ : dOne R A y₁ = 0 := by
    change dOne R A (mapOne (restrictSections g V (β ∘ τ) (vertex 1)) w₁) = 0
    rw [dOne_natural, hb, map_zero]
  simp only [cochainMap_apply, cochainOne_fst, cechD_zero_apply]
  change dZero R _ (L.sections τ 0 x + L.contraction hI τ 1 0 y₁) =
    mapOne (restrictSections f U τ (vertex 1))
      (mapOne (L.sections (τ ∘ vertex 1) 0) w₁) -
      mapOne (restrictSections f U τ (vertex 0))
        (mapOne (L.sections (τ ∘ vertex 0) 0) w₀)
  have hmap : dZero R _ (L.sections τ 0 x) = mapOne (L.sections τ 0) (dZero R A x) :=
    (mapOne_d (L.sections τ 0) x).symm
  rw [map_add, hmap, ← ha,
    ← mapOne_sub_eq_d_contract_of_closed _ _ hI _ hy₁,
    L.restrictOne_apply τ (vertex 1) 0, L.restrictOne_apply τ (vertex 0) 0]
  change mapOne (L.sections τ 0) (y₁ - y₀) +
      (mapOne (L.sections τ 1) y₁ - mapOne (L.sections τ 0) y₁) =
    mapOne (L.sections τ 1) y₁ - mapOne (L.sections τ 0) y₀
  rw [map_sub]
  abel

private lemma restrictOne_vertex {p q : ℕ} (a : Cochains V (oneForms g) 0)
    (τ : Fin (q + 1) → V.I₀) (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1)) :
    mapOne (restrictSections g V τ θ) (restrictCochain (oneForms g) a (τ ∘ θ) (vertex i)) =
      restrictCochain (oneForms g) a τ (vertex (θ i)) :=
  restrictCochain_restrict (oneForms g) a τ θ (vertex i)

private lemma cochainOne_cechD_functions (a : cocycles g V) (τ : Fin (2 + 1) → U.I₀) :
    cechD U (functions f) 1 (L.cochainOne hI a.val).1 τ = 0 := by
  let σ := β ∘ τ
  let θ₀ := (0 : Fin 3).succAbove
  let θ₁ := (1 : Fin 3).succAbove
  let θ₂ := (2 : Fin 3).succAbove
  let A := tupleSections g V σ
  let r₀ := restrictSections g V σ θ₀
  let r₁ := restrictSections g V σ θ₁
  let r₂ := restrictSections g V σ θ₂
  let x₀ : tupleSections g V (σ ∘ θ₀) := a.val.1 (σ ∘ θ₀)
  let x₁ : tupleSections g V (σ ∘ θ₁) := a.val.1 (σ ∘ θ₁)
  let x₂ : tupleSections g V (σ ∘ θ₂) := a.val.1 (σ ∘ θ₂)
  let y₁ : Ω[A⁄R] := restrictCochain (oneForms g) a.val.2 σ (vertex 1)
  let y₂ : Ω[A⁄R] := restrictCochain (oneForms g) a.val.2 σ (vertex 2)
  have ha₀ := congrFun (cocycle_conditions a).1 σ
  rw [cechD_one_apply] at ha₀
  change r₀ x₀ - r₁ x₁ + r₂ x₂ = 0 at ha₀
  have ha₁ := congrFun (cocycle_conditions a).2.1 (σ ∘ θ₀)
  rw [cechD_zero_apply, cochainMap_apply] at ha₁
  let v₂ : Ω[(tupleSections g V (σ ∘ θ₀))⁄R] :=
    restrictCochain (oneForms g) a.val.2 (σ ∘ θ₀) (vertex 1)
  let v₁ : Ω[(tupleSections g V (σ ∘ θ₀))⁄R] :=
    restrictCochain (oneForms g) a.val.2 (σ ∘ θ₀) (vertex 0)
  change v₂ - v₁ = KaehlerDifferential.D R _ x₀ at ha₁
  have hd : y₂ - y₁ = KaehlerDifferential.D R A (r₀ x₀) := by
    have h := congrArg (mapOne r₀) ha₁
    rw [map_sub, mapOne_d] at h
    have h₂ : mapOne r₀ v₂ = y₂ := restrictOne_vertex a.val.2 σ θ₀ 1
    have h₁ : mapOne r₀ v₁ = y₁ := restrictOne_vertex a.val.2 σ θ₀ 0
    rwa [h₂, h₁] at h
  rw [cechD_one_apply]
  simp only [restrictCochain, cochainOne_fst]
  change
    restrictSections f U τ θ₀ (L.sections (τ ∘ θ₀) 0 x₀ +
      L.contraction hI (τ ∘ θ₀) 1 0
        (restrictCochain (oneForms g) a.val.2 (σ ∘ θ₀) (vertex 1))) -
    restrictSections f U τ θ₁ (L.sections (τ ∘ θ₁) 0 x₁ +
      L.contraction hI (τ ∘ θ₁) 1 0
        (restrictCochain (oneForms g) a.val.2 (σ ∘ θ₁) (vertex 1))) +
    restrictSections f U τ θ₂ (L.sections (τ ∘ θ₂) 0 x₂ +
      L.contraction hI (τ ∘ θ₂) 1 0
        (restrictCochain (oneForms g) a.val.2 (σ ∘ θ₂) (vertex 1))) = 0
  rw [map_add, map_add, map_add,
    L.restrictSections_apply τ θ₀ 0, L.restrictSections_apply τ θ₁ 0,
    L.restrictSections_apply τ θ₂ 0,
    L.restrictSections_contraction hI τ θ₀ 1 0, L.restrictSections_contraction hI τ θ₁ 1 0,
    L.restrictSections_contraction hI τ θ₂ 1 0]
  have hv₀ : mapOne r₀ (restrictCochain (oneForms g) a.val.2 (σ ∘ θ₀) (vertex 1)) = y₂ :=
    restrictOne_vertex a.val.2 σ θ₀ 1
  have hv₁ : mapOne r₁ (restrictCochain (oneForms g) a.val.2 (σ ∘ θ₁) (vertex 1)) = y₂ :=
    restrictOne_vertex a.val.2 σ θ₁ 1
  have hv₂ : mapOne r₂ (restrictCochain (oneForms g) a.val.2 (σ ∘ θ₂) (vertex 1)) = y₁ :=
    restrictOne_vertex a.val.2 σ θ₂ 1
  rw [hv₀, hv₁, hv₂]
  let s₁ := L.sections τ 1
  let s₀ := L.sections τ 0
  let c₂₁ := L.contraction hI τ 2 1
  let c₂₀ := L.contraction hI τ 2 0
  let c₁₀ := L.contraction hI τ 1 0
  change (s₁ (r₀ x₀) + c₂₁ y₂) - (s₀ (r₁ x₁) + c₂₀ y₂) + (s₀ (r₂ x₂) + c₁₀ y₁) = 0
  have hc : s₁ (r₀ x₀) - s₀ (r₀ x₀) = c₁₀ y₂ - c₁₀ y₁ := by
    rw [← map_sub, hd]
    exact (contractDifferenceOne_d _ _ hI (L.congruent τ 1 0) (r₀ x₀)).symm
  have hsum : s₀ (r₀ x₀) - s₀ (r₁ x₁) + s₀ (r₂ x₂) = 0 := by
    rw [← map_sub, ← map_add, ha₀, map_zero]
  have htel : c₂₁ y₂ + c₁₀ y₂ = c₂₀ y₂ :=
    contractDifferenceOne_telescopes _ _ hI (L.congruent τ 2 1) _
      (L.congruent τ 1 0) (L.congruent τ 2 0) y₂
  calc
    _ = ((s₁ (r₀ x₀) - s₀ (r₀ x₀)) - (c₁₀ y₂ - c₁₀ y₁)) +
        (s₀ (r₀ x₀) - s₀ (r₁ x₁) + s₀ (r₂ x₂)) := by rw [← htel]; abel
    _ = 0 := by rw [hc, hsum, sub_self, add_zero]

/-- The corrected pullback on total degree one takes cocycles to cocycles. -/
lemma cochainOne_mem_cocycles (a : cocycles g V) :
    L.cochainOne hI a.val ∈ cocycles f U := by
  change D1 f U (L.cochainOne hI a.val) = 0
  rw [D1_apply]
  refine Prod.ext (funext (L.cochainOne_cechD_functions hI a))
    (Prod.ext (funext fun τ => ?_) (funext (L.cochainOne_closed_oneForms hI a)))
  exact sub_eq_zero.mpr (L.cochainOne_dZero_eq_cechD hI a τ).symm

/-- Corrected pullback of cocycles, as a linear map. -/
def cocyclePullback : cocycles g V →ₗ[R] cocycles f U :=
  LinearMap.codRestrict _ ((L.cochainOne hI).comp (cocycles g V).subtype)
    (L.cochainOne_mem_cocycles hI)

section ChangeLocalLifts

variable (M : LocalPullbacks (f := f) (g := g) I β)
  (hLM : ∀ {p : ℕ} (σ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1))
    (a : tupleSections g V (β ∘ σ)),
    L.sections σ i a - M.sections σ j a ∈ I.map (algebraMap R (tupleSections f U σ)))

private abbrev crossContraction {p : ℕ} (σ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1)) :=
  contractDifferenceOne (L.sections σ i) (M.sections σ j) hI (hLM σ i j)

private def changeLiftPrimitive (a : cocycles g V) : C0 f U := fun τ =>
  L.crossContraction hI M hLM τ 0 0 (a.val.2 (β ∘ τ))

private lemma cochainOne_sub_eq_D0 (a : cocycles g V) :
    L.cochainOne hI a.val - M.cochainOne hI a.val =
      D0 f U (L.changeLiftPrimitive hI M hLM a) := by
  refine Prod.ext (funext fun τ => ?_) (funext fun τ => ?_)
  · let σ := β ∘ τ
    let A := tupleSections g V σ
    let x : A := a.val.1 σ
    let w₁ : Ω[(tupleSections g V (σ ∘ vertex 1))⁄R] := a.val.2 (σ ∘ vertex 1)
    let w₀ : Ω[(tupleSections g V (σ ∘ vertex 0))⁄R] := a.val.2 (σ ∘ vertex 0)
    let y₁ : Ω[A⁄R] := restrictCochain (oneForms g) a.val.2 σ (vertex 1)
    let y₀ : Ω[A⁄R] := restrictCochain (oneForms g) a.val.2 σ (vertex 0)
    have hd := congrFun (cocycle_conditions a).2.1 σ
    rw [cechD_zero_apply, cochainMap_apply] at hd
    change y₁ - y₀ = KaehlerDifferential.D R A x at hd
    change (L.cochainOne hI a.val).1 τ - (M.cochainOne hI a.val).1 τ =
      cechD U (functions f) 0 (L.changeLiftPrimitive hI M hLM a) τ
    rw [cochainOne_fst, cochainOne_fst, cechD_zero_apply]
    change (L.sections τ 0 x + L.contraction hI τ 1 0 y₁) -
        (M.sections τ 0 x + M.contraction hI τ 1 0 y₁) =
      restrictSections f U τ (vertex 1) (L.crossContraction hI M hLM (τ ∘ vertex 1) 0 0 w₁) -
        restrictSections f U τ (vertex 0) (L.crossContraction hI M hLM (τ ∘ vertex 0) 0 0 w₀)
    rw [L.restrictSections_contract hI M hLM τ (vertex 1) 0 0,
      L.restrictSections_contract hI M hLM τ (vertex 0) 0 0]
    let e₁ := L.crossContraction hI M hLM τ 1 1
    let e₀ := L.crossContraction hI M hLM τ 0 0
    let c := L.crossContraction hI M hLM τ 1 0
    change (L.sections τ 0 x + L.contraction hI τ 1 0 y₁) -
      (M.sections τ 0 x + M.contraction hI τ 1 0 y₁) = e₁ y₁ - e₀ y₀
    have ht₁ : L.contraction hI τ 1 0 y₁ + e₀ y₁ = c y₁ :=
      contractDifferenceOne_telescopes _ _ hI (L.congruent τ 1 0) _
        (hLM τ 0 0) (hLM τ 1 0) y₁
    have ht₂ : e₁ y₁ + M.contraction hI τ 1 0 y₁ = c y₁ :=
      contractDifferenceOne_telescopes _ _ hI (hLM τ 1 1) _
        (M.congruent τ 1 0) (hLM τ 1 0) y₁
    have he : e₀ y₁ - e₀ y₀ = L.sections τ 0 x - M.sections τ 0 x := by
      rw [← map_sub, hd]
      exact contractDifferenceOne_d _ _ hI (hLM τ 0 0) x
    have ht : L.contraction hI τ 1 0 y₁ - M.contraction hI τ 1 0 y₁ =
        e₁ y₁ - e₀ y₁ := by
      calc
        _ = (L.contraction hI τ 1 0 y₁ + e₀ y₁) -
            (e₁ y₁ + M.contraction hI τ 1 0 y₁) + (e₁ y₁ - e₀ y₁) := by abel
        _ = _ := by rw [ht₁, ht₂, sub_self, zero_add]
    rw [add_sub_add_comm, ← he, ht]
    abel
  · let ω : Ω[(tupleSections g V (β ∘ τ))⁄R] := a.val.2 (β ∘ τ)
    have hω : dOne R _ ω = 0 := congrFun (cocycle_conditions a).2.2 (β ∘ τ)
    change (L.cochainOne hI a.val).2 τ - (M.cochainOne hI a.val).2 τ =
      dZero R _ (L.crossContraction hI M hLM τ 0 0 ω)
    rw [cochainOne_snd, cochainOne_snd]
    exact mapOne_sub_eq_d_contract_of_closed _ _ hI (hLM τ 0 0) hω

end ChangeLocalLifts

variable [Smooth f] [IsSeparated f] [Finite U.I₀] [Smooth g] [IsSeparated g] [Finite V.I₀]

/-- The degree-one map induced by the supplied local lifts. -/
def pullbackH1 : H1 g V →ₗ[R] H1 f U :=
  (boundaries g V).liftQ ((boundaries f U).mkQ.comp (L.cocyclePullback hI)) (by
    rintro z ⟨a, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨L.cochainZero a, Subtype.ext (L.cochainOne_D0 hI a).symm⟩)

@[simp]
lemma pullbackH1_mk (a : cocycles g V) :
    L.pullbackH1 hI ((boundaries g V).mkQ a) =
      (boundaries f U).mkQ (L.cocyclePullback hI a) := rfl

/-- Two chartwise lift systems with the same reduction give the same map on
degree-one cohomology. -/
theorem pullbackH1_eq_of_congruent (M : LocalPullbacks (f := f) (g := g) I β)
    (hLM : ∀ {p : ℕ} (σ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1))
      (a : tupleSections g V (β ∘ σ)),
      L.sections σ i a - M.sections σ j a ∈ I.map (algebraMap R (tupleSections f U σ))) :
    L.pullbackH1 hI = M.pullbackH1 hI := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨a, rfl⟩ := (boundaries g V).mkQ_surjective z
  rw [pullbackH1_mk, pullbackH1_mk, ← sub_eq_zero, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨L.changeLiftPrimitive hI M hLM a,
    Subtype.ext (L.cochainOne_sub_eq_D0 hI M hLM a).symm⟩

private def closedFormCocycle (b : closedForms g V) : cocycles g V :=
  ⟨(0, b.val), by
    have hb := b.property
    change cechD V (oneForms g) 0 b.val = 0 ∧ cochainMap V (exteriorD1 g) 0 b.val = 0 at hb
    change D1 g V (0, b.val) = 0
    rw [D1_apply, map_zero, map_zero, sub_zero, hb.1, hb.2]
    rfl⟩

/-- When the corrected pullback of a closed form lies in the first Hodge
step, its difference contractions on the overlaps are a Čech boundary. -/
theorem exists_functionPrimitive_of_pullback_closedForm_mem_hodgeF1
    (b : closedForms g V) (hb : L.pullbackH1 hI (closedFormClass g V b) ∈ hodgeF1 f U) :
    ∃ h : C0 f U, ∀ τ : Fin (1 + 1) → U.I₀,
      cechD U (functions f) 0 h τ =
        L.contraction hI τ 1 0 (restrictCochain (oneForms g) b.val (β ∘ τ) (vertex 1)) := by
  let a := closedFormCocycle b
  let c := L.cocyclePullback hI a
  obtain ⟨b', hb'⟩ := hb
  change (boundaries f U).mkQ (closedFormCocycle b') =
    L.pullbackH1 hI ((boundaries g V).mkQ a) at hb'
  rw [pullbackH1_mk] at hb'
  obtain ⟨h, hh⟩ := (Submodule.Quotient.eq (boundaries f U)).mp hb'.symm
  refine ⟨h, fun τ => ?_⟩
  have hh₀ := congrArg (fun d : cocycles f U => d.val.1 τ) hh
  change cechD U (functions f) 0 h τ = (L.cochainOne hI a.val).1 τ - 0 at hh₀
  rw [sub_zero, cochainOne_fst] at hh₀
  change cechD U (functions f) 0 h τ = L.sections τ 0 0 +
    L.contraction hI τ 1 0 (restrictCochain (oneForms g) b.val (β ∘ τ) (vertex 1)) at hh₀
  simpa only [map_zero, zero_add] using hh₀

/-- A lift system whose overlap maps are independent of the selected vertex
preserves the first Hodge step. -/
theorem pullbackH1_maps_hodgeF1
    (hL : ∀ (τ : Fin (1 + 1) → U.I₀), L.sections τ 1 = L.sections τ 0)
    {z : H1 g V} (hz : z ∈ hodgeF1 g V) :
    L.pullbackH1 hI z ∈ hodgeF1 f U := by
  obtain ⟨b, rfl⟩ := hz
  let a := closedFormCocycle b
  let c := L.cocyclePullback hI a
  have hc₀ : c.val.1 = 0 := by
    funext τ
    change (L.cochainOne hI a.val).1 τ = 0
    rw [cochainOne_fst]
    have hc := contractDifferenceOne_congr (L.sections τ 1) (L.sections τ 0) hI
      (L.congruent τ 1 0) (L.sections τ 0) (L.sections τ 0)
      (fun x => by rw [sub_self]; exact Ideal.zero_mem _) (hL τ) rfl
      (restrictCochain (oneForms g) a.val.2 (β ∘ τ) (vertex 1))
    rw [hc, contractDifferenceOne_self, add_zero]
    exact map_zero (L.sections τ 0)
  have hc := c.property
  change D1 f U (c.val.1, c.val.2) = 0 at hc
  rw [hc₀, D1_apply, map_zero, map_zero, sub_zero] at hc
  have hclosed : cechD U (oneForms f) 0 c.val.2 = 0 ∧
      cochainMap U (exteriorD1 f) 0 c.val.2 = 0 :=
    ⟨congrArg (fun x => x.2.1) hc, congrArg (fun x => x.2.2) hc⟩
  let b' : closedForms f U := ⟨c.val.2, hclosed⟩
  refine ⟨b', ?_⟩
  change closedFormClass f U b' = L.pullbackH1 hI ((boundaries g V).mkQ a)
  rw [pullbackH1_mk]
  apply congrArg ((boundaries f U).mkQ)
  exact Subtype.ext (Prod.ext hc₀.symm rfl)

end LocalPullbacks

end Langlands.AlgebraicGeometry.AffineCechDeRham
