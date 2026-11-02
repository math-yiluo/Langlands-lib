import Langlands.Representation.Aubert.SubgroupComplex

/-! Naturality of the actual signed subgroup complex and its terminal quotient. -/

noncomputable section

set_option maxHeartbeats 1600000

namespace Langlands.Aubert.CutComplex.Diagram

universe uI uA uB

variable {ι : Type uI} [LinearOrder ι]
variable (D : CutComplex.Diagram.{uI, uA} ι) (E : CutComplex.Diagram.{uI, uB} ι)
variable (f : ∀ s, D.Obj s →ₗ[ℂ] E.Obj s)

/-- Apply a family of coefficient maps on the total product. -/
def mapTotal : D.Total →ₗ[ℂ] E.Total where
  toFun x s := f s (x s)
  map_add' x y := by funext s; exact (f s).map_add _ _
  map_smul' a x := by funext s; exact (f s).map_smul _ _

/-- Apply the same family on one homogeneous degree. -/
def mapDegree (k : ℕ) : D.Degree k →ₗ[ℂ] E.Degree k where
  toFun x s := f s.1 (x s)
  map_add' x y := by funext s; exact (f s.1).map_add _ _
  map_smul' a x := by funext s; exact (f s.1).map_smul _ _

@[simp] theorem mapTotal_apply (x : D.Total) (s : Finset ι) :
    mapTotal D E f x s = f s (x s) := rfl

@[simp] theorem mapDegree_apply (k : ℕ) (x : D.Degree k)
    (s : {s : Finset ι // s.card = k}) :
    mapDegree D E f k x s = f s.1 (x s) := rfl

theorem mapTotal_extend (k : ℕ) (x : D.Degree k) :
    mapTotal D E f (D.extend k x) = E.extend k (mapDegree D E f k x) := by
  funext s
  by_cases hs : s.card = k
  · simp only [mapTotal_apply, extend_apply, hs, ↓reduceDIte, mapDegree_apply]
  · simp only [mapTotal_apply, extend_apply, hs, ↓reduceDIte, map_zero]

variable (h : ∀ {s t : Finset ι} (hst : s ⊆ t),
  f t ∘ₗ D.map hst = E.map hst ∘ₗ f s)

include h

theorem mapTotal_step (i : ι) (x : D.Total) :
    mapTotal D E f (D.step i x) = E.step i (mapTotal D E f x) := by
  funext s
  by_cases hi : i ∈ s
  · simp only [mapTotal_apply, step_apply, hi, ↓reduceIte, map_smul]
    exact congrArg (fun y => CutComplex.sign s i • y)
      (LinearMap.congr_fun (h (Finset.erase_subset i s)) (x (s.erase i)))
  · simp only [mapTotal_apply, step_apply, hi, ↓reduceIte, map_zero]

variable [Fintype ι]

theorem mapTotal_differential (x : D.Total) :
    mapTotal D E f (D.differential x) = E.differential (mapTotal D E f x) := by
  simp only [differential_apply, map_sum, mapTotal_step D E f h]

/-- A commuting diagram map is a chain map for the signed differentials. -/
theorem mapDegree_differential (k : ℕ) (x : D.Degree k) :
    mapDegree D E f (k + 1) (D.degreeDifferential k x) =
      E.degreeDifferential k (mapDegree D E f k x) := by
  apply E.extend_injective (k + 1)
  rw [← mapTotal_extend, D.extend_degreeDifferential,
    mapTotal_differential D E f h, mapTotal_extend, E.extend_degreeDifferential]

end Langlands.Aubert.CutComplex.Diagram

namespace Langlands.Aubert.SubgroupComplex

open Jacquet.Localization

universe uI uG uV uW uX

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (P U : Finset ι → Subgroup G)
variable (hPU : ∀ s, P s ≤ Subgroup.normalizer (U s))
variable (hP : Antitone P) (hU : Monotone U)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- The canonical family induced by an ambient intertwiner. -/
def objectMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (s : Finset ι) :
    Term P U hPU ρ s →ₗ[ℂ] Term P U hPU σ s :=
  (SubgroupTransition.termMap (P s) (U s) (hPU s) f).toLinearMap

omit [Fintype ι] in
theorem objectMap_natural {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) {s t : Finset ι} (hst : s ⊆ t) :
    objectMap P U hPU f t ∘ₗ (diagram P U hPU hP hU ρ).map hst =
      (diagram P U hPU hP hU σ).map hst ∘ₗ objectMap P U hPU f s :=
  congrArg Representation.IntertwiningMap.toLinearMap
    (SubgroupTransition.map_natural (P s) (U s) (P t) (U t)
      (hPU s) (hPU t) (hP hst) (hU hst) f).symm

/-- The canonical equivariant map on a homogeneous degree. -/
def degreeMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (k : ℕ) :
    (degreeRepresentation P U hPU hP hU ρ k).IntertwiningMap
      (degreeRepresentation P U hPU hP hU σ k) where
  toLinearMap := CutComplex.Diagram.mapDegree
    (diagram P U hPU hP hU ρ) (diagram P U hPU hP hU σ) (objectMap P U hPU f) k
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext s
    exact LinearMap.congr_fun
      ((SubgroupTransition.termMap (P s.1) (U s.1) (hPU s.1) f).isIntertwining' g) (x s)

/-- The actual coefficient maps commute with the signed differential. -/
theorem degreeMap_differential {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (k : ℕ) :
    (degreeMap P U hPU hP hU f (k + 1)).comp (differential P U hPU hP hU ρ k) =
      (differential P U hPU hP hU σ k).comp (degreeMap P U hPU hP hU f k) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact CutComplex.Diagram.mapDegree_differential
    (diagram P U hPU hP hU ρ) (diagram P U hPU hP hU σ)
    (objectMap P U hPU f) (objectMap_natural P U hPU hP hU f) k

theorem boundary_map_le {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (k : ℕ) :
    boundary P U hPU hP hU ρ k ≤
      (boundary P U hPU hP hU σ k).comap (degreeMap P U hPU hP hU f k).toLinearMap := by
  cases k with
  | zero => exact bot_le
  | succ k =>
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨degreeMap P U hPU hP hU f k y,
      (LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
        (degreeMap_differential P U hPU hP hU f k)) y).symm⟩

/-- The actual induced map on the retained terminal quotient. -/
def terminalMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (k : ℕ) :
    (terminalRepresentation P U hPU hP hU ρ k).IntertwiningMap
      (terminalRepresentation P U hPU hP hU σ k) where
  toLinearMap := Submodule.mapQ
    (boundary P U hPU hP hU ρ k) (boundary P U hPU hP hU σ k)
    (degreeMap P U hPU hP hU f k).toLinearMap (boundary_map_le P U hPU hP hU f k)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    change (boundary P U hPU hP hU σ k).mkQ
        (degreeMap P U hPU hP hU f k (degreeRepresentation P U hPU hP hU ρ k g x)) =
      (boundary P U hPU hP hU σ k).mkQ
        (degreeRepresentation P U hPU hP hU σ k g (degreeMap P U hPU hP hU f k x))
    exact congrArg (boundary P U hPU hP hU σ k).mkQ
      (LinearMap.congr_fun ((degreeMap P U hPU hP hU f k).isIntertwining' g) x)

/-- Naturality of the actual terminal quotient projection. -/
theorem terminalMap_comp_projection {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (k : ℕ) :
    (terminalMap P U hPU hP hU f k).comp (terminalProjection P U hPU hP hU ρ k) =
      (terminalProjection P U hPU hP hU σ k).comp (degreeMap P U hPU hP hU f k) := by
  apply Representation.IntertwiningMap.ext
  rfl

end Langlands.Aubert.SubgroupComplex
