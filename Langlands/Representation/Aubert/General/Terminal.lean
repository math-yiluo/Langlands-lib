import Langlands.Representation.Aubert.General.Complex

/-! Actual terminal cokernels of the normalized signed complex. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.Complex

open CategoryTheory

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ s, IsSemidirectDecomposition (P s) (M s) (U s))
variable (hclosed : ∀ s, IsClosed (U s : Set G))
variable (hδ : ∀ s, IsUnimodularModulus (U s) (hclosed s))
variable (hP : Antitone P) (hU : Monotone U)

/-- Incoming boundaries at a specified terminal degree, including degree zero. -/
def boundary (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    Submodule ℂ (Degree P M U h hclosed A k) :=
  match k with
  | 0 => ⊥
  | k + 1 => LinearMap.range (differential P M U h hclosed hδ hP hU A k).toLinearMap

/-- Incoming images are invariant under the actual ambient group action. -/
theorem boundary_stable (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) (g : G) :
    boundary P M U h hclosed hδ hP hU A k ≤
      (boundary P M U h hclosed hδ hP hU A k).comap
        (degreeRepresentation P M U h hclosed A k g) := by
  intro x hx
  change degreeRepresentation P M U h hclosed A k g x ∈
    boundary P M U h hclosed hδ hP hU A k
  cases k with
  | zero =>
    change x ∈ (⊥ : Submodule ℂ _) at hx
    change _ ∈ (⊥ : Submodule ℂ _)
    have hx0 : x = 0 := by simpa using hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _
  | succ k =>
    change x ∈ LinearMap.range (differential P M U h hclosed hδ hP hU A k).toLinearMap at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨degreeRepresentation P M U h hclosed A k g y,
      LinearMap.congr_fun
        ((differential P M U h hclosed hδ hP hU A k).isIntertwining' g) y⟩

/-- The terminal carrier is the actual quotient by the incoming differential. -/
abbrev Terminal (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :=
  Degree P M U h hclosed A k ⧸
    boundary P M U h hclosed hδ hP hU A k

/-- The descended group action on the actual terminal quotient. -/
def terminalRepresentation (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    Representation ℂ G (Terminal P M U h hclosed hδ hP hU A k) :=
  Representation.quotient (degreeRepresentation P M U h hclosed A k)
    (boundary P M U h hclosed hδ hP hU A k)
    (boundary_stable P M U h hclosed hδ hP hU A k)

/-- The canonical equivariant terminal projection. -/
def terminalProjection (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    (degreeRepresentation P M U h hclosed A k).IntertwiningMap
      (terminalRepresentation P M U h hclosed hδ hP hU A k) where
  toLinearMap := (boundary P M U h hclosed hδ hP hU A k).mkQ
  isIntertwining' _ := rfl

theorem terminalProjection_surjective (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    Function.Surjective (terminalProjection P M U h hclosed hδ hP hU A k) :=
  (boundary P M U h hclosed hδ hP hU A k).mkQ_surjective

theorem terminalProjection_ker (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    LinearMap.ker (terminalProjection P M U h hclosed hδ hP hU A k).toLinearMap =
      boundary P M U h hclosed hδ hP hU A k := by
  ext x
  exact Submodule.Quotient.mk_eq_zero _

/-- The incoming differential is killed by the projection. -/
theorem terminalProjection_comp_differential
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    (terminalProjection P M U h hclosed hδ hP hU A (k + 1)).comp
      (differential P M U h hclosed hδ hP hU A k) = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (boundary P M U h hclosed hδ hP hU A (k + 1)).mkQ
    (differential P M U h hclosed hδ hP hU A k x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

theorem terminal_isSmooth (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    IsSmooth (terminalRepresentation P M U h hclosed hδ hP hU A k) :=
  isSmooth_of_surjective (terminalProjection P M U h hclosed hδ hP hU A k)
    (terminalProjection_surjective P M U h hclosed hδ hP hU A k)
    (degree_isSmooth P M U h hclosed A k)

/-- The actual smooth terminal cokernel at degree `k`. -/
def terminalObject (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    SmoothRep.{0, uG, max uI uG uV} ℂ G :=
  SmoothRep.of (terminalRepresentation P M U h hclosed hδ hP hU A k)
    (terminal_isSmooth P M U h hclosed hδ hP hU A k)

/-- The degree at which the surviving standard-root subsets have cardinality `|I|`. -/
def terminalDegree (I : Finset ι) : ℕ := Fintype.card ι - I.card

/-- The retained terminal cokernel for a specified support rank. -/
def sharpObject (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) :
    SmoothRep.{0, uG, max uI uG uV} ℂ G :=
  terminalObject P M U h hclosed hδ hP hU A (terminalDegree I)

/-- Normalization identifies the incoming image submodules exactly. -/
theorem boundary_equiv (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    (boundary P M U h hclosed hδ hP hU A k).map
        (degreeEquiv P M U h hclosed hδ hP hU A k).toLinearEquiv.toLinearMap =
      SubgroupComplex.boundary P U (fun s => (h s).le_normalizer) hP hU A.representation k := by
  cases k with
  | zero =>
    exact Submodule.map_bot _
  | succ k =>
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, rfl⟩ := hx
      exact ⟨degreeEquiv P M U h hclosed hδ hP hU A k y,
        (degreeEquiv_differential P M U h hclosed hδ hP hU A k y).symm⟩
    · rintro _ ⟨y, rfl⟩
      let x := (degreeEquiv P M U h hclosed hδ hP hU A k).symm y
      refine ⟨differential P M U h hclosed hδ hP hU A k x, ⟨x, rfl⟩, ?_⟩
      exact (degreeEquiv_differential P M U h hclosed hδ hP hU A k x).trans
        (congrArg (SubgroupComplex.differential P U (fun s => (h s).le_normalizer)
          hP hU A.representation k)
          ((degreeEquiv P M U h hclosed hδ hP hU A k).toLinearEquiv.apply_symm_apply y))

/-- The canonical linear comparison of terminal quotients. -/
def terminalLinearEquiv (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    Terminal P M U h hclosed hδ hP hU A k ≃ₗ[ℂ]
      SubgroupComplex.Terminal P U (fun s => (h s).le_normalizer) hP hU A.representation k :=
  Submodule.Quotient.equiv
    (boundary P M U h hclosed hδ hP hU A k)
    (SubgroupComplex.boundary P U (fun s => (h s).le_normalizer) hP hU A.representation k)
    (degreeEquiv P M U h hclosed hδ hP hU A k).toLinearEquiv
    (boundary_equiv P M U h hclosed hδ hP hU A k)

/-- The terminal comparison is equivariant for the actual quotient actions. -/
def terminalEquiv (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    (terminalRepresentation P M U h hclosed hδ hP hU A k).Equiv
      (SubgroupComplex.terminalRepresentation P U (fun s => (h s).le_normalizer)
        hP hU A.representation k) :=
  Representation.Equiv.mk (terminalLinearEquiv P M U h hclosed hδ hP hU A k) (fun g => by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    change (SubgroupComplex.boundary P U (fun s => (h s).le_normalizer)
        hP hU A.representation k).mkQ
      (degreeEquiv P M U h hclosed hδ hP hU A k
        (degreeRepresentation P M U h hclosed A k g x)) =
      (SubgroupComplex.boundary P U (fun s => (h s).le_normalizer)
        hP hU A.representation k).mkQ
      (SubgroupComplex.degreeRepresentation P U (fun s => (h s).le_normalizer)
        hP hU A.representation k g
        (degreeEquiv P M U h hclosed hδ hP hU A k x))
    exact congrArg
      (SubgroupComplex.boundary P U (fun s => (h s).le_normalizer)
        hP hU A.representation k).mkQ
      (LinearMap.congr_fun ((degreeEquiv P M U h hclosed hδ hP hU A k).isIntertwining' g) x))

/-- The terminal comparison commutes with the canonical quotient projections. -/
theorem terminalEquiv_projection (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ)
    (x : Degree P M U h hclosed A k) :
    terminalEquiv P M U h hclosed hδ hP hU A k
        (terminalProjection P M U h hclosed hδ hP hU A k x) =
      SubgroupComplex.terminalProjection P U (fun s => (h s).le_normalizer)
        hP hU A.representation k (degreeEquiv P M U h hclosed hδ hP hU A k x) :=
  rfl

end Langlands.Aubert.General.Complex
