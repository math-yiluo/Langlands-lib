import Langlands.Representation.Aubert.SubgroupTransition
import Langlands.Representation.Aubert.ActualCutComplex

/-!
# Signed complexes of actual subgroup induction--coinvariant terms

The input is a family of actual subgroups and their containments. All
representation maps are constructed, and all diagram and square-zero laws
are proved. No exactness, support or finiteness theorem is an input.
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace Langlands.Aubert.SubgroupComplex

open CategoryTheory

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (P U : Finset ι → Subgroup G)
variable (hPU : ∀ s, P s ≤ Subgroup.normalizer (U s))
variable (hP : Antitone P) (hU : Monotone U)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual smooth induced-function carrier at one set of removed roots. -/
abbrev Term (ρ : Representation ℂ G V) (s : Finset ι) :=
  Induction.SmoothFunctions (P s) (SubgroupTransition.inducing (P s) (U s) (hPU s) ρ)

/-- The actual pointwise quotient transition for inclusion of index sets. -/
def transition (ρ : Representation ℂ G V) {s t : Finset ι} (h : s ⊆ t) :=
  SubgroupTransition.map (P s) (U s) (P t) (U t) (hPU s) (hPU t) (hP h) (hU h) ρ

/-- The commuting diagram of actual function-space representations. -/
def diagram (ρ : Representation ℂ G V) : CutComplex.Diagram ι where
  Obj := Term P U hPU ρ
  add _ := inferInstance
  module _ := inferInstance
  map h := (transition P U hPU hP hU ρ h).toLinearMap
  map_refl s := by
    change (SubgroupTransition.map (P s) (U s) (P s) (U s)
      (hPU s) (hPU s) _ _ ρ).toLinearMap = _
    rw [SubgroupTransition.map_refl]
    rfl
  map_comp {s t u} hst htu := by
    change ((SubgroupTransition.map (P t) (U t) (P u) (U u)
        (hPU t) (hPU u) _ _ ρ).comp
      (SubgroupTransition.map (P s) (U s) (P t) (U t)
        (hPU s) (hPU t) _ _ ρ)).toLinearMap = _
    rw [SubgroupTransition.map_comp]
    rfl

/-- The actual pointwise action on a signed homogeneous degree. -/
def degreeRepresentation (ρ : Representation ℂ G V) (k : ℕ) :
    Representation ℂ G ((diagram P U hPU hP hU ρ).Degree k) :=
  FiniteProduct.representation (fun s =>
    SubgroupTransition.term (P s.1) (U s.1) (hPU s.1) ρ)

omit [Fintype ι] in
theorem diagram_map_intertwining (ρ : Representation ℂ G V)
    {s t : Finset ι} (h : s ⊆ t) (g : G) (v : Term P U hPU ρ s) :
    (diagram P U hPU hP hU ρ).map h
        (SubgroupTransition.term (P s) (U s) (hPU s) ρ g v) =
      SubgroupTransition.term (P t) (U t) (hPU t) ρ g
        ((diagram P U hPU hP hU ρ).map h v) :=
  LinearMap.congr_fun ((transition P U hPU hP hU ρ h).isIntertwining' g) v

/-- The signed differential, equivariant for the actual ambient action. -/
def differential (ρ : Representation ℂ G V) (k : ℕ) :
    (degreeRepresentation P U hPU hP hU ρ k).IntertwiningMap
      (degreeRepresentation P U hPU hP hU ρ (k + 1)) where
  toLinearMap := (diagram P U hPU hP hU ρ).degreeDifferential k
  isIntertwining' g := LinearMap.ext fun x =>
    EquivariantDiagram.degreeDifferential_intertwining
      (diagram P U hPU hP hU ρ)
      (fun s => SubgroupTransition.term (P s) (U s) (hPU s) ρ)
      (diagram_map_intertwining P U hPU hP hU ρ) k g x

/-- Square zero follows from actual transition composition and exterior signs. -/
theorem differential_square (ρ : Representation ℂ G V) (k : ℕ) :
    (differential P U hPU hP hU ρ (k + 1)).comp
        (differential P U hPU hP hU ρ k) = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact (diagram P U hPU hP hU ρ).degreeDifferential_square k

/-- Every degree is smooth, with no finite-length premise on the input. -/
theorem degree_isSmooth (ρ : Representation ℂ G V) (k : ℕ) :
    IsSmooth (degreeRepresentation P U hPU hP hU ρ k) :=
  FiniteProduct.isSmooth
    (fun s : {s : Finset ι // s.card = k} =>
      SubgroupTransition.term (P s.1) (U s.1) (hPU s.1) ρ)
    (fun s => Induction.smoothInduced_smooth (P s.1)
      (SubgroupTransition.inducing (P s.1) (U s.1) (hPU s.1) ρ))

/-- The homogeneous object of actual smooth representations. -/
def degreeObject (ρ : Representation ℂ G V) (k : ℕ) :
    SmoothRep.{0, uG, max uI uG uV} ℂ G :=
  SmoothRep.of (degreeRepresentation P U hPU hP hU ρ k)
    (degree_isSmooth P U hPU hP hU ρ k)

/-- The signed differential as a morphism of the smooth category. -/
def degreeMorphism (ρ : Representation ℂ G V) (k : ℕ) :
    degreeObject P U hPU hP hU ρ k ⟶ degreeObject P U hPU hP hU ρ (k + 1) :=
  SmoothRep.ofHom (differential P U hPU hP hU ρ k)

/-- There are no homogeneous coordinates above the number of available roots. -/
theorem degree_subsingleton (ρ : Representation ℂ G V) (k : ℕ)
    (hk : Fintype.card ι < k) :
    Subsingleton ((diagram P U hPU hP hU ρ).Degree k) :=
  EquivariantDiagram.degree_subsingleton_of_gt (diagram P U hPU hP hU ρ) k hk

/-- Incoming boundaries at a chosen terminal degree; degree zero has no predecessor. -/
def boundary (ρ : Representation ℂ G V) (k : ℕ) :
    Submodule ℂ ((diagram P U hPU hP hU ρ).Degree k) :=
  match k with
  | 0 => ⊥
  | k + 1 => LinearMap.range (differential P U hPU hP hU ρ k).toLinearMap

theorem boundary_stable (ρ : Representation ℂ G V) (k : ℕ) (g : G) :
    boundary P U hPU hP hU ρ k ≤
      (boundary P U hPU hP hU ρ k).comap (degreeRepresentation P U hPU hP hU ρ k g) := by
  intro x hx
  change degreeRepresentation P U hPU hP hU ρ k g x ∈ boundary P U hPU hP hU ρ k
  cases k with
  | zero =>
    change x ∈ (⊥ : Submodule ℂ _) at hx
    change _ ∈ (⊥ : Submodule ℂ _)
    have hx0 : x = 0 := by simpa using hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _
  | succ k =>
    change x ∈ LinearMap.range (differential P U hPU hP hU ρ k).toLinearMap at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨degreeRepresentation P U hPU hP hU ρ k g y,
      LinearMap.congr_fun ((differential P U hPU hP hU ρ k).isIntertwining' g) y⟩

/-- The actual terminal cokernel carrier at a specified degree. -/
abbrev Terminal (ρ : Representation ℂ G V) (k : ℕ) :=
  (diagram P U hPU hP hU ρ).Degree k ⧸ boundary P U hPU hP hU ρ k

/-- The descended action on the actual terminal quotient. -/
def terminalRepresentation (ρ : Representation ℂ G V) (k : ℕ) :
    Representation ℂ G (Terminal P U hPU hP hU ρ k) :=
  Representation.quotient (degreeRepresentation P U hPU hP hU ρ k)
    (boundary P U hPU hP hU ρ k) (boundary_stable P U hPU hP hU ρ k)

/-- The canonical terminal quotient map. -/
def terminalProjection (ρ : Representation ℂ G V) (k : ℕ) :
    (degreeRepresentation P U hPU hP hU ρ k).IntertwiningMap
      (terminalRepresentation P U hPU hP hU ρ k) where
  toLinearMap := (boundary P U hPU hP hU ρ k).mkQ
  isIntertwining' _ := rfl

theorem terminalProjection_surjective (ρ : Representation ℂ G V) (k : ℕ) :
    Function.Surjective (terminalProjection P U hPU hP hU ρ k) :=
  (boundary P U hPU hP hU ρ k).mkQ_surjective

theorem terminalProjection_ker (ρ : Representation ℂ G V) (k : ℕ) :
    LinearMap.ker (terminalProjection P U hPU hP hU ρ k).toLinearMap =
      boundary P U hPU hP hU ρ k := by
  ext x
  exact Submodule.Quotient.mk_eq_zero _

/-- The incoming differential is killed, without asserting the quotient vanishes. -/
theorem terminalProjection_comp_differential (ρ : Representation ℂ G V) (k : ℕ) :
    (terminalProjection P U hPU hP hU ρ (k + 1)).comp
        (differential P U hPU hP hU ρ k) = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (boundary P U hPU hP hU ρ (k + 1)).mkQ
    ((differential P U hPU hP hU ρ k) x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

theorem terminal_isSmooth (ρ : Representation ℂ G V) (k : ℕ) :
    IsSmooth (terminalRepresentation P U hPU hP hU ρ k) :=
  isSmooth_of_surjective (terminalProjection P U hPU hP hU ρ k)
    (terminalProjection_surjective P U hPU hP hU ρ k)
    (degree_isSmooth P U hPU hP hU ρ k)

/-- The actual smooth terminal cokernel object. -/
def terminalObject (ρ : Representation ℂ G V) (k : ℕ) :
    SmoothRep.{0, uG, max uI uG uV} ℂ G :=
  SmoothRep.of (terminalRepresentation P U hPU hP hU ρ k)
    (terminal_isSmooth P U hPU hP hU ρ k)

end Langlands.Aubert.SubgroupComplex
