import Langlands.Representation.Aubert.CutTransitionMaps
import Langlands.Representation.Aubert.SignedCutComplex
import Langlands.Representation.Category.Basic

/-! The signed complex of actual normalized induction--Jacquet terms. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear CategoryTheory
open scoped BigOperators

namespace FiniteProduct

universe uJ uG uM

variable {J : Type uJ} {G : Type uG} [Group G]
  {M : J → Type uM} [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)]

/-- The pointwise representation on a product of coefficient modules. -/
def representation (ρ : ∀ j, Representation ℂ G (M j)) :
    Representation ℂ G (∀ j, M j) where
  toFun g :=
    { toFun x j := ρ j g (x j)
      map_add' x y := by funext j; exact (ρ j g).map_add _ _
      map_smul' a x := by funext j; exact (ρ j g).map_smul _ _ }
  map_one' := by
    ext x j
    change ρ j 1 (x j) = x j
    simp
  map_mul' g h := by
    ext x j
    change ρ j (g * h) (x j) = ρ j g (ρ j h (x j))
    rw [map_mul]
    rfl

@[simp]
theorem representation_apply (ρ : ∀ j, Representation ℂ G (M j))
    (g : G) (x : ∀ j, M j) (j : J) : representation ρ g x j = ρ j g (x j) := rfl

variable [TopologicalSpace G] [Fintype J]

/-- A finite family of smooth vectors has a common open stabilizer. -/
theorem isSmooth (ρ : ∀ j, Representation ℂ G (M j)) (hρ : ∀ j, IsSmooth (ρ j)) :
    IsSmooth (representation ρ) := by
  classical
  intro x
  choose K hK using fun j => hρ j (x j)
  refine ⟨Finset.univ.inf K, ?_⟩
  intro g
  funext j
  apply hK j ⟨g, ?_⟩
  have hle : Finset.univ.inf K ≤ K j := Finset.inf_le (Finset.mem_univ j)
  exact SetLike.le_def.mp hle g.property

end FiniteProduct

namespace EquivariantDiagram

universe uI uG uM

variable {ι : Type uI} [LinearOrder ι] {G : Type uG} [Group G]
  (D : CutComplex.Diagram.{uI,uM} ι)
  (ρ : ∀ s, Representation ℂ G (D.Obj s))

theorem step_intertwining
    (hmap : ∀ {s t : Finset ι} (h : s ⊆ t) (g : G) (v : D.Obj s),
      D.map h (ρ s g v) = ρ t g (D.map h v))
    (i : ι) (g : G) (x : D.Total) :
    D.step i (FiniteProduct.representation ρ g x) =
      FiniteProduct.representation ρ g (D.step i x) := by
  funext s
  by_cases hi : i ∈ s
  · simp only [CutComplex.Diagram.step_apply, FiniteProduct.representation_apply,
      hi, ↓reduceIte]
    exact (congrArg (fun v => CutComplex.sign s i • v)
      (hmap (Finset.erase_subset i s) g (x (s.erase i)))).trans
        ((ρ s g).map_smul _ _).symm
  · simp only [CutComplex.Diagram.step_apply, FiniteProduct.representation_apply,
      hi, ↓reduceIte, map_zero]

theorem extend_intertwining (k : ℕ) (g : G) (x : D.Degree k) :
    D.extend k (FiniteProduct.representation (fun s => ρ s.1) g x) =
      FiniteProduct.representation ρ g (D.extend k x) := by
  funext s
  by_cases hs : s.card = k
  · simp only [CutComplex.Diagram.extend_apply, FiniteProduct.representation_apply,
      hs, ↓reduceDIte]
  · simp only [CutComplex.Diagram.extend_apply, FiniteProduct.representation_apply,
      hs, ↓reduceDIte]
    exact (ρ s g).map_zero.symm

variable [Fintype ι]

/-- Above the number of available cuts, the homogeneous product has no coordinates. -/
theorem degree_subsingleton_of_gt (k : ℕ) (hk : Fintype.card ι < k) :
    Subsingleton (D.Degree k) := by
  have : IsEmpty {s : Finset ι // s.card = k} := ⟨fun s => by
    have hcard := s.1.card_le_univ
    have := s.property
    omega⟩
  infer_instance

theorem differential_intertwining
    (hmap : ∀ {s t : Finset ι} (h : s ⊆ t) (g : G) (v : D.Obj s),
      D.map h (ρ s g v) = ρ t g (D.map h v))
    (g : G) (x : D.Total) :
    D.differential (FiniteProduct.representation ρ g x) =
      FiniteProduct.representation ρ g (D.differential x) := by
  simp only [CutComplex.Diagram.differential_apply, map_sum,
    step_intertwining D ρ hmap]

theorem degreeDifferential_intertwining
    (hmap : ∀ {s t : Finset ι} (h : s ⊆ t) (g : G) (v : D.Obj s),
      D.map h (ρ s g v) = ρ t g (D.map h v))
    (k : ℕ) (g : G) (x : D.Degree k) :
    D.degreeDifferential k (FiniteProduct.representation (fun s => ρ s.1) g x) =
      FiniteProduct.representation (fun s => ρ s.1) g (D.degreeDifferential k x) := by
  apply D.extend_injective (k + 1)
  rw [CutComplex.Diagram.extend_degreeDifferential, extend_intertwining,
    extend_intertwining, differential_intertwining D ρ hmap,
    CutComplex.Diagram.extend_degreeDifferential]

end EquivariantDiagram

namespace ActualCutComplex

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual block shape with the specified interior cuts. -/
abbrev shape (s : Finset (Fin (n - 1))) : BlockShape n := (BlockShape.cutEquiv n).symm s

/-- The actual normalized induction--Jacquet carrier, indexed by its cuts. -/
abbrev Term (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (s : Finset (Fin (n - 1))) : Type (max uF uV) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.SmoothFunctions ((shape s).parabolic F.Carrier)
    (Transition.inducing T (shape s) ρ)

/-- The actual pointwise transition for inclusion of cut sets. -/
def transition (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {s t : Finset (Fin (n - 1))} (h : s ⊆ t) :
    (Transition.term T (shape s) ρ).IntertwiningMap (Transition.term T (shape t) ρ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Transition.cutMap T ρ (by simpa using h)

/-- The commuting cut diagram consists of the actual induced representations. -/
def diagram (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    CutComplex.Diagram (Fin (n - 1)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  { Obj := Term T ρ
    add _ := inferInstance
    module _ := inferInstance
    map h := (transition T ρ h).toLinearMap
    map_refl s := by
      change (Transition.cutMap T (B := shape s) ρ _).toLinearMap = _
      rw [Transition.cutMap_refl]
      rfl
    map_comp hst htu := by
      change ((transition T ρ htu).comp (transition T ρ hst)).toLinearMap = _
      change ((Transition.cutMap T ρ _).comp (Transition.cutMap T ρ _)).toLinearMap = _
      rw [Transition.cutMap_comp]
      rfl }

/-- The total product action, with the genuine action on each induced term. -/
def totalRepresentation (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (GeneralLinear n F.Carrier) (diagram T ρ).Total :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  FiniteProduct.representation (fun s => Transition.term T (shape s) ρ)

/-- The action on the homogeneous term indexed by sets of `k` cuts. -/
def degreeRepresentation (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    Representation ℂ (GeneralLinear n F.Carrier) ((diagram T ρ).Degree k) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  FiniteProduct.representation (fun s => Transition.term T (shape s.1) ρ)

@[simp]
theorem totalRepresentation_apply (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (g : GeneralLinear n F.Carrier) (x : (diagram T ρ).Total)
    (s : Finset (Fin (n - 1))) :
    totalRepresentation T ρ g x s = Transition.term T (shape s) ρ g (x s) := rfl

@[simp]
theorem degreeRepresentation_apply (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (g : GeneralLinear n F.Carrier) (x : (diagram T ρ).Degree k)
    (s : {s : Finset (Fin (n - 1)) // s.card = k}) :
    degreeRepresentation T ρ k g x s = Transition.term T (shape s.1) ρ g (x s) := rfl

theorem diagram_map_intertwining (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {s t : Finset (Fin (n - 1))} (h : s ⊆ t) (g : GeneralLinear n F.Carrier)
    (v : Term T ρ s) :
    (diagram T ρ).map h (Transition.term T (shape s) ρ g v) =
      Transition.term T (shape t) ρ g ((diagram T ρ).map h v) :=
  LinearMap.congr_fun ((transition T ρ h).isIntertwining' g) v

theorem step_intertwining (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (i : Fin (n - 1)) (g : GeneralLinear n F.Carrier) (x : (diagram T ρ).Total) :
    (diagram T ρ).step i (totalRepresentation T ρ g x) =
      totalRepresentation T ρ g ((diagram T ρ).step i x) :=
  EquivariantDiagram.step_intertwining (diagram T ρ)
    (fun s => Transition.term T (shape s) ρ) (diagram_map_intertwining T ρ) i g x

theorem differential_intertwining (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (g : GeneralLinear n F.Carrier) (x : (diagram T ρ).Total) :
    (diagram T ρ).differential (totalRepresentation T ρ g x) =
      totalRepresentation T ρ g ((diagram T ρ).differential x) :=
  EquivariantDiagram.differential_intertwining (diagram T ρ)
    (fun s => Transition.term T (shape s) ρ) (diagram_map_intertwining T ρ) g x

theorem extend_intertwining (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (g : GeneralLinear n F.Carrier) (x : (diagram T ρ).Degree k) :
    (diagram T ρ).extend k (degreeRepresentation T ρ k g x) =
      totalRepresentation T ρ g ((diagram T ρ).extend k x) :=
  EquivariantDiagram.extend_intertwining (diagram T ρ)
    (fun s => Transition.term T (shape s) ρ) k g x

theorem degreeDifferential_intertwining (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (g : GeneralLinear n F.Carrier) (x : (diagram T ρ).Degree k) :
    (diagram T ρ).degreeDifferential k (degreeRepresentation T ρ k g x) =
      degreeRepresentation T ρ (k + 1) g ((diagram T ρ).degreeDifferential k x) :=
  EquivariantDiagram.degreeDifferential_intertwining (diagram T ρ)
    (fun s => Transition.term T (shape s) ρ) (diagram_map_intertwining T ρ) k g x

/-- The genuine equivariant differential between consecutive degree terms. -/
def differential (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    (degreeRepresentation T ρ k).IntertwiningMap (degreeRepresentation T ρ (k + 1)) where
  toLinearMap := (diagram T ρ).degreeDifferential k
  isIntertwining' g := LinearMap.ext (fun x => degreeDifferential_intertwining T ρ k g x)

theorem differential_square (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) :
    (differential T ρ (k + 1)).comp (differential T ρ k) = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (diagram T ρ).degreeDifferential_square k x

/-- The complex is zero above the number of interior coordinates. -/
theorem degree_subsingleton (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (hk : n - 1 < k) : Subsingleton ((diagram T ρ).Degree k) :=
  EquivariantDiagram.degree_subsingleton_of_gt (diagram T ρ) k (by simpa using hk)

/-- Every actual degree representation is smooth. -/
theorem degree_isSmooth (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    letI := T.topology
    IsSmooth (degreeRepresentation T ρ k) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact FiniteProduct.isSmooth
    (fun s : {s : Finset (Fin (n - 1)) // s.card = k} => Transition.term T (shape s.1) ρ)
    (fun _ => Induction.smoothInduced_smooth _ _)

/-- The actual degree object in the category of smooth representations. -/
def degreeObject (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  SmoothRep.of (degreeRepresentation T ρ k) (degree_isSmooth T ρ k)

/-- The differential as a morphism of actual smooth representations. -/
def degreeMorphism (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    letI := T.topology
    degreeObject T ρ k ⟶ degreeObject T ρ (k + 1) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  SmoothRep.ofHom (differential T ρ k)

end ActualCutComplex
end Langlands.Aubert
