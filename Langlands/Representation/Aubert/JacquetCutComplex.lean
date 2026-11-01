import Langlands.Representation.Aubert.FiniteProductCoinvariants

/-! The actual normalized Jacquet image of the cut complex. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear
open scoped BigOperators

universe uF uV uI

namespace EquivariantDiagram

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (C : BlockShape n)
  {ι : Type uI} [LinearOrder ι] (D : CutComplex.Diagram.{uI,uV} ι)
  (ρ : ∀ s, Representation ℂ (GeneralLinear n F.Carrier) (D.Obj s))
  (hmap : ∀ {s t : Finset ι} (h : s ⊆ t) (g : GeneralLinear n F.Carrier)
    (v : D.Obj s), D.map h (ρ s g v) = ρ t g (D.map h v))

/-- Actual normalized Jacquet quotients of an equivariant cut diagram. -/
def jacquetDiagram : CutComplex.Diagram ι where
  Obj s := C.JacquetModule (ρ s)
  add _ := inferInstance
  module _ := inferInstance
  map h := (T.normalizedJacquetMap C
    { toLinearMap := D.map h
      isIntertwining' g := LinearMap.ext (hmap h g) }).toLinearMap
  map_refl s := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := C.jacquetMk_surjective (ρ s) x
    change C.jacquetMk (ρ s) (D.map Finset.Subset.rfl v) = C.jacquetMk (ρ s) v
    rw [D.map_refl]
    rfl
  map_comp {s t u} hst htu := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := C.jacquetMk_surjective (ρ s) x
    change C.jacquetMk (ρ u) (D.map htu (D.map hst v)) =
      C.jacquetMk (ρ u) (D.map (hst.trans htu) v)
    rw [D.map_map]

end EquivariantDiagram

namespace ActualCutComplex

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (C : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Apply the actual normalized Jacquet functor to each term and transition. -/
def jacquetDiagram (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    CutComplex.Diagram (Fin (n - 1)) :=
  EquivariantDiagram.jacquetDiagram T C (diagram T ρ)
    (fun s => Transition.term T (shape s) ρ) (diagram_map_intertwining T ρ)

theorem jacquetDiagram_map
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {s t : Finset (Fin (n - 1))} (h : s ⊆ t) :
    (jacquetDiagram T C ρ).map h =
      (T.normalizedJacquetMap C (transition T ρ h)).toLinearMap := rfl

@[simp]
theorem jacquetDiagram_map_mk
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {s t : Finset (Fin (n - 1))} (h : s ⊆ t) (v : Term T ρ s) :
    (jacquetDiagram T C ρ).map h (C.jacquetMk (Transition.term T (shape s) ρ) v) =
      C.jacquetMk (Transition.term T (shape t) ρ) ((diagram T ρ).map h v) := rfl

/-- The actual coordinate quotient maps on total cut families. -/
def totalQuotient (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    (diagram T ρ).Total →ₗ[ℂ] (jacquetDiagram T C ρ).Total :=
  LinearMap.piMap (fun s => C.jacquetMk (Transition.term T (shape s) ρ))

@[simp]
theorem totalQuotient_apply (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (x : (diagram T ρ).Total) (s : Finset (Fin (n - 1))) :
    totalQuotient T C ρ x s = C.jacquetMk (Transition.term T (shape s) ρ) (x s) := rfl

/-- The actual coordinate quotient maps on homogeneous families. -/
def degreeQuotient (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    (diagram T ρ).Degree k →ₗ[ℂ] (jacquetDiagram T C ρ).Degree k :=
  LinearMap.piMap (fun s => C.jacquetMk (Transition.term T (shape s.1) ρ))

@[simp]
theorem degreeQuotient_apply (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (x : (diagram T ρ).Degree k)
    (s : {s : Finset (Fin (n - 1)) // s.card = k}) :
    degreeQuotient T C ρ k x s =
      C.jacquetMk (Transition.term T (shape s.1) ρ) (x s) := rfl

/-- Passing to actual quotients commutes with extension by zero. -/
theorem totalQuotient_extend (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (x : (diagram T ρ).Degree k) :
    totalQuotient T C ρ ((diagram T ρ).extend k x) =
      (jacquetDiagram T C ρ).extend k (degreeQuotient T C ρ k x) := by
  funext s
  by_cases hs : s.card = k
  · simp only [totalQuotient_apply, CutComplex.Diagram.extend_apply, hs, ↓reduceDIte,
      degreeQuotient_apply]
    rfl
  · simp only [totalQuotient_apply, CutComplex.Diagram.extend_apply, hs, ↓reduceDIte]
    exact (C.jacquetMk (Transition.term T (shape s) ρ)).map_zero

theorem degreeQuotient_restrict (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (x : (diagram T ρ).Total) :
    degreeQuotient T C ρ k ((diagram T ρ).restrict k x) =
      (jacquetDiagram T C ρ).restrict k (totalQuotient T C ρ x) := rfl

/-- Each actual signed insertion commutes with the coordinate quotient maps. -/
theorem totalQuotient_step (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (i : Fin (n - 1)) (x : (diagram T ρ).Total) :
    totalQuotient T C ρ ((diagram T ρ).step i x) =
      (jacquetDiagram T C ρ).step i (totalQuotient T C ρ x) := by
  funext s
  by_cases hi : i ∈ s
  · simp only [totalQuotient_apply, CutComplex.Diagram.step_apply, hi, ↓reduceIte]
    exact (C.jacquetMk (Transition.term T (shape s) ρ)).map_smul
      (CutComplex.sign s i) ((diagram T ρ).map (Finset.erase_subset i s) (x (s.erase i)))
  · simp only [totalQuotient_apply, CutComplex.Diagram.step_apply, hi, ↓reduceIte]
    exact (C.jacquetMk (Transition.term T (shape s) ρ)).map_zero

theorem totalQuotient_differential
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (x : (diagram T ρ).Total) :
    totalQuotient T C ρ ((diagram T ρ).differential x) =
      (jacquetDiagram T C ρ).differential (totalQuotient T C ρ x) := by
  simp only [CutComplex.Diagram.differential_apply, map_sum, totalQuotient_step]

/-- The actual homogeneous quotient maps commute with the signed differential. -/
theorem degreeQuotient_differential
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (x : (diagram T ρ).Degree k) :
    degreeQuotient T C ρ (k + 1) ((diagram T ρ).degreeDifferential k x) =
      (jacquetDiagram T C ρ).degreeDifferential k (degreeQuotient T C ρ k x) := by
  change degreeQuotient T C ρ (k + 1)
    ((diagram T ρ).restrict (k + 1) ((diagram T ρ).differential
      ((diagram T ρ).extend k x))) = _
  rw [degreeQuotient_restrict, totalQuotient_differential, totalQuotient_extend]
  rfl

/-- The Jacquet module of the actual degree product is the homogeneous Jacquet diagram. -/
def jacquetDegreeEquiv (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    C.JacquetModule (degreeRepresentation T ρ k) ≃ₗ[ℂ] (jacquetDiagram T C ρ).Degree k :=
  FiniteProduct.jacquetEquiv C
    (fun s : {s : Finset (Fin (n - 1)) // s.card = k} =>
      Transition.term T (shape s.1) ρ)

@[simp]
theorem jacquetDegreeEquiv_mk
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (x : (diagram T ρ).Degree k) :
    jacquetDegreeEquiv T C ρ k (C.jacquetMk (degreeRepresentation T ρ k) x) =
      degreeQuotient T C ρ k x := by
  funext s
  exact FiniteProduct.jacquetEquiv_mk C
    (fun s : {s : Finset (Fin (n - 1)) // s.card = k} =>
      Transition.term T (shape s.1) ρ) x s

/-- The genuine normalized Levi action on each homogeneous Jacquet family. -/
def jacquetDegreeRepresentation
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    Representation ℂ (C.Levi F.Carrier) ((jacquetDiagram T C ρ).Degree k) :=
  FiniteProduct.representation
    (fun s => T.normalizedJacquet C (Transition.term T (shape s.1) ρ))

theorem jacquetDegreeEquiv_intertwining
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (m : C.Levi F.Carrier) (x : C.JacquetModule (degreeRepresentation T ρ k)) :
    jacquetDegreeEquiv T C ρ k (T.normalizedJacquet C (degreeRepresentation T ρ k) m x) =
      jacquetDegreeRepresentation T C ρ k m (jacquetDegreeEquiv T C ρ k x) :=
  FiniteProduct.jacquetEquiv_intertwining C (T.leviModulus C)
    (fun s : {s : Finset (Fin (n - 1)) // s.card = k} =>
      Transition.term T (shape s.1) ρ) m x

/-- The degree equivalences compare the actual normalized Jacquet differential. -/
theorem jacquetDegreeEquiv_differential
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (k : ℕ) (x : C.JacquetModule (degreeRepresentation T ρ k)) :
    jacquetDegreeEquiv T C ρ (k + 1) (T.normalizedJacquetMap C (differential T ρ k) x) =
      (jacquetDiagram T C ρ).degreeDifferential k (jacquetDegreeEquiv T C ρ k x) := by
  obtain ⟨v, rfl⟩ := C.jacquetMk_surjective (degreeRepresentation T ρ k) x
  change jacquetDegreeEquiv T C ρ (k + 1)
    (C.jacquetMk (degreeRepresentation T ρ (k + 1))
      ((diagram T ρ).degreeDifferential k v)) = _
  rw [jacquetDegreeEquiv_mk, jacquetDegreeEquiv_mk]
  exact degreeQuotient_differential T C ρ k v

end ActualCutComplex
end Langlands.Aubert
