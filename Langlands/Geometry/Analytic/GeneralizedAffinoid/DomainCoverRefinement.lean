import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! # Composition and refinement of actual finite full-domain covers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory CategoryTheory.Limits Topology
open scoped BigOperators

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : PresentedAffinoidAlgebra K} {V : Domain K A}

/-- A finite indexed family of actual restrictions with pointwise coverage
gives a cover in the fixed finite-ordinal representation. -/
def ofFintype {ι : Type v} [Fintype ι] (obj : ι → Domain K A)
    (map : ∀ i, obj i ⟶ V)
    (covers : ∀ x ∈ V.locus, ∃ i, x ∈ (obj i).locus) : FiniteCover V where
  size := Fintype.card ι
  obj i := obj ((Fintype.equivFin ι).symm i)
  map i := map ((Fintype.equivFin ι).symm i)
  covers x hx := by
    obtain ⟨i, hi⟩ := covers x hx
    exact ⟨Fintype.equivFin ι i, by simpa only [Equiv.symm_apply_apply] using hi⟩

/-- A refinement remembers its choice of a coarser component and the actual
bounded restriction from each finer component. -/
structure Refinement (d c : FiniteCover V) where
  index : Fin d.size → Fin c.size
  map : ∀ j, d.obj j ⟶ c.obj (index j)

namespace Refinement

variable {a b c d : FiniteCover V}

/-- With a fixed index function, uniqueness of actual domain restrictions
determines the entire refinement. -/
@[ext] theorem ext {r s : Refinement d c} (h : r.index = s.index) : r = s := by
  cases r with
  | mk ri rm =>
    cases s with
    | mk si sm =>
      dsimp at h
      cases h
      congr 1
      funext j
      exact (inferInstance : Subsingleton (Inclusion _ _)).elim _ _

def id (c : FiniteCover V) : Refinement c c where
  index i := i
  map i := 𝟙 (c.obj i)

def comp (r : Refinement a b) (s : Refinement b c) : Refinement a c where
  index i := s.index (r.index i)
  map i := r.map i ≫ s.map (r.index i)

/-- Refinement arrows commute with the actual restrictions to the target. -/
theorem over_target (r : Refinement d c) (i : Fin d.size) :
    r.map i ≫ c.map (r.index i) = d.map i :=
  (inferInstance : Subsingleton (Inclusion _ _)).elim _ _

/-- Every cover refines the concrete singleton identity cover. -/
def toSingleton (c : FiniteCover V) : Refinement c (singleton V) where
  index _ := ⟨0, by change 0 < 1; decide⟩
  map i := c.map i

/-- Send each actual finer representing spectrum through its bounded restriction
to the chosen coarser representing spectrum. -/
def spectrumMap (r : Refinement d c) :
    C((Σ j : Fin d.size, BanachSpectrum (d.obj j).algebra),
      (Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra)) where
  toFun x := ⟨r.index x.1, (r.map x.1).spectrumMap x.2⟩
  continuous_toFun := continuous_sigma fun j =>
    (continuous_sigmaMk
      (σ := fun i : Fin c.size => BanachSpectrum (c.obj i).algebra)
      (i := r.index j)).comp (r.map j).spectrumMap.continuous

/-- The spectrum map of a refinement lies over the original target locus. -/
theorem spectrumMap_over_target (r : Refinement d c) :
    c.totalMap.comp r.spectrumMap = d.totalMap := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (c.obj (r.index x.1)).spectrumMap ((r.map x.1).spectrumMap x.2) =
    (d.obj x.1).spectrumMap x.2
  exact (r.map x.1).spectrumMap_over_base x.2

end Refinement

/-- Finite covers form a category whose morphisms retain their index choices. -/
instance : Category (FiniteCover V) where
  Hom d c := Refinement d c
  id c := Refinement.id c
  comp r s := Refinement.comp r s
  id_comp _ := Refinement.ext rfl
  comp_id _ := Refinement.ext rfl
  assoc _ _ _ := Refinement.ext rfl

/-- The identity singleton is terminal in the cover refinement category. -/
def singletonIsTerminal (V : Domain K A) : IsTerminal (singleton V) :=
  IsTerminal.ofUniqueHom (fun c => Refinement.toSingleton c) (fun _ r => by
    apply Refinement.ext
    funext i
    exact (inferInstance : Subsingleton (Fin 1)).elim _ _)

/-- Compose a finite cover with one supplied finite cover of each component.
Every component is already a full domain in the same ambient spectrum. -/
def bind (c : FiniteCover V) (d : ∀ i : Fin c.size, FiniteCover (c.obj i)) :
    FiniteCover V :=
  ofFintype
    (fun ij : Σ i : Fin c.size, Fin (d i).size => (d ij.1).obj ij.2)
    (fun ij => (d ij.1).map ij.2 ≫ c.map ij.1)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := c.covers x hx
      obtain ⟨j, hj⟩ := (d i).covers x hi
      exact ⟨⟨i, j⟩, hj⟩)

/-- The number of components is the sum of the supplied component counts. -/
@[simp] theorem bind_size (c : FiniteCover V)
    (d : ∀ i : Fin c.size, FiniteCover (c.obj i)) :
    (c.bind d).size = ∑ i, (d i).size := by
  simp [bind, ofFintype, Fintype.card_sigma]

/-- The index of a specified inner component in the composed finite cover. -/
def bindIndex (c : FiniteCover V)
    (d : ∀ i : Fin c.size, FiniteCover (c.obj i))
    (i : Fin c.size) (j : Fin (d i).size) : Fin (c.bind d).size :=
  Fintype.equivFin (Σ i : Fin c.size, Fin (d i).size) ⟨i, j⟩

@[simp] theorem bind_obj_bindIndex (c : FiniteCover V)
    (d : ∀ i : Fin c.size, FiniteCover (c.obj i))
    (i : Fin c.size) (j : Fin (d i).size) :
    (c.bind d).obj (c.bindIndex d i j) = (d i).obj j := by
  exact congrArg
    (fun ij : Σ i : Fin c.size, Fin (d i).size => (d ij.1).obj ij.2)
    ((Fintype.equivFin (Σ i : Fin c.size, Fin (d i).size)).symm_apply_apply ⟨i, j⟩)

/-- The composed cover canonically refines its outer cover using the actual
inner restriction maps. -/
def bindRefinement (c : FiniteCover V)
    (d : ∀ i : Fin c.size, FiniteCover (c.obj i)) :
    Refinement (c.bind d) c where
  index k := ((Fintype.equivFin (Σ i : Fin c.size, Fin (d i).size)).symm k).1
  map k :=
    let ij := (Fintype.equivFin (Σ i : Fin c.size, Fin (d i).size)).symm k
    (d ij.1).map ij.2

@[simp] theorem bindRefinement_index (c : FiniteCover V)
    (d : ∀ i : Fin c.size, FiniteCover (c.obj i))
    (i : Fin c.size) (j : Fin (d i).size) :
    (c.bindRefinement d).index (c.bindIndex d i j) = i := by
  simp [bindRefinement, bindIndex]

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
