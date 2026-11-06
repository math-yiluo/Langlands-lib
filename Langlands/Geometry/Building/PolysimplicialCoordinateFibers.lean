import Langlands.Geometry.Building.AbstractBuilding

/-! # Coordinate-fiber criteria for polysimplicial isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Geometry.Building.AbstractBuilding

variable {ι : Type v} {ι' : Type v} {V : ι → Type u} {V' : ι' → Type w}

/-- The output coordinate `σ i` depends only on input coordinate `i`. -/
def RespectsCoordinateFibers (σ : ι ≃ ι')
    (e : (∀ i, V i) ≃ (∀ j, V' j)) : Prop :=
  ∀ i x y, x i = y i → e x (σ i) = e y (σ i)

namespace RespectsCoordinateFibers

variable {σ : ι ≃ ι'} {e : (∀ i, V i) ≃ (∀ j, V' j)}

local instance : DecidableEq ι := Classical.decEq ι
local instance : DecidableEq ι' := Classical.decEq ι'

/-- Vary a single coordinate in a fixed base vertex. -/
def coordinateMap (σ : ι ≃ ι') (e : (∀ i, V i) ≃ (∀ j, V' j))
    (a : ∀ i, V i) (i : ι) (z : V i) : V' (σ i) :=
  e (Function.update a i z) (σ i)

theorem coordinateMap_apply (he : RespectsCoordinateFibers σ e)
    (a x : ∀ i, V i) (i : ι) :
    coordinateMap σ e a i (x i) = e x (σ i) :=
  he i _ _ (Function.update_self _ _ _)

theorem coordinateMap_bijective (he : RespectsCoordinateFibers σ e)
    (a : ∀ i, V i) (i : ι) :
    Function.Bijective (coordinateMap σ e a i) := by
  constructor
  · intro z t hzt
    have H : Function.update a i z = Function.update a i t := by
      apply e.injective
      funext j
      obtain ⟨k, rfl⟩ := σ.surjective j
      by_cases hki : k = i
      · subst k
        exact hzt
      · apply he k
        simp [hki]
    have H' := congrArg (fun x => x i) H
    simpa only [Function.update_self] using H'
  · intro z
    obtain ⟨x, hx⟩ := e.surjective (Function.update (e a) (σ i) z)
    refine ⟨x i, ?_⟩
    rw [coordinateMap_apply he, hx, Function.update_self]

/-- A product bijection respecting coordinate fibers induces factor bijections. -/
def coordinateEquiv (he : RespectsCoordinateFibers σ e)
    (a : ∀ i, V i) (i : ι) : V i ≃ V' (σ i) :=
  Equiv.ofBijective (coordinateMap σ e a i) (coordinateMap_bijective he a i)

theorem coordinateEquiv_apply (he : RespectsCoordinateFibers σ e)
    (a x : ∀ i, V i) (i : ι) :
    coordinateEquiv he a i (x i) = e x (σ i) :=
  coordinateMap_apply he a x i

theorem coordinateEquiv_symm_apply (he : RespectsCoordinateFibers σ e)
    (a : ∀ i, V i) (y : ∀ j, V' j) (i : ι) :
    (coordinateEquiv he a i).symm (y (σ i)) = e.symm y i := by
  apply (coordinateEquiv he a i).injective
  rw [(coordinateEquiv he a i).apply_symm_apply, coordinateEquiv_apply,
    e.apply_symm_apply]

theorem piCongr_coordinateEquiv (he : RespectsCoordinateFibers σ e)
    (a : ∀ i, V i) :
    Equiv.piCongr σ (coordinateEquiv he a) = e := by
  apply Equiv.ext
  intro x
  funext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  rw [Equiv.piCongr_apply_apply]
  exact coordinateEquiv_apply he a x i

theorem eval_image_image (he : RespectsCoordinateFibers σ e)
    (a : ∀ i, V i) (A : Set (∀ i, V i)) (i : ι) :
    (fun y => y (σ i)) '' (e '' A) =
      coordinateEquiv he a i '' ((fun x => x i) '' A) := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  exact (coordinateEquiv_apply he a x i).symm

theorem eval_image_preimage (he : RespectsCoordinateFibers σ e)
    (a : ∀ i, V i) (A : Set (∀ j, V' j)) (i : ι) :
    (fun x => x i) '' (e ⁻¹' A) =
      coordinateEquiv he a i ⁻¹' ((fun y => y (σ i)) '' A) := by
  rw [← e.image_symm_eq_preimage, ← (coordinateEquiv he a i).image_symm_eq_preimage,
    Set.image_image, Set.image_image]
  apply Set.image_congr
  intro y _
  exact (coordinateEquiv_symm_apply he a y i).symm

variable [Finite ι] [Finite ι']
  {K : PolysimplicialComplex ι V} {L : PolysimplicialComplex ι' V'}

theorem coordinateEquiv_image_mem (he : RespectsCoordinateFibers σ e)
    (himage : ∀ A ∈ K.facets, e '' A ∈ L.facets)
    (a : ∀ i, V i) (i : ι) {s : Set (V i)} (hs : s ∈ (K.factor i).faces) :
    coordinateEquiv he a i '' s ∈ (L.factor (σ i)).faces := by
  let t : ∀ j, Set (V j) := Function.update (fun j => {a j}) i s
  have ht : ∀ j, t j ∈ (K.factor j).faces := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [t] using hs
    · simpa [t, hji] using (K.factor j).singleton_mem (a j)
  have hA := K.pi_mem_facets ht
  have H := (L.facetsOrderIso ⟨e '' Set.univ.pi t, himage _ hA⟩ (σ i)).property
  change (fun y => y (σ i)) '' (e '' Set.univ.pi t) ∈ (L.factor (σ i)).faces at H
  rw [eval_image_image he a, Set.eval_image_univ_pi
    (PolysimplicialComplex.nonempty_of_mem_facets hA)] at H
  simpa [t] using H

theorem coordinateEquiv_preimage_mem (he : RespectsCoordinateFibers σ e)
    (hpreimage : ∀ A ∈ L.facets, e ⁻¹' A ∈ K.facets)
    (a : ∀ i, V i) (i : ι) {s : Set (V' (σ i))} (hs : s ∈ (L.factor (σ i)).faces) :
    coordinateEquiv he a i ⁻¹' s ∈ (K.factor i).faces := by
  let t : ∀ j, Set (V' j) := Function.update (fun j => {e a j}) (σ i) s
  have ht : ∀ j, t j ∈ (L.factor j).faces := by
    intro j
    by_cases hji : j = σ i
    · subst j
      simpa [t] using hs
    · simpa [t, hji] using (L.factor j).singleton_mem (e a j)
  have hA := L.pi_mem_facets ht
  have H := (K.facetsOrderIso ⟨e ⁻¹' Set.univ.pi t, hpreimage _ hA⟩ i).property
  change (fun x => x i) '' (e ⁻¹' Set.univ.pi t) ∈ (K.factor i).faces at H
  rw [eval_image_preimage he a, Set.eval_image_univ_pi
    (PolysimplicialComplex.nonempty_of_mem_facets hA)] at H
  simpa [t] using H

/-- Facet preservation makes the induced coordinate bijections simplicial. -/
def toPolysimplicialIso (he : RespectsCoordinateFibers σ e)
    (himage : ∀ A ∈ K.facets, e '' A ∈ L.facets)
    (hpreimage : ∀ A ∈ L.facets, e ⁻¹' A ∈ K.facets)
    (a : ∀ i, V i) : PolysimplicialIso K L where
  perm := σ
  factorIso i := {
    toEquiv := coordinateEquiv he a i
    image_mem := fun _ hs => coordinateEquiv_image_mem he himage a i hs
    preimage_mem := fun _ hs => coordinateEquiv_preimage_mem he hpreimage a i hs }

theorem toPolysimplicialIso_vertexEquiv (he : RespectsCoordinateFibers σ e)
    (himage : ∀ A ∈ K.facets, e '' A ∈ L.facets)
    (hpreimage : ∀ A ∈ L.facets, e ⁻¹' A ∈ K.facets)
    (a : ∀ i, V i) :
    (toPolysimplicialIso he himage hpreimage a).vertexEquiv = e :=
  piCongr_coordinateEquiv he a

end RespectsCoordinateFibers

namespace PolysimplicialIso

variable [Finite ι] [Finite ι']
  {K : PolysimplicialComplex ι V} {L : PolysimplicialComplex ι' V'}

theorem respectsCoordinateFibers (φ : PolysimplicialIso K L) :
    RespectsCoordinateFibers φ.perm φ.vertexEquiv := by
  intro i x y hxy
  rw [vertexEquiv_apply_apply, vertexEquiv_apply_apply, hxy]

end PolysimplicialIso

/-- With facet preservation supplied, the remaining obstruction is a coordinate permutation
under which each output coordinate depends only on the matching input coordinate. -/
theorem exists_polysimplicialIso_iff_respectsCoordinateFibers [Finite ι] [Finite ι']
    {K : PolysimplicialComplex ι V} {L : PolysimplicialComplex ι' V'}
    (e : (∀ i, V i) ≃ (∀ j, V' j))
    (himage : ∀ A ∈ K.facets, e '' A ∈ L.facets)
    (hpreimage : ∀ A ∈ L.facets, e ⁻¹' A ∈ K.facets) :
    (∃ φ : PolysimplicialIso K L, φ.vertexEquiv = e) ↔
      ∃ σ : ι ≃ ι', RespectsCoordinateFibers σ e := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.perm, φ.respectsCoordinateFibers⟩
  · rintro ⟨σ, he⟩
    let a : ∀ i, V i := fun i => Classical.choice (K.factor i).nonempty_vertices
    exact ⟨he.toPolysimplicialIso himage hpreimage a,
      he.toPolysimplicialIso_vertexEquiv himage hpreimage a⟩

theorem isPolysimplicialAutomorphism_iff_respectsCoordinateFibers [Finite ι]
    (K : PolysimplicialComplex ι V) (e : (∀ i, V i) ≃ (∀ i, V i))
    (himage : ∀ A ∈ K.facets, e '' A ∈ K.facets)
    (hpreimage : ∀ A ∈ K.facets, e ⁻¹' A ∈ K.facets) :
    IsPolysimplicialAutomorphism K e ↔
      ∃ σ : Equiv.Perm ι, RespectsCoordinateFibers σ e :=
  exists_polysimplicialIso_iff_respectsCoordinateFibers e himage hpreimage

end Langlands.Geometry.Building.AbstractBuilding
