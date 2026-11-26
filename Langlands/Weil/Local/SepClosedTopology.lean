import Langlands.Weil.Local.Assembly
import Langlands.Galois.Local.ResidueProjectionInertia
import Langlands.Topology.Nonarchimedean.Subgroup

/-!
# Topology and unramified characters of the local Weil group of a separable closure

For a nonarchimedean local field `K` of either characteristic and a separable closure `Ω`
of `K`, this file proves the topological and character-theoretic facts about
`localWeilGroup K Ω` that the generic finite-image and unramified-reduction theorems
consume: the Krull topology of `Ω ≃ₐ[K] Ω` is nonarchimedean, Hausdorff and compact,
the projection to `Ω ≃ₐ[K] Ω` has dense image, the inertia subgroup is open and
compact, the Weil group is nonarchimedean, and a complex character trivial on inertia
is the unramified character given by its value at the chosen geometric Frobenius.
-/

noncomputable section

namespace Langlands.Weil.Local.SepClosed

open Topology

universe uK uΩ

section Galois

variable (K : Type uK) [Field K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]

/-- The Krull topology of `Ω ≃ₐ[K] Ω` has a basis of open subgroups at the identity. -/
theorem absoluteGalois_nonarchimedean : NonarchimedeanGroup (Ω ≃ₐ[K] Ω) :=
  ⟨fun U hU => by
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp hU
    let := hE
    exact ⟨⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩, hEU⟩⟩

variable [IsSepClosure K Ω]

/-- The Krull topology of `Ω ≃ₐ[K] Ω` is Hausdorff. -/
theorem absoluteGalois_t2Space : T2Space (Ω ≃ₐ[K] Ω) :=
  krullTopology_t2

/-- The Krull topology of `Ω ≃ₐ[K] Ω` is compact. -/
theorem absoluteGalois_compactSpace : CompactSpace (Ω ≃ₐ[K] Ω) :=
  inferInstance

end Galois

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]

/-- The residue degree of the separable closure is an open map. -/
theorem localResidueDegree_isOpenMap : IsOpenMap (localResidueDegree K Ω) :=
  (Galois.FiniteField.profiniteEquivalence (localResidueField K)).toHomeomorph.isOpenMap.comp
    (LocalGalois.SepClosed.isOpenMap_absoluteResidueHom K Ω)

/-- The projection of the Weil group to `Ω ≃ₐ[K] Ω` has dense image. -/
theorem localProjection_denseRange : DenseRange (localProjection K Ω) := by
  have hr : Set.range (localProjection K Ω) =
      (localResidueDegree K Ω) ⁻¹' Set.range frobenius := by
    exact congrArg (fun S : Subgroup (Ω ≃ₐ[K] Ω) => (S : Set (Ω ≃ₐ[K] Ω)))
      (projection_range (localResidueDegree K Ω))
  change Dense (Set.range (localProjection K Ω))
  rw [hr]
  exact (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).preimage
    (localResidueDegree_isOpenMap K Ω)

/-- The degree-zero subgroup of the Weil group is open. -/
theorem localInertia_isOpen : IsOpen (localInertia K Ω : Set (localWeilGroup K Ω)) :=
  (topologyProperties (Ω ≃ₐ[K] Ω) (localResidueDegree K Ω)).2.2.1

/-- The degree-zero subgroup of the Weil group is compact. -/
theorem localInertia_isCompact : IsCompact (localInertia K Ω : Set (localWeilGroup K Ω)) := by
  have hrange : Set.range (inertiaInclusion (localResidueDegree K Ω)) =
      (localInertia K Ω : Set (localWeilGroup K Ω)) :=
    congrArg (fun S : Subgroup (localWeilGroup K Ω) => (S : Set (localWeilGroup K Ω)))
      (inertiaInclusion_range (localResidueDegree K Ω))
  have hclosed : IsClosed ((inertia (localResidueDegree K Ω) : Subgroup (Ω ≃ₐ[K] Ω)) :
      Set (Ω ≃ₐ[K] Ω)) :=
    isClosed_singleton.preimage (localResidueDegree K Ω).continuous
  have : CompactSpace (inertia (localResidueDegree K Ω)) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  rw [← hrange]
  exact isCompact_range (inertiaInclusion (localResidueDegree K Ω)).continuous

private theorem degree_nonarchimedean : NonarchimedeanGroup Degree where
  is_nonarchimedean U hU := by
    refine ⟨⟨⊥, isOpen_discrete _⟩, ?_⟩
    intro n hn
    have hn' : n = 1 := hn
    simpa only [hn'] using mem_of_mem_nhds hU

/-- The Weil group of the separable closure is a nonarchimedean topological group. -/
theorem localWeilGroup_nonarchimedean : NonarchimedeanGroup (localWeilGroup K Ω) := by
  have := absoluteGalois_nonarchimedean K Ω
  have := degree_nonarchimedean
  exact Langlands.subgroupNonarchimedean (pullbackSubgroup (localResidueDegree K Ω))

/-- The projection of a degree-zero Weil element lies in absolute inertia. -/
theorem localProjection_mem_absoluteInertia {w : localWeilGroup K Ω}
    (hw : w ∈ localInertia K Ω) :
    localProjection K Ω w ∈ LocalGalois.SepClosed.absoluteInertia K Ω := by
  rw [← localResidueDegree_ker K Ω]
  change localResidueDegree K Ω (localProjection K Ω w) = 1
  have hw' : localDegree K Ω w = 1 := hw
  rw [show localResidueDegree K Ω (localProjection K Ω w) =
    Weil.frobenius (localDegree K Ω w) from w.property, hw', map_one]

/-- Absolute inertia is the image of degree-zero Weil elements. -/
theorem localProjection_localInertiaInclusion
    (i : LocalGalois.SepClosed.absoluteInertia K Ω) :
    localProjection K Ω (localInertiaInclusion K Ω i) = i := rfl

/-- The inclusion of absolute inertia lands in degree zero. -/
theorem localInertiaInclusion_mem (i : LocalGalois.SepClosed.absoluteInertia K Ω) :
    localInertiaInclusion K Ω i ∈ localInertia K Ω := rfl

/-- Unramified characters are trivial on inertia. -/
theorem localUnramifiedCharacter_on_inertia (z : ℂˣ) {w : localWeilGroup K Ω}
    (hw : w ∈ localInertia K Ω) : localUnramifiedCharacter K Ω z w = 1 :=
  unramifiedCharacter_on_kernel (localDegree K Ω) z hw

/-- The unramified character with parameter `z` takes the value `z` at geometric Frobenius. -/
theorem localUnramifiedCharacter_geometricFrobenius (z : ℂˣ) :
    localUnramifiedCharacter K Ω z (localGeometricFrobenius K Ω) = z :=
  unramifiedCharacter_degree_one (localDegree K Ω) z (localGeometricFrobenius_degree K Ω)

/-- A complex character of the Weil group that is trivial on inertia is the unramified
character given by its value at the chosen geometric Frobenius. -/
theorem localUnramifiedCharacter_eq_of_on_inertia (χ : localWeilGroup K Ω →* ℂˣ)
    (hχ : ∀ w ∈ localInertia K Ω, χ w = 1) :
    (localUnramifiedCharacter K Ω (χ (localGeometricFrobenius K Ω))).toMonoidHom = χ := by
  apply MonoidHom.ext
  intro g
  have hd : localDegree K Ω (localGeometricFrobenius K Ω ^ localDegreeInt K Ω g) =
      localDegree K Ω g := by
    rw [map_zpow, localGeometricFrobenius_degree]
    apply Multiplicative.toAdd.injective
    simp [localDegreeInt]
  have hi : g / localGeometricFrobenius K Ω ^ localDegreeInt K Ω g ∈ localInertia K Ω := by
    change localDegree K Ω (g / localGeometricFrobenius K Ω ^ localDegreeInt K Ω g) = 1
    rw [map_div, hd, div_self']
  have hc := hχ _ hi
  have hg : χ g / χ (localGeometricFrobenius K Ω) ^ localDegreeInt K Ω g = 1 := by
    simpa using hc
  change χ (localGeometricFrobenius K Ω) ^ localDegreeInt K Ω g = χ g
  exact (div_eq_one.mp hg).symm

end Langlands.Weil.Local.SepClosed
