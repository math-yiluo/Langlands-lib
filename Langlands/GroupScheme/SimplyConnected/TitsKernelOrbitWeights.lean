import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights
import Langlands.GroupScheme.SimplyConnected.AnisotropicKernelStarRestriction

/-! # Full star orbit weights and the actual anisotropic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]

/-- Every vertex in the full star orbit of a zero vertex is a zero vertex. -/
theorem mem_zeroVertices_of_mem_starOrbitVertices (d : TitsIndexData G)
    {a b : d.Vertex} (hb : b ∈ d.starOrbitVertices a) :
    b ∈ d.zeroVertices ↔ a ∈ d.zeroVertices := by
  obtain ⟨σ, rfl⟩ := (d.mem_starOrbitVertices a b).mp hb
  exact titsIndexStarInvariant k G d σ a

/-- A full star orbit of simple vertices lies in the zero vertices or is
disjoint from them. -/
theorem starOrbitVertices_subset_zero_or_disjoint (d : TitsIndexData G) (a : d.Vertex) :
    (∀ b ∈ d.starOrbitVertices a, b ∈ d.zeroVertices) ∨
      (∀ b ∈ d.starOrbitVertices a, b ∉ d.zeroVertices) := by
  by_cases ha : a ∈ d.zeroVertices
  · exact Or.inl fun b hb => (d.mem_zeroVertices_of_mem_starOrbitVertices hb).mpr ha
  · exact Or.inr fun b hb hb0 =>
      ha ((d.mem_zeroVertices_of_mem_starOrbitVertices hb).mp hb0)

variable {d : TitsIndexData G} {e : TitsIndexData D} {ι : D ⟶ G}

/-- The kernel vertex equivalence carries full star orbits of kernel vertices
onto the full star orbits of the corresponding ambient zero vertices. -/
theorem KernelComparison.mem_starOrbitVertices_vertexEquiv_iff
    (h : d.KernelComparison ι e) (c c' : e.Vertex) :
    (h.vertexEquiv c').val ∈ d.starOrbitVertices (h.vertexEquiv c).val ↔
      c' ∈ e.starOrbitVertices c := by
  rw [d.mem_starOrbitVertices, e.mem_starOrbitVertices]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    apply h.vertexEquiv.injective
    apply Subtype.ext
    rw [h.vertexEquiv_star]
    exact hσ
  · rintro ⟨σ, rfl⟩
    refine ⟨σ, ?_⟩
    rw [h.vertexEquiv_star]
    rfl

/-- Every vertex in the full star orbit of an ambient zero vertex comes from
the full star orbit of the corresponding kernel vertex. -/
theorem KernelComparison.exists_of_mem_starOrbitVertices
    (h : d.KernelComparison ι e) (c : e.Vertex) {b : d.Vertex}
    (hb : b ∈ d.starOrbitVertices (h.vertexEquiv c).val) :
    ∃ c' ∈ e.starOrbitVertices c, (h.vertexEquiv c').val = b := by
  obtain ⟨σ, rfl⟩ := (d.mem_starOrbitVertices _ b).mp hb
  refine ⟨e.star σ c, (e.mem_starOrbitVertices c _).mpr ⟨σ, rfl⟩, ?_⟩
  rw [h.vertexEquiv_star]
  rfl

/-- The actual integral fundamental weight of a zero vertex restricts to the
actual integral fundamental weight of the corresponding kernel vertex. -/
theorem KernelComparison.weightRestriction_absoluteFundamentalCharacter_vertexEquiv
    (h : d.KernelComparison ι e) (hsc : IsSimplyConnected G)
    (hscD : IsSimplyConnected D) (c : e.Vertex) :
    h.weightRestriction (d.absoluteFundamentalCharacter hsc (h.vertexEquiv c).val) =
      e.absoluteFundamentalCharacter hscD c := by
  have hw := h.weightRestriction_fundamentalWeight_zero (d.pinning_corootSpan_eq_top hsc)
    (e.pinning_corootSpan_eq_top hscD) (h.vertexEquiv c)
  rw [Equiv.symm_apply_apply] at hw
  exact hw

/-- The actual integral fundamental weight of a distinguished vertex
restricts to zero on the kernel torus. -/
theorem KernelComparison.weightRestriction_absoluteFundamentalCharacter_distinguished
    (h : d.KernelComparison ι e) (hsc : IsSimplyConnected G)
    (hscD : IsSimplyConnected D) (b : d.Vertex) (hb : b ∉ d.zeroVertices) :
    h.weightRestriction (d.absoluteFundamentalCharacter hsc b) = 0 :=
  h.weightRestriction_fundamentalWeight_distinguished (d.pinning_corootSpan_eq_top hsc)
    (e.pinning_corootSpan_eq_top hscD) b hb

/-- Orbit formula inside the zero vertices: the restriction of the sum of
the actual integral fundamental weights over the full star orbit of the zero
vertex corresponding to a kernel vertex `c` is the matching orbit sum of the
actual kernel at `c`. -/
theorem KernelComparison.weightRestriction_absoluteOrbitWeight_vertexEquiv
    (h : d.KernelComparison ι e) (hsc : IsSimplyConnected G)
    (hscD : IsSimplyConnected D) (c : e.Vertex) :
    h.weightRestriction (d.absoluteOrbitWeight hsc (h.vertexEquiv c).val) =
      e.absoluteOrbitWeight hscD c := by
  classical
  unfold absoluteOrbitWeight
  rw [map_sum]
  symm
  refine Finset.sum_bij (fun c' _ => (h.vertexEquiv c').val) ?_ ?_ ?_ ?_
  · intro c' hc'
    exact (h.mem_starOrbitVertices_vertexEquiv_iff c c').mpr hc'
  · intro c₁ _ c₂ _ h12
    exact h.vertexEquiv.injective (Subtype.ext h12)
  · intro b hb
    obtain ⟨c', hc', rfl⟩ := h.exists_of_mem_starOrbitVertices c hb
    exact ⟨c', hc', rfl⟩
  · intro c' _
    exact (h.weightRestriction_absoluteFundamentalCharacter_vertexEquiv hsc hscD c').symm

/-- Orbit formula inside the zero vertices, indexed by an ambient zero vertex. -/
theorem KernelComparison.weightRestriction_absoluteOrbitWeight_of_zero
    (h : d.KernelComparison ι e) (hsc : IsSimplyConnected G)
    (hscD : IsSimplyConnected D) (a : d.zeroVertices) :
    h.weightRestriction (d.absoluteOrbitWeight hsc a.val) =
      e.absoluteOrbitWeight hscD (h.vertexEquiv.symm a) := by
  have hw := h.weightRestriction_absoluteOrbitWeight_vertexEquiv hsc hscD
    (h.vertexEquiv.symm a)
  rw [Equiv.apply_symm_apply] at hw
  exact hw

/-- Orbit formula outside the zero vertices: the sum of the actual integral
fundamental weights over a full star orbit of distinguished vertices restricts
to zero on the kernel torus. -/
theorem KernelComparison.weightRestriction_absoluteOrbitWeight_of_not_zero
    (h : d.KernelComparison ι e) (hsc : IsSimplyConnected G)
    (hscD : IsSimplyConnected D) (a : d.Vertex) (ha : a ∉ d.zeroVertices) :
    h.weightRestriction (d.absoluteOrbitWeight hsc a) = 0 := by
  classical
  unfold absoluteOrbitWeight
  rw [map_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  refine h.weightRestriction_absoluteFundamentalCharacter_distinguished hsc hscD b ?_
  intro hb0
  exact ha ((d.mem_zeroVertices_of_mem_starOrbitVertices hb).mp hb0)

/-- The exhaustive orbit dichotomy: every full star orbit either lies in the
zero vertices, where its weight restricts to the matching kernel orbit weight,
or is disjoint from them, where its weight restricts to zero. -/
theorem KernelComparison.weightRestriction_absoluteOrbitWeight_cases
    (h : d.KernelComparison ι e) (hsc : IsSimplyConnected G)
    (hscD : IsSimplyConnected D) (a : d.Vertex) :
    (∃ c : e.Vertex, (∀ b ∈ d.starOrbitVertices a, b ∈ d.zeroVertices) ∧
        (h.vertexEquiv c).val = a ∧
        h.weightRestriction (d.absoluteOrbitWeight hsc a) =
          e.absoluteOrbitWeight hscD c) ∨
      ((∀ b ∈ d.starOrbitVertices a, b ∉ d.zeroVertices) ∧
        h.weightRestriction (d.absoluteOrbitWeight hsc a) = 0) := by
  by_cases ha : a ∈ d.zeroVertices
  · refine Or.inl ⟨h.vertexEquiv.symm ⟨a, ha⟩, ?_, ?_, ?_⟩
    · exact fun b hb => (d.mem_zeroVertices_of_mem_starOrbitVertices hb).mpr ha
    · rw [Equiv.apply_symm_apply]
    · exact h.weightRestriction_absoluteOrbitWeight_of_zero hsc hscD ⟨a, ha⟩
  · refine Or.inr ⟨?_, h.weightRestriction_absoluteOrbitWeight_of_not_zero hsc hscD a ha⟩
    exact fun b hb hb0 => ha ((d.mem_zeroVertices_of_mem_starOrbitVertices hb).mp hb0)

open Classical in
/-- The explicit value of the restricted orbit weight at an ambient vertex `a`:
the kernel orbit weight at the corresponding kernel vertex when `a` is a zero
vertex, and zero otherwise. -/
def KernelComparison.restrictedOrbitWeight (h : d.KernelComparison ι e)
    (hscD : IsSimplyConnected D) (a : d.Vertex) :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        e.pinning.torus) :=
  if ha : a ∈ d.zeroVertices then e.absoluteOrbitWeight hscD (h.vertexEquiv.symm ⟨a, ha⟩)
  else 0

/-- The restriction of every full star orbit weight is given by the explicit
formula `KernelComparison.restrictedOrbitWeight`. -/
theorem KernelComparison.weightRestriction_absoluteOrbitWeight
    (h : d.KernelComparison ι e) (hsc : IsSimplyConnected G)
    (hscD : IsSimplyConnected D) (a : d.Vertex) :
    h.weightRestriction (d.absoluteOrbitWeight hsc a) = h.restrictedOrbitWeight hscD a := by
  classical
  unfold KernelComparison.restrictedOrbitWeight
  by_cases ha : a ∈ d.zeroVertices
  · simp only [ha, ↓reduceDIte]
    exact h.weightRestriction_absoluteOrbitWeight_of_zero hsc hscD ⟨a, ha⟩
  · simp only [ha, ↓reduceDIte]
    exact h.weightRestriction_absoluteOrbitWeight_of_not_zero hsc hscD a ha

end Langlands.GroupScheme.TitsIndexData

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G}

/-- The explicit restricted orbit weight for the actual anisotropic kernel of a
simply connected group. -/
def restrictedOrbitWeight (p : d.AnisotropicKernelIndex) (hsc : IsSimplyConnected G)
    (a : d.Vertex) :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        p.index.pinning.torus) :=
  p.comparison.restrictedOrbitWeight (p.isSimplyConnected hsc) a

/-- Restriction of a full star orbit weight to the actual anisotropic kernel is
the explicit restricted orbit weight. -/
theorem weightRestriction_absoluteOrbitWeight (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (a : d.Vertex) :
    p.weightRestriction (d.absoluteOrbitWeight hsc a) = p.restrictedOrbitWeight hsc a :=
  p.comparison.weightRestriction_absoluteOrbitWeight hsc (p.isSimplyConnected hsc) a

/-- Orbit formula for the actual anisotropic kernel inside the zero vertices. -/
theorem weightRestriction_absoluteOrbitWeight_of_zero (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (a : d.zeroVertices) :
    p.weightRestriction (d.absoluteOrbitWeight hsc a.val) =
      p.index.absoluteOrbitWeight (p.isSimplyConnected hsc)
        (p.comparison.vertexEquiv.symm a) :=
  p.comparison.weightRestriction_absoluteOrbitWeight_of_zero hsc (p.isSimplyConnected hsc) a

/-- Orbit formula for the actual anisotropic kernel outside the zero vertices. -/
theorem weightRestriction_absoluteOrbitWeight_of_not_zero (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (a : d.Vertex) (ha : a ∉ d.zeroVertices) :
    p.weightRestriction (d.absoluteOrbitWeight hsc a) = 0 :=
  p.comparison.weightRestriction_absoluteOrbitWeight_of_not_zero hsc
    (p.isSimplyConnected hsc) a ha

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex
