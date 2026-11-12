import Langlands.BruhatTits.SpecialCompact.ContractionPredicates
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.GroupScheme.Rational.PointTopology

/-! # Literal radical intersections under powers of a contracting element -/

noncomputable section

universe u

open Set Filter Topology CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {H : Type*} [Group H]

/-- The actual image of the literal intersection under conjugation by `m^n`. -/
def conjugatePowerIntersection (K U : Subgroup H) (m : H) (n : ℕ) : Subgroup H :=
  (K ⊓ U).map (MulAut.conj (m ^ n)).toMonoidHom

theorem coe_conjugatePowerIntersection (K U : Subgroup H) (m : H) (n : ℕ) :
    (conjugatePowerIntersection K U m n : Set H) =
      ambientConjugate (m ^ n) ((K ⊓ U : Subgroup H) : Set H) := rfl

variable [TopologicalSpace H]

/-- Pointwise contraction exhausts a normalized subgroup by expanding
conjugates of any open ambient subgroup's literal intersection. -/
theorem iUnion_expanding_conjugate_intersection
    (K U : Subgroup H) (m : H) (hK : IsOpen (K : Set H))
    (hconj : ∀ n : ℕ, ∀ x ∈ U, m ^ n * x * (m ^ n)⁻¹ ∈ U)
    (hinv : ∀ n : ℕ, ∀ x ∈ U, (m ^ n)⁻¹ * x * m ^ n ∈ U)
    (hlim : ∀ x ∈ U,
      Tendsto (fun n : ℕ => m ^ n * x * (m ^ n)⁻¹) atTop (𝓝 1)) :
    (U : Set H) =
      ⋃ n : ℕ, ambientConjugate ((m ^ n)⁻¹)
        ((K ⊓ U : Subgroup H) : Set H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := ((hlim x hx).eventually (hK.mem_nhds K.one_mem)).exists
    refine mem_iUnion.mpr ⟨n, ?_⟩
    refine ⟨m ^ n * x * (m ^ n)⁻¹, ⟨hn, hconj n x hx⟩, ?_⟩
    simp only [inv_inv]
    group
  · intro hx
    obtain ⟨n, y, hy, rfl⟩ := mem_iUnion.mp hx
    change (m ^ n)⁻¹ * y * ((m ^ n)⁻¹)⁻¹ ∈ U
    simpa only [inv_inv] using hinv n y hy.2

variable [IsTopologicalGroup H]

/-- Uniform contraction of compact subsets gives the precise intrinsic power
neighborhood basis used in the simultaneous-basis predicate. -/
theorem conjugatePowerNeighborhoodBasis_of_uniform_contraction
    (K U : Subgroup H) (m : H)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H))
    (hUc : IsClosed (U : Set H))
    (hconj : ∀ n : ℕ, ∀ x ∈ U, m ^ n * x * (m ^ n)⁻¹ ∈ U)
    (hinv : ∀ n : ℕ, ∀ x ∈ U, (m ^ n)⁻¹ * x * m ^ n ∈ U)
    (hlim : ∀ C : Set H, IsCompact C → C ⊆ U →
      ∀ W ∈ 𝓝 (1 : H),
        ∀ᶠ n : ℕ in atTop, ∀ x ∈ C, m ^ n * x * (m ^ n)⁻¹ ∈ W) :
    ConjugatePowerNeighborhoodBasis K U m := by
  refine ⟨fun n x hx => ?_, hasBasis_iff.mpr ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hx
    exact hconj n y hy.2
  · intro W
    constructor
    · intro hW
      rw [nhds_subtype_eq_comap] at hW
      obtain ⟨V, hV, hVW⟩ := mem_comap.mp hW
      have hcompact : IsCompact ((K : Set H) ∩ U) := hKc.inter_right hUc
      obtain ⟨n, hn⟩ := (hlim _ hcompact inter_subset_right V hV).exists
      refine ⟨n, trivial, ?_⟩
      rintro x ⟨y, hy, heq⟩
      apply hVW
      change (x : H) ∈ V
      rw [heq]
      exact hn y ⟨hy, y.property⟩
    · rintro ⟨n, _, hnW⟩
      have hc : Continuous (fun x : U => (m ^ n)⁻¹ * (x : H) * m ^ n) := by
        fun_prop
      have hn : {x : U | (m ^ n)⁻¹ * (x : H) * m ^ n ∈ K} ∈ 𝓝 (1 : U) :=
        hc.continuousAt.preimage_mem_nhds (by simpa using hKo.mem_nhds K.one_mem)
      refine mem_of_superset hn ?_
      intro x hx
      apply hnW
      refine ⟨⟨(m ^ n)⁻¹ * (x : H) * m ^ n, hinv n x x.property⟩, hx, ?_⟩
      change (x : H) = m ^ n * ((m ^ n)⁻¹ * (x : H) * m ^ n) * (m ^ n)⁻¹
      group

end Groups

section Dynamic

open Langlands.GroupScheme
open Langlands.GroupScheme.Dynamic
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- Every positive or negative power of a cocharacter value normalizes its
actual dynamic unipotent radical. -/
theorem cocharPoint_pow_conj_mem (t : Fˣ) (n : ℕ)
    (x : rationalPoints G) (hx : x ∈ unipotentPoints χ) :
    cocharPoint χ t ^ n * x * (cocharPoint χ t ^ n)⁻¹ ∈ unipotentPoints χ := by
  exact conj_mem_unipotent χ
    (((parabolic χ).carrier (Over.mk (𝟙 _))).pow_mem
      (centralizer_le_parabolic χ _ (cocharPoint_mem_centralizer χ t)) n) hx

theorem cocharPoint_inv_pow_conj_mem (t : Fˣ) (n : ℕ)
    (x : rationalPoints G) (hx : x ∈ unipotentPoints χ) :
    (cocharPoint χ t ^ n)⁻¹ * x * cocharPoint χ t ^ n ∈ unipotentPoints χ := by
  have h := conj_mem_unipotent χ
    (((parabolic χ).carrier (Over.mk (𝟙 _))).inv_mem
      (((parabolic χ).carrier (Over.mk (𝟙 _))).pow_mem
        (centralizer_le_parabolic χ _ (cocharPoint_mem_centralizer χ t)) n)) hx
  simpa only [inv_inv] using h

variable [TopologicalSpace F] [IsTopologicalRing F] [IsAffine G.X.left]

local instance contractingPowerBasisPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- For any open ambient subgroup, every point of the actual dynamic radical
lies in an expanding conjugate of its literal intersection. -/
theorem dynamic_iUnion_expanding_intersection
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (K : Subgroup (rationalPoints G)) (hK : IsOpen (K : Set (rationalPoints G))) :
    (unipotentPoints χ : Set (rationalPoints G)) =
      ⋃ n : ℕ, ambientConjugate ((cocharPoint χ t ^ n)⁻¹)
        ((K ⊓ unipotentPoints χ : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) := by
  have hp : ∀ x ∈ unipotentPoints χ,
      Tendsto (fun n : ℕ => cocharPoint χ t ^ n * x *
        (cocharPoint χ t ^ n)⁻¹) atTop (𝓝 1) := by
    intro x hx
    apply tendsto_def.mpr
    intro W hW
    have hsub : ({x} : Set (rationalPoints G)) ⊆ unipotentPoints χ := by
      intro y hy
      rcases mem_singleton_iff.mp hy with rfl
      exact hx
    filter_upwards [eventually_cocharPoint_pow_conj_mem_ambient χ t ht
      {x} isCompact_singleton hsub W hW] with n hn
    exact hn x (mem_singleton x)
  exact iUnion_expanding_conjugate_intersection (H := rationalPoints G)
    K (unipotentPoints χ) (cocharPoint χ t) hK
    (cocharPoint_pow_conj_mem χ t) (cocharPoint_inv_pow_conj_mem χ t) hp

variable [T2Space F] [IsTopologicalGroup (rationalPoints G)]

/-- For any compact open ambient subgroup, contracting powers of its literal
intersection with the actual dynamic radical form an intrinsic identity basis. -/
theorem dynamic_conjugatePowerNeighborhoodBasis
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (K : Subgroup (rationalPoints G))
    (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G))) :
    ConjugatePowerNeighborhoodBasis K (unipotentPoints χ) (cocharPoint χ t) := by
  exact conjugatePowerNeighborhoodBasis_of_uniform_contraction K (unipotentPoints χ)
    (cocharPoint χ t) hKo hKc (isClosed_unipotentPoints χ)
    (cocharPoint_pow_conj_mem χ t) (cocharPoint_inv_pow_conj_mem χ t)
    (eventually_cocharPoint_pow_conj_mem_ambient χ t ht)

/-- The two dynamic radicals satisfy both power clauses at the same original
cocharacter point and every compact open ambient subgroup. -/
theorem dynamic_power_basis_and_exhaustion
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (K : Subgroup (rationalPoints G))
    (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G))) :
    StrictChamberExhaustion K (unipotentPoints χ)
      (unipotentPoints (inverseCocharacter χ)) {cocharPoint χ t} ∧
    StrictChamberNeighborhoodBases K (unipotentPoints χ)
      (unipotentPoints (inverseCocharacter χ)) {cocharPoint χ t} := by
  constructor
  · rintro m (rfl : m = cocharPoint χ t)
    refine ⟨dynamic_iUnion_expanding_intersection χ t ht K hKo, ?_⟩
    simpa only [cocharPoint_inverseCocharacter, inv_pow, inv_inv] using
      dynamic_iUnion_expanding_intersection (inverseCocharacter χ) t ht K hKo
  · rintro m (rfl : m = cocharPoint χ t)
    refine ⟨dynamic_conjugatePowerNeighborhoodBasis χ t ht K hKo hKc, ?_⟩
    simpa only [cocharPoint_inverseCocharacter] using
      dynamic_conjugatePowerNeighborhoodBasis (inverseCocharacter χ) t ht K hKo hKc

end Dynamic

end Langlands.BruhatTits.SpecialCompact
