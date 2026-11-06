import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Topology.RestrictedProductSplit

/-!
# Splitting finite adelic general linear groups at finitely many places

For a decidable predicate `p` on the finite places satisfied by only finitely many places,
the finite adelic general linear group is identified, as a topological group, with the full
product of the local groups at the places satisfying `p` times the restricted product of the
local groups at the remaining places. The standard integral subgroup corresponds to the
product of the local integral subgroups and the subgroup of away families integral at every
remaining place.
-/

noncomputable section

universe u

namespace Langlands.Global.FiniteAdelicGL

open scoped RestrictedProduct

variable (K : Type u) [Field K] [NumberField K] (n : ℕ) (p : FinitePlace K → Prop)

/-- The restricted product of the finite local general linear groups at the places not
satisfying `p`. -/
abbrev AwayRestrictedProduct :=
  Πʳ v : {v : FinitePlace K // ¬ p v}, [FiniteLocalGL K n v, localIntegral K n v]

/-- The open subgroup of away families integral at every place not satisfying `p`. -/
def awayIntegral : OpenSubgroup (AwayRestrictedProduct K n p) where
  carrier := {x | ∀ v : {v : FinitePlace K // ¬ p v}, x v ∈ localIntegral K n v}
  one_mem' v := (localIntegral K n v).one_mem
  mul_mem' hx hy v := (localIntegral K n v).mul_mem (hx v) (hy v)
  inv_mem' hx v := (localIntegral K n v).inv_mem (hx v)
  isOpen' := RestrictedProduct.isOpen_forall_mem fun v => (localIntegral K n v).isOpen

@[simp]
theorem mem_awayIntegral (x : AwayRestrictedProduct K n p) :
    x ∈ awayIntegral K n p ↔ ∀ v : {v : FinitePlace K // ¬ p v}, x v ∈ localIntegral K n v :=
  Iff.rfl

variable [DecidablePred p] [Finite {v : FinitePlace K // p v}]

/-- The finite adelic general linear group is the full product of the local groups at the
finitely many places satisfying `p` times the restricted product at the remaining places. -/
def splitAtPlaces :
    FiniteAdelicGL K n ≃ₜ*
      (Π v : {v : FinitePlace K // p v}, FiniteLocalGL K n v) × AwayRestrictedProduct K n p :=
  (restrictedProductEquiv K n).trans
    (RestrictedProduct.splitFiniteContinuousMulEquiv _ _ p fun v => (localIntegral K n v).isOpen)

@[simp]
theorem splitAtPlaces_apply_fst (g : FiniteAdelicGL K n) (v : {v : FinitePlace K // p v}) :
    (splitAtPlaces K n p g).1 v = localProjection K n v g :=
  rfl

@[simp]
theorem splitAtPlaces_apply_snd (g : FiniteAdelicGL K n) (v : {v : FinitePlace K // ¬ p v}) :
    (splitAtPlaces K n p g).2 v = localProjection K n v g :=
  rfl

theorem localProjection_splitAtPlaces_symm_of_pos
    (z : (Π v : {v : FinitePlace K // p v}, FiniteLocalGL K n v) × AwayRestrictedProduct K n p)
    {v : FinitePlace K} (h : p v) :
    localProjection K n v ((splitAtPlaces K n p).symm z) = z.1 ⟨v, h⟩ := by
  change localProjection K n v ((restrictedProductEquiv K n).symm
    ((RestrictedProduct.splitFiniteContinuousMulEquiv _ _ p
      fun v => (localIntegral K n v).isOpen).symm z)) = _
  rw [← restrictedProductEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
  exact RestrictedProduct.splitFiniteContinuousMulEquiv_symm_apply_of_pos _ _ p _ z h

theorem localProjection_splitAtPlaces_symm_of_neg
    (z : (Π v : {v : FinitePlace K // p v}, FiniteLocalGL K n v) × AwayRestrictedProduct K n p)
    {v : FinitePlace K} (h : ¬ p v) :
    localProjection K n v ((splitAtPlaces K n p).symm z) = z.2 ⟨v, h⟩ := by
  change localProjection K n v ((restrictedProductEquiv K n).symm
    ((RestrictedProduct.splitFiniteContinuousMulEquiv _ _ p
      fun v => (localIntegral K n v).isOpen).symm z)) = _
  rw [← restrictedProductEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
  exact RestrictedProduct.splitFiniteContinuousMulEquiv_symm_apply_of_neg _ _ p _ z h

/-- A finite adelic matrix is standard integral exactly when its components at the places
satisfying `p` are locally integral and its away part is integral at every remaining place. -/
theorem mem_standardIntegral_iff_splitAtPlaces (g : FiniteAdelicGL K n) :
    g ∈ standardIntegral K n ↔
      (∀ v : {v : FinitePlace K // p v}, (splitAtPlaces K n p g).1 v ∈ localIntegral K n v) ∧
        (splitAtPlaces K n p g).2 ∈ awayIntegral K n p := by
  rw [mem_standardIntegral_iff_local]
  refine ⟨fun h => ⟨fun v => h v, (mem_awayIntegral K n p _).mpr fun v => h v⟩,
    fun h v => ?_⟩
  by_cases hv : p v
  · exact h.1 ⟨v, hv⟩
  · exact (mem_awayIntegral K n p _).mp h.2 ⟨v, hv⟩

/-- Splitting at the places satisfying `p` carries the standard integral subgroup onto the
product of the local integral subgroups at those places and the away integral subgroup. -/
theorem map_standardIntegral_splitAtPlaces :
    (standardIntegral K n).toSubgroup.map (splitAtPlaces K n p).toMonoidHom =
      (Subgroup.pi Set.univ fun v : {v : FinitePlace K // p v} =>
        (localIntegral K n v).toSubgroup).prod (awayIntegral K n p).toSubgroup := by
  ext z
  rw [Subgroup.mem_prod, Subgroup.mem_pi]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have h := (mem_standardIntegral_iff_splitAtPlaces K n p g).mp hg
    exact ⟨fun v _ => h.1 v, h.2⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨(splitAtPlaces K n p).symm z, ?_, (splitAtPlaces K n p).apply_symm_apply z⟩
    refine (mem_standardIntegral_iff_splitAtPlaces K n p _).mpr ?_
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact ⟨fun v => h₁ v (Set.mem_univ v), h₂⟩

end Langlands.Global.FiniteAdelicGL
