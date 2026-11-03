import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition

/-! Exact subgroup and projection identities for rational standard induction in stages. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General

namespace IsSemidirectDecomposition

variable {H : Type u} [Group H] {P M U Q : Subgroup H}

/-- A subgroup between the radical and the parabolic is preserved by the
actual Levi projection. -/
theorem projection_mem_of_radical_le (h : IsSemidirectDecomposition P M U)
    (hQP : Q ≤ P) (hUQ : U ≤ Q) (q : Q) :
    (h.projection ⟨q, hQP q.property⟩ : H) ∈ Q := by
  have hu := h.projection_inv_mul_mem ⟨q, hQP q.property⟩
  have hm := Q.mul_mem q.property (Q.inv_mem (hUQ hu))
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hm

/-- Such a subgroup is exactly the inverse image of its intersection with the
Levi, under the actual projection. -/
theorem subgroupOf_eq_comap_projection (h : IsSemidirectDecomposition P M U)
    (hQP : Q ≤ P) (hUQ : U ≤ Q) :
    Q.subgroupOf P = (Q.subgroupOf M).comap h.projection := by
  ext p
  constructor
  · intro hp
    exact h.projection_mem_of_radical_le hQP hUQ ⟨p, hp⟩
  · intro hm
    change (h.projection p : H) ∈ Q at hm
    have hu := hUQ (h.projection_inv_mul_mem p)
    have hp : (h.projection p : H) *
        ((h.projection p : H)⁻¹ * (p : H)) ∈ Q := Q.mul_mem hm hu
    change (p : H) ∈ Q
    simpa only [mul_inv_cancel_left] using hp

/-- Restriction along the actual Levi section gives the literal subgroup
intersection used inside the Levi. -/
theorem subgroupOf_comap_levi (h : IsSemidirectDecomposition P M U) :
    (Q.subgroupOf P).comap (Subgroup.inclusion h.levi_le) = Q.subgroupOf M := rfl

/-- The two actual projections compose for nested radicals and Levis. -/
theorem projection_stages {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup H}
    (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
    (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
    (hL : IsSemidirectDecomposition
      (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
    (hP : P₀ ≤ P₁) (hM : M₀ ≤ M₁) (hU : U₁ ≤ U₀) (p : P₀) :
    Subgroup.subgroupOfEquivOfLe hM
        (hL.projection
          ⟨h₁.projection ⟨p, hP p.property⟩,
            h₁.projection_mem_of_radical_le hP (hU.trans h₀.unipotent_le) p⟩) =
      h₀.projection p := by
  symm
  rw [h₀.projection_eq_iff]
  let q : P₀.subgroupOf M₁ :=
    ⟨h₁.projection ⟨p, hP p.property⟩,
      h₁.projection_mem_of_radical_le hP (hU.trans h₀.unipotent_le) p⟩
  change ((hL.projection q : M₁) : H)⁻¹ * (p : H) ∈ U₀
  have ha : ((hL.projection q : M₁) : H)⁻¹ * ((q : M₁) : H) ∈ U₀ :=
    hL.projection_inv_mul_mem q
  have hb : ((q : M₁) : H)⁻¹ * (p : H) ∈ U₀ :=
    hU (h₁.projection_inv_mul_mem ⟨p, hP p.property⟩)
  have hab := U₀.mul_mem ha hb
  simpa only [mul_assoc, mul_inv_cancel_left] using hab

/-- The composite Levi projection constructed from the two stages. -/
def stageProjection {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup H}
    (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
    (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
    (hL : IsSemidirectDecomposition
      (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
    (hP : P₀ ≤ P₁) (hM : M₀ ≤ M₁) (hU : U₁ ≤ U₀) : P₀ →* M₀ :=
  (Subgroup.subgroupOfEquivOfLe hM).toMonoidHom.comp
    (hL.projection.comp
      ((h₁.projection.comp (Subgroup.inclusion hP)).codRestrict
        (P₀.subgroupOf M₁)
        (fun p => h₁.projection_mem_of_radical_le hP
          (hU.trans h₀.unipotent_le) p)))

/-- Uniqueness identifies the constructed composite with the finer projection. -/
theorem stageProjection_eq {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup H}
    (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
    (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
    (hL : IsSemidirectDecomposition
      (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
    (hP : P₀ ≤ P₁) (hM : M₀ ≤ M₁) (hU : U₁ ≤ U₀) :
    stageProjection h₀ h₁ hL hP hM hU = h₀.projection := by
  apply MonoidHom.ext
  intro p
  exact projection_stages h₀ h₁ hL hP hM hU p

end IsSemidirectDecomposition

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hInter hG hi hν

/-- The given rational radical product, on the exact finite root labels. -/
theorem unipotent_product_of_subset (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    (unipotent i ν I : Set (RationalPoint k G.X)) =
      (levi i ν J ⊓ unipotent i ν I : Set (RationalPoint k G.X)) *
        (unipotent i ν J : Set (RationalPoint k G.X)) :=
  (hInter k G hG T i hi ν hν (rootSet i ν I) (rootSet i ν J)
    (rootSet_subset i ν I) (rootSet_subset i ν J)
    ((rootSet_subset_iff i ν I J).mpr hIJ)).2

/-- Standard Levis are nested, as a consequence of the named all-test
intersection statement. -/
theorem levi_le_of_subset (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    levi i ν I ≤ levi i ν J := by
  have h := (hInter k G hG T i hi ν hν (rootSet i ν I) (rootSet i ν J)
    (rootSet_subset i ν I) (rootSet_subset i ν J)
    ((rootSet_subset_iff i ν I J).mpr hIJ)).1 (Over.mk (𝟙 _))
  exact fun _ hm => (h.2.1 hm).1

/-- The larger standard subset has the smaller radical. -/
theorem unipotent_le_of_subset (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    unipotent i ν J ≤ unipotent i ν I := by
  intro x hx
  change x ∈ (unipotent i ν I : Set (RationalPoint k G.X))
  rw [unipotent_product_of_subset i ν hInter hG hi hν I J hIJ]
  exact Set.mem_mul.mpr ⟨1, (levi i ν J ⊓ unipotent i ν I).one_mem, x, hx, one_mul x⟩

/-- Each finer radical lies in the coarser parabolic. -/
theorem unipotent_le_parabolic_of_subset
    (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    unipotent i ν I ≤ parabolic i ν J := by
  intro x hx
  change x ∈ (unipotent i ν I : Set (RationalPoint k G.X)) at hx
  rw [unipotent_product_of_subset i ν hInter hG hi hν I J hIJ] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
  exact (parabolic i ν J).mul_mem (levi_le_parabolic i ν J ha.1)
    (unipotent_le_parabolic i ν J hb)

variable (hStandard : StandardCocharacterStatement.{u})

include hStandard

/-- The actual standard parabolic subgroups are nested. -/
theorem parabolic_le_of_subset (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    parabolic i ν I ≤ parabolic i ν J := by
  intro x hx
  let hI := isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν I
  let p : parabolic i ν I := ⟨x, hx⟩
  have hm := (levi_le_parabolic i ν J)
    (levi_le_of_subset i ν hInter hG hi hν I J hIJ (hI.projection p).property)
  have hu := unipotent_le_parabolic_of_subset i ν hInter hG hi hν I J hIJ
    (hI.projection_inv_mul_mem p)
  simpa only [mul_inv_cancel_left] using (parabolic i ν J).mul_mem hm hu

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

/-- The exact fine parabolic inside the coarse one is the inverse image of
its literal intersection with the coarse Levi. -/
theorem parabolic_subgroupOf_eq_comap_projection
    (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    (parabolic i ν I).subgroupOf (parabolic i ν J) =
      ((parabolic i ν I).subgroupOf (levi i ν J)).comap (dec J).projection :=
  (dec J).subgroupOf_eq_comap_projection
    (parabolic_le_of_subset i ν hInter hG hi hν hStandard I J hIJ)
    ((unipotent_le_of_subset i ν hInter hG hi hν I J hIJ).trans
      (unipotent_le_parabolic i ν I))

/-- The kernel of the coarse projection is contained in the exact fine
parabolic inside the coarse parabolic. -/
theorem projection_ker_le_parabolic_subgroupOf
    (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    (dec J).projection.ker ≤ (parabolic i ν I).subgroupOf (parabolic i ν J) := by
  intro p hp
  exact unipotent_le_parabolic i ν I
    (unipotent_le_of_subset i ν hInter hG hi hν I J hIJ
      (((dec J).projection_eq_one_iff p).mp hp))

/-- Actual ambient and inside-Levi projections compose, for the literal
`Finset J` family used in the rational Aubert target. -/
theorem standardLeviProjection_stages
    (J : Finset (SimpleRoot i ν)) (I : Finset J)
    (p : parabolic i ν (leviIndex J I)) :
    Subgroup.subgroupOfEquivOfLe
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
        (standardLeviProjection i ν hInter hG hi hν J I
          ⟨(dec J).projection
              ⟨p, parabolic_le_of_subset i ν hInter hG hi hν hStandard
                _ J (leviIndex_subset J I) p.property⟩,
            (dec J).projection_mem_of_radical_le
              (parabolic_le_of_subset i ν hInter hG hi hν hStandard
                _ J (leviIndex_subset J I))
              ((unipotent_le_of_subset i ν hInter hG hi hν
                _ J (leviIndex_subset J I)).trans
                (unipotent_le_parabolic i ν (leviIndex J I))) p⟩) =
      (dec (leviIndex J I)).projection p :=
  IsSemidirectDecomposition.projection_stages
    (dec (leviIndex J I)) (dec J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (parabolic_le_of_subset i ν hInter hG hi hν hStandard
      _ J (leviIndex_subset J I))
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (unipotent_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I)) p

end RationalPointFamily

end Langlands.Aubert.General
