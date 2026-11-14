import Langlands.GroupScheme.Reductive.CommutingMultiplicationIsogeny

/-! # A closed coordinate projection of the commuting multiplication kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H K G : GroupScheme S}
variable (j : H ⟶ G) (i : K ⟶ G)
variable (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
  Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))

/-- The second coordinate of the full scheme-theoretic multiplication kernel. -/
def commutingMultiplicationKernelRightProjection :
    kernel (commutingSubgroupMultiplicationHom j i hc) ⟶ K :=
  kernelι (commutingSubgroupMultiplicationHom j i hc) ≫ snd H K

/-- The kernel is the pullback of the first inclusion along the inverse of the
second inclusion, as schemes over the original base. -/
theorem commutingMultiplicationKernelRightProjection_isPullback :
    IsPullback
      ((kernelι (commutingSubgroupMultiplicationHom j i hc)).hom.hom ≫ fst H.X K.X)
      (commutingMultiplicationKernelRightProjection j i hc).hom.hom
      j.hom.hom (i.hom.hom ≫ ι[G.X]) := by
  let f := commutingSubgroupMultiplicationHom j i hc
  have hk : (kernelι f).hom.hom ≫ f.hom.hom = 1 := by
    exact (kernel_isPullback f).w
  have hw : ((kernelι f).hom.hom ≫ fst H.X K.X) ≫ j.hom.hom =
      ((kernelι f).hom.hom ≫ snd H.X K.X) ≫ (i.hom.hom ≫ ι[G.X]) := by
    have hrel := mul_eq_one_iff_eq_inv.mp (show
        ((kernelι f).hom.hom ≫ fst H.X K.X ≫ j.hom.hom) *
          ((kernelι f).hom.hom ≫ snd H.X K.X ≫ i.hom.hom) = 1 by
      simpa only [f, commutingSubgroupMultiplicationHom_hom, subgroupMultiplication,
        MonObj.comp_mul] using hk)
    simpa only [Hom.inv_def, Category.assoc] using hrel
  let l := fun (c : PullbackCone j.hom.hom (i.hom.hom ≫ ι[G.X])) =>
    (kernel_isPullback f).lift (lift c.fst c.snd) (toUnit _) (by
      change lift c.fst c.snd ≫ subgroupMultiplication j i = 1
      rw [comp_subgroupMultiplication]
      have hrel : c.fst ≫ j.hom.hom = (c.snd ≫ i.hom.hom)⁻¹ := by
        simpa only [Hom.inv_def, Category.assoc] using c.condition
      rw [hrel, inv_mul_cancel])
  have hl (c : PullbackCone j.hom.hom (i.hom.hom ≫ ι[G.X])) :
      l c ≫ (kernelι f).hom.hom = lift c.fst c.snd :=
    (kernel_isPullback f).lift_fst _ _ _
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ l ?_ ?_ ?_⟩⟩
  · intro c
    rw [← Category.assoc, hl, lift_fst]
  · intro c
    change l c ≫ ((kernelι f).hom.hom ≫ snd H.X K.X) = c.snd
    rw [← Category.assoc, hl, lift_snd]
  · intro c m hm hn
    apply (cancel_mono (kernelι f).hom.hom).mp
    rw [hl]
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst] using hm
    · change m ≫ ((kernelι f).hom.hom ≫ snd H.X K.X) = c.snd at hn
      simpa only [Category.assoc, lift_snd] using hn

/-- A closed first factor makes the kernel's second projection closed. -/
theorem commutingMultiplicationKernelRightProjection_isClosedSubgroup
    (hj : IsClosedSubgroup j) :
    IsClosedSubgroup (commutingMultiplicationKernelRightProjection j i hc) := by
  change IsClosedImmersion (commutingMultiplicationKernelRightProjection j i hc).hom.hom.left
  exact MorphismProperty.of_isPullback
    ((commutingMultiplicationKernelRightProjection_isPullback j i hc).map (Over.forget S))
    (show IsClosedImmersion j.hom.hom.left from hj)

/-- If the second factor is monomorphic, the kernel projects into its full centre. -/
theorem commutingMultiplicationKernelRightProjection_isCentral [Mono i.hom.hom] :
    IsCentral (commutingMultiplicationKernelRightProjection j i hc) := by
  apply (isCentral_iff_range_le_center _).mpr
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  change (y ≫ (kernelι (commutingSubgroupMultiplicationHom j i hc)).hom.hom) ≫
    snd H.X K.X ∈ (center K).carrier T
  exact commutingSubgroupMultiplication_right_mem_center j i hc _
    (kernelPointsEquiv _ T y).property

/-- The full multiplication kernel is finite if the second factor has finite
full centre. No finiteness of the first factor's centre is required. -/
theorem kernel_commutingSubgroupMultiplicationHom_isFinite_of_right_finiteCenter
    (hj : IsClosedSubgroup j) [Mono i.hom.hom] (hK : HasFiniteCenter K) :
    IsFinite (kernel (commutingSubgroupMultiplicationHom j i hc)).X.hom :=
  isFinite_of_isClosedSubgroup_of_isCentral_of_hasFiniteCenter
    (commutingMultiplicationKernelRightProjection j i hc)
    (commutingMultiplicationKernelRightProjection_isClosedSubgroup j i hc hj)
    (commutingMultiplicationKernelRightProjection_isCentral j i hc) hK

end Langlands.GroupScheme
