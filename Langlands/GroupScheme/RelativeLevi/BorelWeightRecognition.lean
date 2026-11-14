import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.BorelIdentityComponent
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Lie.FiniteDimensional

/-! # Recognizing Borel subgroups by the absence of opposite weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section WeightImage

variable {R : CommRingCat.{u}} {P G : GroupScheme (Spec R)}
  {T : CommGroupScheme (Spec R)}
  [IsAffineHom P.X.hom] [IsAffineHom G.X.hom]

/-- For a monomorphic subgroup, a nonzero intrinsic weight is equivalent to a
nonzero ambient weight vector in its actual Lie image. -/
theorem weightSpace_ne_bot_iff_exists_lieKernel_image
    (i : P ⟶ G) [Mono i.hom.hom] (f : T.toGrp ⟶ P)
    (α : characterLattice T) :
    weightSpace f α ≠ ⊥ ↔
      ∃ X ∈ weightSpace (f ≫ i) α, X ≠ 0 ∧
        ∃ Y : lieKernel P R, Y.val ≫ i.hom.hom = X.toMul.val := by
  constructor
  · intro h
    obtain ⟨Y, hY, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine ⟨Lie.targetMapLinear i R Y,
      lieKernelHomLinear_mem_weightSpace i f α hY, ?_, Y.toMul, rfl⟩
    intro h0
    apply hY0
    apply Lie.targetMapLinear_injective i R
    simpa only [map_zero] using h0
  · rintro ⟨X, hX, hX0, Y, hY⟩ hbot
    have hmap : Lie.targetMapLinear i R (Additive.ofMul Y) = X := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hY
    have hmem : Additive.ofMul Y ∈ weightSpace f α :=
      (lieKernelHomLinear_mem_weightSpace_iff i f α _).mp (hmap.symm ▸ hX)
    rw [hbot, Submodule.mem_bot] at hmem
    apply hX0
    rw [← hmap, hmem, map_zero]

end WeightImage

section Field

variable {k : Type u} [Field k]
  {P G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom P.X.hom] [IsAffineHom G.X.hom]

/-- A Borel through a split maximal torus has no pair of opposite nonzero
intrinsic adjoint weights. -/
theorem IsBorelSubgroup.no_opposite_weights
    (hG : IsConnectedReductive G) (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus (f ≫ i))
    (hi : IsBorelSubgroup i) :
    ∀ α : characterLattice T, α ≠ 0 →
      weightSpace f α = ⊥ ∨ weightSpace f (-α) = ⊥ := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  intro α hα
  by_cases hpos : weightSpace f α = ⊥
  · exact Or.inl hpos
  · right
    by_contra hneg
    obtain ⟨X, hX, hX0, hXP⟩ :=
      (weightSpace_ne_bot_iff_exists_lieKernel_image i f α).mp hpos
    have hroot : α ∈ roots (f ≫ i) := by
      refine ⟨hα, ?_⟩
      intro hbot
      rw [hbot, Submodule.mem_bot] at hX
      exact hX0 hX
    exact rankOneSolvableObstruction k G hG T (f ≫ i) hT hj P i f
      hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isSolvableGroupScheme rfl
      α hroot ⟨⟨X, hX, hX0, hXP⟩,
        (weightSpace_ne_bot_iff_exists_lieKernel_image i f (-α)).mp hneg⟩

variable [IsAlgClosed k]

/-- Over an algebraically closed field, a parabolic containing a split maximal
torus of the ambient reductive group is Borel exactly when its intrinsic Lie
algebra has no pair of opposite nonzero character weights. -/
theorem isBorelSubgroup_iff_no_opposite_weights
    (hG : IsConnectedReductive G) (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus (f ≫ i))
    (hi : IsParabolicSubgroup i) :
    IsBorelSubgroup i ↔
      ∀ α : characterLattice T, α ≠ 0 →
        weightSpace f α = ⊥ ∨ weightSpace f (-α) = ⊥ := by
  constructor
  · exact IsBorelSubgroup.no_opposite_weights hG i f hT hj
  · intro hno
    have : Smooth G.X.hom := hG.smooth
    have : ConnectedSpace G.X.left := hG.connectedSpace
    have : Smooth P.X.hom := hi.smooth
    have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    obtain ⟨B, b, c, hb, hc⟩ := hi.exists_isBorelSubgroup_factor
    have : ConnectedSpace P.X.left :=
      borelContainingSubgroupConnectedStatement k G P B i b c
        hi.isClosedSubgroup hi.smooth hb hc
    let d := BorelExistence.borelPairInOvergroupData (f ≫ i) i f hT hj
      hi.isClosedSubgroup rfl
      (borelSubgroupsAreConjugate_of_borelConjugacy borelConjugacy)
      ⟨B, c, hc.symm ▸ hb⟩
    have htorus : d.torusFactor ≫ (d.inclusion ≫ i) = f ≫ i := by
      rw [← Category.assoc, d.torusFactor_comp]
    obtain ⟨ν, _, hrep⟩ := (regularCocharacterBorel k G hG T (f ≫ i) hT hj).2.2
      d.subgroup (d.inclusion ≫ i) d.torusFactor d.isBorelSubgroup htorus
    have hobs : ∀ α ∈ roots (f ≫ i),
        ¬ ((∃ X ∈ weightSpace (f ≫ i) α, X ≠ 0 ∧
            ∃ Y : lieKernel P k, Y.val ≫ i.hom.hom = X.toMul.val) ∧
          (∃ X ∈ weightSpace (f ≫ i) (-α), X ≠ 0 ∧
            ∃ Y : lieKernel P k, Y.val ≫ i.hom.hom = X.toMul.val)) := by
      intro α hroot hboth
      have hpos := (weightSpace_ne_bot_iff_exists_lieKernel_image i f α).mpr hboth.1
      have hneg := (weightSpace_ne_bot_iff_exists_lieKernel_image i f (-α)).mpr hboth.2
      rcases hno α hroot.1 with h | h
      · exact hpos h
      · exact hneg h
    have : IsIso d.inclusion :=
      isIso_of_comp_eq_of_isRepresentedBy_parabolic dynamicLie dynamicSmooth
        lieSubgroupEquality hT (f ≫ i) ν
        (neg_mem_roots_of_relativeRootNegation relativeRootNegation hG hT (f ≫ i) hj)
        (d.inclusion ≫ i) d.isBorelSubgroup.isClosedSubgroup hrep i d.inclusion
        hi.isClosedSubgroup hobs rfl
    have htransport := d.isBorelSubgroup.iso_comp (asIso d.inclusion).symm
    change IsBorelSubgroup
      ((asIso d.inclusion).inv ≫ ((asIso d.inclusion).hom ≫ i)) at htransport
    simpa only [Iso.inv_hom_id_assoc] using htransport

/-- The Borel recognition criterion expressed by finite weight dimensions. -/
theorem isBorelSubgroup_iff_no_opposite_weight_finranks
    (hG : IsConnectedReductive G) (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus (f ≫ i))
    (hi : IsParabolicSubgroup i) :
    IsBorelSubgroup i ↔
      ∀ α : characterLattice T, α ≠ 0 →
        Module.finrank k (weightSpace f α) = 0 ∨
          Module.finrank k (weightSpace f (-α)) = 0 := by
  have : Smooth P.X.hom := hi.smooth
  simpa only [Submodule.finrank_eq_zero] using
    isBorelSubgroup_iff_no_opposite_weights hG i f hT hj hi

end Field

namespace splitTorus

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] [IsAlgClosed k]
  {P G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom P.X.hom] [IsAffineHom G.X.hom]

/-- Standard integral coordinates express Borel recognition directly as
the absence of opposite nonzero entries in the full weight-dimension profile. -/
theorem isBorelSubgroup_iff_no_opposite_exponent_weight_finranks
    (I : Type u) [Fintype I] (hG : IsConnectedReductive G)
    (i : P ⟶ G) (f : splitTorus (Spec (CommRingCat.of k)) I ⟶ P)
    (hj : IsMaximalTorus (T := commGroupScheme _ I) (f ≫ i))
    (hi : IsParabolicSubgroup i) :
    IsBorelSubgroup i ↔
      ∀ m : I → ℤ, m ≠ 0 →
        Module.finrank k (weightSpace f ((characterLatticeEquiv k I).symm m)) = 0 ∨
          Module.finrank k
            (weightSpace f ((characterLatticeEquiv k I).symm (-m))) = 0 := by
  rw [isBorelSubgroup_iff_no_opposite_weight_finranks
    (T := commGroupScheme _ I) hG i f
    (isSplitTorus_splitTorus I) hj hi]
  constructor
  · intro h m hm
    have hα : (characterLatticeEquiv k I).symm m ≠ 0 :=
      fun hz => hm ((characterLatticeEquiv k I).symm.map_eq_zero_iff.mp hz)
    rw [(characterLatticeEquiv k I).symm.map_neg m]
    exact h ((characterLatticeEquiv k I).symm m) hα
  · intro h α hα
    have hm : characterLatticeEquiv k I α ≠ 0 :=
      fun hz => hα ((characterLatticeEquiv k I).map_eq_zero_iff.mp hz)
    have hpos := (characterLatticeEquiv k I).symm_apply_apply α
    have hneg :
        (characterLatticeEquiv k I).symm (-(characterLatticeEquiv k I α)) = -α :=
      ((characterLatticeEquiv k I).symm.map_neg _).trans (congrArg Neg.neg hpos)
    let rank (β : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :=
      Module.finrank k (weightSpace f β)
    rcases h (characterLatticeEquiv k I α) hm with hp | hn
    · exact Or.inl ((congrArg rank hpos).symm.trans hp)
    · exact Or.inr ((congrArg rank hneg).symm.trans hn)

end splitTorus

end Langlands.GroupScheme
