import Langlands.GroupScheme.Lie.RootOrbitFixedReconstruction
import Langlands.GroupScheme.Lie.WeightGaloisFixedDescent

/-! # Actual relative weights from a whole Galois root fiber -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section RootFiberDecomposition

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A nonzero restricted weight is the sum of precisely the actual root
weight spaces having that restriction. Zero weight spaces can be discarded. -/
theorem weightSpace_comp_eq_iSup_roots
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0) :
    weightSpace (CommGroupScheme.groupHom f ≫ j) a =
      ⨆ β : {β : roots j // f ≫ β.val = a}, weightSpace j β.val.val := by
  classical
  rw [weightSpace_comp_eq_iSup hT hS f j a]
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    by_cases hχ : weightSpace j χ.val = ⊥
    · rw [hχ]
      exact bot_le
    · have hχ0 : χ.val ≠ 0 := by
        intro hz
        apply ha
        rw [← χ.property, hz]
        simp
      exact le_iSup_of_le ⟨⟨χ.val, hχ0, hχ⟩, χ.property⟩ le_rfl
  · refine iSup_le fun β => ?_
    exact le_iSup_of_le ⟨β.val.val, β.property⟩ le_rfl

end RootFiberDecomposition

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (j : T.toGrp ⟶ G) (f : S ⟶ T) (a : characterLattice S)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "f_L" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f
local notation "a_L" => characterLattice.baseChange b S a

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local instance : LocallyOfFiniteType (G_L).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- If an ordinary root orbit is the whole restriction fiber, its literal
ambient span equals the entire actual base-changed relative weight space. -/
theorem rootOrbitWeightSpan_eq_weightSpace
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp) (ha : a ≠ 0)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a) :
    rootOrbitWeightSpan k L j β =
      weightSpace ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom f ≫ j)) a_L := by
  have haL : a_L ≠ 0 :=
    (characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha
  rw [CategoryTheory.Functor.map_comp]
  change rootOrbitWeightSpan k L j β =
    weightSpace (CommGroupScheme.groupHom f_L ≫ j_L) a_L
  rw [weightSpace_comp_eq_iSup_roots hT (hS.baseChange b) f_L j_L a_L haL]
  change (⨆ γ : MulAction.orbit (L ≃ₐ[k] L) β, weightSpace j_L γ.val.val) = _
  apply le_antisymm
  · refine iSup_le fun γ => ?_
    have hγ : γ.val ∈ rootRestrictionFiber k L j f a := by
      rw [← horbit]
      exact γ.property
    exact le_iSup_of_le ⟨γ.val, hγ⟩ le_rfl
  · refine iSup_le fun γ => ?_
    have hγ : γ.val ∈ MulAction.orbit (L ≃ₐ[k] L) β := by
      rw [horbit]
      exact γ.property
    exact le_iSup_of_le ⟨γ.val, hγ⟩ le_rfl

/-- The equality of actual ambient weight submodules identifies their exact
canonical Galois-fixed carriers, preserving the underlying Lie vector. -/
def rootOrbitFixedWeightSpaceEquiv
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp) (ha : a ≠ 0)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a) :
    rootOrbitFixedSpan k L j β ≃+
      Lie.baseChangeFixedWeightSpace k L (CommGroupScheme.groupHom f ≫ j) a := by
  let e := rootOrbitWeightSpan_eq_weightSpace k L j f a hS hT ha β horbit
  exact
    { toFun := fun x => ⟨⟨x.val.val, e.le x.val.property⟩, x.property⟩
      invFun := fun x => ⟨⟨x.val.val, e.ge x.val.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

@[simp]
theorem rootOrbitFixedWeightSpaceEquiv_val
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp) (ha : a ≠ 0)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (x : rootOrbitFixedSpan k L j β) :
    (rootOrbitFixedWeightSpaceEquiv k L j f a hS hT ha β horbit x).val.val =
      x.val.val := rfl

variable [FiniteDimensional k L] [IsGalois k L]

/-- Under the whole-fiber hypothesis, the actual stabilizer field gives
additive coordinates on the entire original relative weight space. -/
def rootOrbitFieldWeightSpaceEquiv
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp) (ha : a ≠ 0)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a) :
    rootOrbitField k L j β ≃+ weightSpace (CommGroupScheme.groupHom f ≫ j) a :=
  ((rootOrbitFieldFixedSpanEquiv k L j hG hj hT β).trans
    (rootOrbitFixedWeightSpaceEquiv k L j f a hS hT ha β horbit)).trans
      (Lie.weightSpaceGaloisFixedEquiv k L (CommGroupScheme.groupHom f ≫ j) a hS).symm

/-- Extending the constructed original vector recovers its literal fixed
ambient orbit vector. -/
theorem rootOrbitFieldWeightSpaceEquiv_baseChange
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp) (ha : a ≠ 0)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (x : rootOrbitField k L j β) :
    (Lie.baseChangeFixedLieEquiv k L G
      (rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit x).val).val =
        (rootOrbitFieldFixedSpanEquiv k L j hG hj hT β x).val.val := by
  let e := Lie.weightSpaceGaloisFixedEquiv k L (CommGroupScheme.groupHom f ≫ j) a hS
  let y := rootOrbitFixedWeightSpaceEquiv k L j f a hS hT ha β horbit
    (rootOrbitFieldFixedSpanEquiv k L j hG hj hT β x)
  have h := congrArg
    (fun z : Lie.baseChangeFixedWeightSpace k L (CommGroupScheme.groupHom f ≫ j) a =>
      z.val.val) (e.apply_symm_apply y)
  exact h

end Langlands.GroupScheme
