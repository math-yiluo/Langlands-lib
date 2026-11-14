import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # All absolute roots restrict nontrivially in a quasi-split group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Centralizer

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- No root vanishes on a subtorus whose full centralizer is the acting split torus. -/
theorem root_restrict_ne_zero_of_sameField_torusCentralizer
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ j = a)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    {β : characterLattice T} (hβ : β ∈ roots j) : f ≫ β ≠ 0 := by
  have := hS.isAffineHom
  intro hz
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hβ.2
  have hXa : X ∈ weightSpace a 0 := by
    have h := weightSpace_le_comp f j β hX
    rwa [hf, hz] at h
  have hcentral := Lie.mem_torusCentralizer_of_mem_weightSpace_zero a X.toMul hXa
  rw [← hj.2] at hcentral
  have hXzero : X ∈ weightSpace j 0 :=
    Lie.mem_weightSpace_zero_of_mem_torusCentralizer j X.toMul
      (range_le_torusCentralizer j _ hcentral)
  exact hX0 ((Submodule.disjoint_def.mp (weightSpace_disjoint hT j hβ.1)) X hX hXzero)

/-- Restrict every actual root, without discarding roots, when the full
centralizer is the acting split torus. -/
def rootRestrictionOfTorusCentralizer
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ j = a)
    (hj : (torusCentralizer a).IsRepresentedBy j) (β : roots j) : roots a := by
  refine ⟨f ≫ β.val, ?_⟩
  rw [← hf]
  exact (rootRestriction f j ⟨β.val, β.property,
    root_restrict_ne_zero_of_sameField_torusCentralizer hS hT a j f hf hj β.property⟩).property

@[simp]
theorem rootRestrictionOfTorusCentralizer_val
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ j = a)
    (hj : (torusCentralizer a).IsRepresentedBy j) (β : roots j) :
    (rootRestrictionOfTorusCentralizer hS hT a j f hf hj β).val = f ≫ β.val := rfl

end Centralizer

section SplittingField

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k L
local notation "S_L" => Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_L" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom (G_L).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b G.X inferInstance

local instance : LocallyOfFiniteType (G_L).X.hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance

/-- Every absolute root has nonzero restriction to the base-changed maximal
split torus of a quasi-split group. -/
theorem IsQuasiSplit.root_restrict_ne_zero
    (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
    (ha : IsMaximalSplitTorus a) (hj : IsMaximalTorus j)
    (hf : CommGroupScheme.groupHom f ≫ j = a)
    (hTL : IsSplitTorus (T_L).toGrp)
    {β : characterLattice T_L}
    (hβ : β ∈ roots (T := T_L) (G := G_L) ((GroupScheme.baseChange b).map j)) :
    (CommGroupScheme.baseChange b).map f ≫ β ≠ 0 := by
  have hcent := (quasiSplitMaximalTorusCentralizer k G hG T S j a
    (CommGroupScheme.groupHom f) hj ha hf).baseChange b
  rw [← torusCentralizer_baseChange] at hcent
  have hfL : CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f) ≫
      (GroupScheme.baseChange b).map j = (GroupScheme.baseChange b).map a := by
    change (GroupScheme.baseChange b).map (CommGroupScheme.groupHom f) ≫
      (GroupScheme.baseChange b).map j = _
    rw [← Functor.map_comp, hf]
  exact root_restrict_ne_zero_of_sameField_torusCentralizer (k := L) (S := S_L) (T := T_L)
    (G := G_L) (ha.1.1.baseChange b) hTL
    ((GroupScheme.baseChange b).map a) ((GroupScheme.baseChange b).map j)
    ((CommGroupScheme.baseChange b).map f) hfL hcent hβ


/-- The total map from every root of a split containing maximal torus over an
extension field to an actual relative root over the original field. -/
def IsQuasiSplit.rootRestriction
    (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
    (ha : IsMaximalSplitTorus a) (hj : IsMaximalTorus j)
    (hf : CommGroupScheme.groupHom f ≫ j = a)
    (hTL : IsSplitTorus (T_L).toGrp)
    (β : roots (T := T_L) (G := G_L) ((GroupScheme.baseChange b).map j)) : roots a := by
  let α := (characterLattice.baseChangeEquiv b S ha.1.1).symm
    ((CommGroupScheme.baseChange b).map f ≫ β.val)
  refine ⟨α, (mem_roots_baseChange_iff (K := L) G S ha.1.1 a α).mp ?_⟩
  have he : characterLattice.baseChange b S α =
      (CommGroupScheme.baseChange b).map f ≫ β.val :=
    (characterLattice.baseChangeEquiv b S ha.1.1).apply_symm_apply _
  rw [he, ← hf, Functor.map_comp]
  change (CommGroupScheme.baseChange b).map f ≫ β.val ∈ roots
    (CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f) ≫
      (GroupScheme.baseChange b).map j)
  exact (mem_roots_comp_iff hTL (ha.1.1.baseChange b)
    ((CommGroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map j) _).mpr
    ⟨hG.root_restrict_ne_zero a j f ha hj hf hTL β.property,
      β.val, β.property, rfl⟩

/-- This total root map is the actual character restriction after pullback. -/
@[simp]
theorem IsQuasiSplit.rootRestriction_baseChange
    (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
    (ha : IsMaximalSplitTorus a) (hj : IsMaximalTorus j)
    (hf : CommGroupScheme.groupHom f ≫ j = a)
    (hTL : IsSplitTorus (T_L).toGrp)
    (β : roots (T := T_L) (G := G_L) ((GroupScheme.baseChange b).map j)) :
    characterLattice.baseChange b S (hG.rootRestriction a j f ha hj hf hTL β).val =
      (CommGroupScheme.baseChange b).map f ≫ β.val :=
  (characterLattice.baseChangeEquiv b S ha.1.1).apply_symm_apply _

/-- Every actual original relative root is reached by total root restriction. -/
theorem IsQuasiSplit.rootRestriction_surjective
    (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
    (ha : IsMaximalSplitTorus a) (hj : IsMaximalTorus j)
    (hf : CommGroupScheme.groupHom f ≫ j = a)
    (hTL : IsSplitTorus (T_L).toGrp) :
    Function.Surjective (hG.rootRestriction a j f ha hj hf hTL) := by
  intro α
  let α' : roots (CommGroupScheme.groupHom f ≫ j) := ⟨α.val, by simpa only [hf] using α.property⟩
  refine ⟨splittingFieldRootLift ha.1.1 hTL f j α', Subtype.ext ?_⟩
  apply (characterLattice.baseChangeEquiv b S ha.1.1).injective
  change characterLattice.baseChange b S _ = characterLattice.baseChange b S _
  rw [hG.rootRestriction_baseChange]
  exact splittingFieldRootLift_restriction ha.1.1 hTL f j α'

end SplittingField

end Langlands.GroupScheme
