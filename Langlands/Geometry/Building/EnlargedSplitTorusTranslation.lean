import Langlands.Geometry.Building.CentralIsogenyTranslation
import Langlands.Geometry.Building.SplitTorusTranslationBaseChange
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Actual reduced translation embeddings into an enlarged split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

section SameField

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (f : S ⟶ T) (i : S.toGrp ⟶ G) (j : T.toGrp ⟶ G)
  (h : CommGroupScheme.groupHom f ≫ j = i)

include hS hT h in
/-- Actual restriction of all roots identifies the exact preimage of the
ambient common root kernel, including roots with zero restriction. -/
theorem cocharacterMapReal_mem_rootAnnihilator_restriction_iff (v : V S) :
    cocharacterMapReal f v ∈ rootAnnihilator j ↔ v ∈ rootAnnihilator i := by
  rw [← h, mem_rootAnnihilator, mem_rootAnnihilator]
  constructor
  · intro hv a ha
    obtain ⟨_, b, hb, rfl⟩ := (mem_roots_comp_iff hT hS f j a).mp ha
    rw [← eval_cocharacterMapReal]
    exact hv b hb
  · intro hv a ha
    rw [eval_cocharacterMapReal]
    by_cases hz : f ≫ a = 0
    · rw [hz, eval_zero_char]
    · exact hv _ ((mem_roots_comp_iff hT hS f j (f ≫ a)).mpr ⟨hz, a, ha, rfl⟩)

/-- The actual cocharacter map descends to reduced translation spaces. -/
def splitTorusTranslationMap : TranslationSpace i →ₗ[ℝ] TranslationSpace j :=
  (rootAnnihilator i).liftQ
    ((rootAnnihilator j).mkQ.comp (cocharacterMapReal f)) fun v hv => by
      change (Submodule.Quotient.mk (cocharacterMapReal f v) : TranslationSpace j) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((cocharacterMapReal_mem_rootAnnihilator_restriction_iff hS hT f i j h v).mpr hv)

@[simp] theorem splitTorusTranslationMap_mk (v : V S) :
    splitTorusTranslationMap hS hT f i j h (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (cocharacterMapReal f v) := rfl

/-- Root-kernel reflection proves injectivity even when the torus map itself
has a kernel; no central-isogeny or root-bijection premise is needed. -/
theorem splitTorusTranslationMap_injective :
    Function.Injective (splitTorusTranslationMap hS hT f i j h) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 0
  rw [LinearMap.mem_ker] at hu
  induction u using Submodule.Quotient.induction_on with
  | _ v =>
    change (Submodule.Quotient.mk (cocharacterMapReal f v) : TranslationSpace j) = 0 at hu
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (cocharacterMapReal_mem_rootAnnihilator_restriction_iff hS hT f i j h v).mp
      ((Submodule.Quotient.mk_eq_zero _).mp hu)

/-- Every ambient root with nonzero restriction supplies the actual restricted root. -/
def splitTorusRestrictedRoot (a : relativeRoots j) (ha : f ≫ a.val ≠ 0) :
    relativeRoots i :=
  ⟨f ≫ a.val, by
    rw [← h]
    exact (mem_roots_comp_iff hT hS f j _).mpr ⟨ha, a.val, a.property, rfl⟩⟩

/-- Nonzero restricted roots intertwine the actual reduced root forms. -/
theorem rootForm_splitTorusTranslationMap (a : relativeRoots j) (ha : f ≫ a.val ≠ 0)
    (v : TranslationSpace i) :
    rootForm j a (splitTorusTranslationMap hS hT f i j h v) =
      rootForm i (splitTorusRestrictedRoot hS hT f i j h a ha) v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  exact eval_cocharacterMapReal f a.val w

end SameField

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance enlargedTranslationAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  infer_instance

private instance enlargedTranslationFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (Limits.pullback.snd G.X.hom b)
  infer_instance

/-- An actual maximal split torus upstairs containing the original pulled-back
torus, with the canonical injective map of reduced translation spaces. -/
structure FieldExtensionTranslationEmbeddingData where
  T : CommGroupScheme (Spec (CommRingCat.of K))
  j : T.toGrp ⟶ G_K
  isMaximalSplitTorus : IsMaximalSplitTorus j
  torusMap : S_K ⟶ T
  factorization : CommGroupScheme.groupHom torusMap ≫ j = i_K
  translationMap : TranslationSpace i →ₗ[ℝ] TranslationSpace (S := T) j
  injective : Function.Injective translationMap
  map_mk : ∀ (hS : IsSplitTorus S.toGrp) (v : V S),
    translationMap (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (cocharacterMapReal torusMap
        (splitCocharacterBaseChange (K := K) S hS v))

/-- Construct the actual maximal enlargement and reduced translation injection.
The containing torus and the root-kernel comparison are outputs. -/
def fieldExtensionTranslationEmbedding (hi : IsSplitSubtorus i) :
    FieldExtensionTranslationEmbeddingData (K := K) i := by
  have hiK : IsSplitSubtorus (T := S_K) i_K :=
    ⟨hi.1.baseChange b, hi.2.baseChange b⟩
  let E := maximalSplitExtension (T := S_K) G_K i_K hiK
  let T := E.1
  let j : T.toGrp ⟶ G_K := E.2.val
  have hj : IsMaximalSplitTorus j := E.2.property.1
  let t : S_K ⟶ T := Additive.ofMul E.2.property.2.choose
  have ht : CommGroupScheme.groupHom t ≫ j = i_K := E.2.property.2.choose_spec
  let L := splitTorusTranslationMap (hi.1.baseChange b) hj.1.1 t i_K j ht
  let C := splitTranslationBaseChange (K := K) hi.1 i
  refine ⟨T, j, hj, t, ht, L.comp C.toLinearMap, ?_, ?_⟩
  · exact (splitTorusTranslationMap_injective (hi.1.baseChange b) hj.1.1 t i_K j ht).comp
      C.injective
  · intro hS v
    rfl

end FieldExtension

end Langlands.Geometry.Building
