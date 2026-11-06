import Langlands.Geometry.Building.SplitTorusTranslationBaseChange
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent

/-! # Actual normalizer actions under split-torus field extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

open GaloisPointComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

/-- An actual normalizing torus automorphism pulls back to one for the
actual scalar extension of the original rational point. -/
theorem IsNormalizingPoint.rationalExtend
    {n : rationalPoints G} {σ : S ≅ S} (hn : IsNormalizingPoint i n σ) :
    IsNormalizingPoint i_K (rationalExtend k K G n)
      ((CommGroupScheme.baseChange b).mapIso σ) := by
  have h := congrArg (fun f => (GroupScheme.baseChange b).map f) hn
  change (GroupScheme.baseChange b).map i ≫
      ((baseChanged k K G).innerIso (GaloisPointComparison.rationalExtend k K G n)).hom =
    (GroupScheme.baseChange b).map (CommGroupScheme.groupHom σ.hom) ≫
      (GroupScheme.baseChange b).map i
  simpa only [IsNormalizingPoint, Functor.map_comp, baseChange_innerIso_hom,
    ← rationalExtend_eq_baseChangeBasePoint k K G] using h

/-- Scalar extension on the existing normalizer-point subgroups. Its
carrier map is the actual ambient `rationalExtend`. -/
def normalizerPointsFieldExtend :
    normalizerPoints i →* normalizerPoints (T := S_K) i_K where
  toFun n := ⟨rationalExtend k K G n.val,
    ⟨(CommGroupScheme.baseChange b).mapIso (normalizingAut i n),
      (isNormalizingPoint_normalizingAut i n).rationalExtend (K := K) i⟩⟩
  map_one' := Subtype.ext (map_one (rationalExtend k K G))
  map_mul' n m := Subtype.ext (map_mul (rationalExtend k K G) n.val m.val)

@[simp] theorem normalizerPointsFieldExtend_coe (n : normalizerPoints i) :
    (normalizerPointsFieldExtend (K := K) i n :
      rationalPoints (baseChanged k K G)) = rationalExtend k K G n.val := rfl

/-- Centralizing original points remain centralizing after field extension. -/
theorem normalizerPointsFieldExtend_mem_centralizerPoints
    {n : normalizerPoints i} (hn : n.val ∈ centralizerPoints i) :
    (normalizerPointsFieldExtend (K := K) i n).val ∈
      centralizerPoints (T := S_K) i_K := by
  have h := (show IsNormalizingPoint i n.val (Iso.refl S) from hn).rationalExtend
    (K := K) i
  change IsNormalizingPoint (T := S_K) i_K (rationalExtend k K G n.val) (Iso.refl S_K)
  simpa only [Functor.mapIso_refl] using h

/-- Field extension of the actual quotient of normalizer by centralizer points. -/
def relativeWeylGroupFieldExtend :
    relativeWeylGroup i →* relativeWeylGroup (T := S_K) i_K :=
  QuotientGroup.map _ _ (normalizerPointsFieldExtend (K := K) i) fun n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact normalizerPointsFieldExtend_mem_centralizerPoints (K := K) i hn

@[simp] theorem relativeWeylGroupFieldExtend_mk (n : normalizerPoints i) :
    relativeWeylGroupFieldExtend (K := K) i (QuotientGroup.mk n) =
      QuotientGroup.mk (normalizerPointsFieldExtend (K := K) i n) := rfl

variable [Mono i.hom.hom.left]

local instance normalizerFieldExtendMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- Uniqueness identifies the chosen normalizing automorphism upstairs
with the actual pullback of the chosen original one. -/
theorem normalizingAut_normalizerPointsFieldExtend (n : normalizerPoints i) :
    normalizingAut (T := S_K) i_K (normalizerPointsFieldExtend (K := K) i n) =
      (CommGroupScheme.baseChange b).mapIso (normalizingAut i n) :=
  (isNormalizingPoint_normalizingAut (T := S_K) i_K
    (normalizerPointsFieldExtend (K := K) i n)).unique (T := S_K) i_K
      ((isNormalizingPoint_normalizingAut i n).rationalExtend (K := K) i)

/-- Actual character pullback intertwines the two normalizer Weyl actions. -/
theorem characterBaseChange_weylAction (n : normalizerPoints i)
    (χ : characterLattice S) :
    characterLattice.baseChange b S (weylAction i n χ) =
      weylAction (T := S_K) i_K (normalizerPointsFieldExtend (K := K) i n)
        (characterLattice.baseChange b S χ) := by
  rw [weylAction_apply, weylAction_apply, normalizingAut_normalizerPointsFieldExtend]
  exact characterLattice.baseChange_precomp b _ _

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
  [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

local instance splitNormalizerBaseChangeMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- The actual real cocharacter base-change equivalence intertwines
normalizer actions through the actual extended rational point. -/
theorem splitCocharacterBaseChange_normalizerAction
    (n : normalizerPoints i) (v : V S) :
    splitCocharacterBaseChange (K := K) S hS (normalizerAction i n v) =
      normalizerAction (T := S_K) i_K (normalizerPointsFieldExtend (K := K) i n)
        (splitCocharacterBaseChange (K := K) S hS v) := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [normalizerAction_tmul, splitCocharacterBaseChange_tmul,
      cocharacterLattice.baseChange_comp, normalizingAut_normalizerPointsFieldExtend]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The same actual equivalence intertwines the quotient relative Weyl actions. -/
theorem splitCocharacterBaseChange_relativeWeylRealAction
    (w : relativeWeylGroup i) (v : V S) :
    splitCocharacterBaseChange (K := K) S hS (relativeWeylRealAction i w v) =
      relativeWeylRealAction (T := S_K) i_K (relativeWeylGroupFieldExtend (K := K) i w)
        (splitCocharacterBaseChange (K := K) S hS v) := by
  refine QuotientGroup.induction_on w fun n => ?_
  exact splitCocharacterBaseChange_normalizerAction (K := K) hS i n v

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance splitNormalizerBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The actual reduced translation equivalence intertwines the existing
normalizer derivatives. No compatibility premise is supplied. -/
theorem splitTranslationBaseChange_translationAction (n : normalizerPoints i)
    (v : TranslationSpace i) :
    splitTranslationBaseChange (K := K) hS i (translationAction i n v) =
      translationAction (S := S_K) i_K (normalizerPointsFieldExtend (K := K) i n)
        (splitTranslationBaseChange (K := K) hS i v) := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [translationAction_mk, splitTranslationBaseChange_mk,
    splitTranslationBaseChange_mk, translationAction_mk]
  exact congrArg Submodule.Quotient.mk
    (splitCocharacterBaseChange_normalizerAction (K := K) hS i n w)

end Langlands.Geometry.Building
