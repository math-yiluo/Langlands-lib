import Langlands.GroupScheme.Reductive.LocalSplitWeylCommutatorReduction
import Langlands.GroupScheme.Reductive.LocalSplitRankOneLaws
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.AffineSplitIsogenyRootMap

/-! # Normal simple-root data and powered root maps under arbitrary scalar extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace LocalSplitCell

open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {v : J → (Ga R ⟶ G)}

/-- The coroot square of rank-one normal data holds on every scheme test. -/
theorem RankOneNormal.constantPoint_square {a : J} (h : RankOneNormal i P v a)
    (Z : Over (Spec (CommRingCat.of R))) :
    G.constantPoint (rootWeylPoint P v a) Z *
        G.constantPoint (rootWeylPoint P v a) Z =
      cocharPoint (P.coroot a) Z (-1) ≫ i.hom.hom := by
  rw [rootWeylPoint, ← GroupScheme.constantPoint_mul, h.2.2,
    ← toUnit_comp_eq_constantPoint, ← Category.assoc, comp_cocharPoint]
  have hm : Units.map (toUnit Z).left.appTop.hom.toMonoidHom
      (-1 : Γ((𝟙_ (Over (Spec (CommRingCat.of R)))).left, ⊤)ˣ) = -1 := by
    convert Units.map_neg_one (toUnit Z).left.appTop.hom using 1
  rw [hm]

/-- Rank-one normalization pulls back along every coefficient algebra.
The original coefficient ring need not be local. -/
theorem RankOneNormal.baseChange {a : J} (h : RankOneNormal i P v a)
    (A : Type u) [CommRing A] [Algebra R A] :
    RankOneNormal (splitTorus.baseChangeHom (K := A) G I i) P
      (fun j => baseChangeRoot A (v j)) a := by
  refine ⟨?_, ?_, ?_⟩
  · intro B _ s x
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G (Over.mk s)).injective
    simp only [map_mul, map_inv, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_rootPoint]
    apply Over.OverMorphism.ext
    exact congrArg CommaMorphism.left (h.1 B (s ≫ algebraBaseMap R A) x)
  · intro B _ s x
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G (Over.mk s)).injective
    simp only [map_mul, map_inv, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_rootPoint]
    apply Over.OverMorphism.ext
    exact congrArg CommaMorphism.left (h.2.1 B (s ≫ algebraBaseMap R A) x)
  · let Z : Over (Spec (CommRingCat.of A)) := 𝟙_ _
    change (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).constantPoint
        (rootWeylPoint P (fun j => baseChangeRoot A (v j)) a) Z) *
        (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).constantPoint
        (rootWeylPoint P (fun j => baseChangeRoot A (v j)) a) Z) =
      cocharPoint (P.coroot a) Z (-1) ≫
        (splitTorus.baseChangeHom (K := A) G I i).hom.hom
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
    simpa only [rootWeylPoint, map_mul, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_torus, baseChangePointsEquiv_cocharPoint] using
      h.constantPoint_square ((Over.map (algebraBaseMap R A)).obj Z)

local instance affineNormalDataPullback
    {A : Type u} [CommRing A] [Algebra R A] [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

/-- All fields of actual normal simple-root data survive arbitrary scalar
extension with the same root datum, base and descending words. -/
theorem IsNormalSimpleData.baseChange [DecidableEq I] [IsAffineHom G.X.hom]
    {b : P.Base} {W : ∀ a, SimpleWord P b a}
    (h : IsNormalSimpleData i P b W v)
    (A : Type u) [CommRing A] [Algebra R A] :
    IsNormalSimpleData (splitTorus.baseChangeHom (K := A) G I i) P b W
      (fun a => baseChangeRoot A (v a)) := by
  let : Smooth G.X.hom := h.reductive.smooth
  exact
    { reductive := h.reductive.baseChange _
      maximal := splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i h.maximal
      rootDatum := h.rootDatum.baseChange_implicit (A := A)
      param := fun a ha =>
        ⟨isRootParametrization_baseChangeRoot A i _ _ (h.param a ha).1,
          isRootParametrization_baseChangeRoot A i _ _ (h.param a ha).2⟩
      weyl := fun a ha => isWeylPoint_baseChange A (h.weyl a ha)
      words := h.words
      rankOne := fun a ha => (h.rankOne a ha).baseChange A }

/-- Normal simple-root data with their original index choices transfer over
every commutative coefficient algebra. -/
def NormalSimpleDataBaseChangeStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    (I : Type u) [Fintype I] [DecidableEq I] (J : Type u)
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (W : ∀ a, SimpleWord P b a) (v : J → (Ga R ⟶ G)),
    IsNormalSimpleData i P b W v →
      IsNormalSimpleData (splitTorus.baseChangeHom (K := A) G I i) P b W
        (fun a => baseChangeRoot A (v a))

theorem normalSimpleDataBaseChange : NormalSimpleDataBaseChangeStatement.{u} := by
  intro R _ A _ _ I _ _ J G _ i P b W v h
  exact h.baseChange A

end LocalSplitCell

namespace AffineRootDatumIsogeny

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)

/-- The original root-factor characteristic hypothesis persists in every algebra. -/
theorem rootFactor_characteristic_baseChange
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0) :
    ∀ j', f.rootFactor j' ≠ 1 → (p : A) = 0 := by
  intro j' hj'
  simpa only [map_natCast, map_zero] using
    congrArg (algebraMap R A) (hchar j' hj')

/-- The actual powered root map pulls back with precisely its original exponent
and the canonical additive-line comparison. -/
theorem baseChangeRoot_rootMap
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (hcharA : ∀ j', f.rootFactor j' ≠ 1 → (p : A) = 0)
    (j' : J') (v : Ga R ⟶ H) :
    baseChangeRoot A (rootMap f hchar j' v) =
      rootMap f hcharA j' (baseChangeRoot A v) := by
  apply hom_ext_rootPoint
  intro Z x
  apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) H Z).injective
  rw [baseChangePointsEquiv_rootPoint, rootPoint_rootMap, rootPoint_rootMap,
    baseChangePointsEquiv_rootPoint]

/-- The prescribed torus map has the canonical base-change square over every scheme. -/
theorem torusMap_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S) :
    (splitTorus.baseChangeIso b I).hom ≫ torusMap S' f =
      (GroupScheme.baseChange b).map (torusMap S f) ≫
        (splitTorus.baseChangeIso b I').hom := by
  classical
  exact congrArg CommGroupScheme.groupHom
    (splitTorus.exponentHom_baseChange S I I' b f.weightMap)

/-- Transporting a prescribed torus restriction preserves its actual coordinate
map after every coefficient extension. -/
theorem baseChangeHom_torusMap
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H) :
    splitTorus.baseChangeHom (K := A) H I (torusMap _ f ≫ i') =
      torusMap (Spec (CommRingCat.of A)) f ≫
        splitTorus.baseChangeHom (K := A) H I' i' := by
  have h : (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
      (GroupScheme.baseChange (algebraBaseMap R A)).map (torusMap _ f) =
      torusMap (Spec (CommRingCat.of A)) f ≫
        (splitTorus.baseChangeIso (algebraBaseMap R A) I').inv := by
    apply (cancel_mono (splitTorus.baseChangeIso (algebraBaseMap R A) I').hom).1
    rw [Category.assoc, ← torusMap_baseChange, Iso.inv_hom_id_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ ≫ (GroupScheme.baseChange (algebraBaseMap R A)).map (torusMap _ f ≫ i') = _
  rw [Functor.map_comp, ← Category.assoc, h, Category.assoc]
  rfl

end AffineRootDatumIsogeny

end Langlands.GroupScheme
