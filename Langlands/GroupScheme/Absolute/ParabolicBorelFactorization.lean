import Langlands.GroupScheme.Absolute.BorelPromotion
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Actual Borel factorizations of parabolics over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme

/-- The natural comparison for successive pullback along a map and its section. -/
def baseChangeSectionNatIso {S S' : Scheme.{u}} (b : S' ⟶ S) (a : S ⟶ S')
    (ha : a ≫ b = 𝟙 S) :
    GroupScheme.baseChange b ⋙ GroupScheme.baseChange a ≅ 𝟭 (GroupScheme S) :=
  Functor.mapGrpCompIso.symm ≪≫
    Functor.mapGrpNatIso ((Over.pullbackComp a b).symm ≪≫
      eqToIso (congrArg (fun c => Over.pullback c) ha) ≪≫ Over.pullbackId) ≪≫
    Functor.mapGrpIdIso

/-- Rational points are unchanged by pullback along an isomorphism of bases. -/
def baseChangeRationalPointsEquivOfIsIso {S S' : Scheme.{u}} (b : S' ⟶ S) [IsIso b]
    (G : GroupScheme S) :
    (Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) ≃*
      (Over.mk (𝟙 S) ⟶ G.X) := by
  let e : (Over.map b).obj (Over.mk (𝟙 S')) ≅ Over.mk (𝟙 S) :=
    Over.isoMk (asIso b) (by simp)
  exact (baseChangePointsEquiv b G (Over.mk (𝟙 S'))).trans
    (G.points.mapIso e.symm.op).groupIsoToMulEquiv

section AlgebraicallyClosed

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, the solvability definition can be read on
points over that very field. -/
theorem isSolvableGroupScheme_iff_rationalPoints
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsSolvableGroupScheme G ↔
      Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) := by
  have : IsIso (toAlgebraicClosure k) :=
    isIso_SpecMap_iff.mpr IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := baseChangeRationalPointsEquivOfIsIso (toAlgebraicClosure k) G
  constructor
  · intro h
    have : Group.IsSolvable
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
          ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X) := h
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  · intro h
    have := h
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- Isomorphic change of algebraically closed base fields preserves solvability. -/
theorem IsSolvableGroupScheme.baseChange_of_isIso
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSolvableGroupScheme G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    IsSolvableGroupScheme ((GroupScheme.baseChange b).obj G) := by
  apply (isSolvableGroupScheme_iff_rationalPoints _).mpr
  have := (isSolvableGroupScheme_iff_rationalPoints G).mp hG
  let e := baseChangeRationalPointsEquivOfIsIso b G
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- Isomorphic change of algebraically closed base fields preserves Borels. -/
theorem IsBorelSubgroup.baseChange_of_isIso
    {B G : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}
    (hi : IsBorelSubgroup i)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    IsBorelSubgroup ((GroupScheme.baseChange b).map i) := by
  let F := GroupScheme.baseChange b
  let R := GroupScheme.baseChange (inv b)
  let e := baseChangeSectionNatIso b (inv b) (IsIso.inv_hom_id b)
  refine ⟨hi.isClosedSubgroup.baseChange b, ?_, ?_,
    hi.isSolvableGroupScheme.baseChange_of_isIso b, ?_⟩
  · have : Smooth B.X.hom := hi.smooth
    change Smooth (pullback.snd B.X.hom b)
    infer_instance
  · exact (Scheme.homeoOfIso (asIso (pullback.fst B.X.hom b))).connectedSpace_iff.mpr
      hi.connectedSpace
  · intro C j f hj hsm hconn hsol hf
    let D := R.obj C
    let jD := R.map j ≫ (e.app G).hom
    let g := (e.app B).inv ≫ R.map f
    have hjD : IsClosedSubgroup jD := by
      have : IsClosedImmersion (R.map j).hom.hom.left := hj.baseChange (inv b)
      have : IsIso (e.app G).hom.hom.hom.left :=
        (inferInstance : IsIso ((Over.forget _).mapIso
          ((Grp.forget _).mapIso (e.app G))).hom)
      change IsClosedImmersion ((R.map j).hom.hom.left ≫ (e.app G).hom.hom.hom.left)
      infer_instance
    have hsmD : Smooth D.X.hom := by
      have : Smooth C.X.hom := hsm
      change Smooth (pullback.snd C.X.hom (inv b))
      infer_instance
    have hconnD : ConnectedSpace D.X.left :=
      (Scheme.homeoOfIso (asIso (pullback.fst C.X.hom (inv b)))).connectedSpace_iff.mpr
        hconn
    have hg : g ≫ jD = i := by
      change ((e.app B).inv ≫ R.map f) ≫ (R.map j ≫ (e.app G).hom) = i
      rw [Category.assoc, ← Category.assoc (R.map f), ← R.map_comp, hf]
      change (e.app B).inv ≫ ((F ⋙ R).map i ≫ e.hom.app G) = i
      rw [e.hom.naturality i]
      change (e.app B).inv ≫ (e.app B).hom ≫ i = i
      simp
    have : IsIso g := hi.maximal D jD g hjD hsmD hconnD
      (hsol.baseChange_of_isIso (inv b)) hg
    have hfactor : R.map f = (e.app B).hom ≫ g := by simp [g]
    have : IsIso (R.map f) := by rw [hfactor]; infer_instance
    exact isIso_of_baseChange (inv b) f

variable {P G : GroupScheme (Spec (CommRingCat.of k))} {i : P ⟶ G}

/-- The geometric Borel witness of a parabolic can be realized over its original
algebraically closed base field, with the original inclusion unchanged. -/
theorem IsParabolicSubgroup.exists_isBorelSubgroup_factor
    (hi : IsParabolicSubgroup i) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (j : B ⟶ G) (f : B ⟶ P),
      IsBorelSubgroup j ∧ f ≫ i = j := by
  have : IsIso (toAlgebraicClosure k) :=
    isIso_SpecMap_iff.mpr IsAlgClosed.algebraMap_bijective_of_isIntegral
  let b := toAlgebraicClosure k
  let R := GroupScheme.baseChange (inv b)
  let e := baseChangeSectionNatIso b (inv b) (IsIso.inv_hom_id b)
  obtain ⟨B, j, f, hj, hf⟩ := hi.exists_isBorelSubgroup
  refine ⟨R.obj B, R.map j ≫ (e.app G).hom, R.map f ≫ (e.app P).hom,
    (hj.baseChange_of_isIso (inv b)).comp_iso (e.app G), ?_⟩
  change (R.map f ≫ (e.app P).hom) ≫ i = R.map j ≫ (e.app G).hom
  have hnat : R.map ((GroupScheme.baseChange b).map i) ≫ (e.app G).hom =
      (e.app P).hom ≫ i := e.hom.naturality i
  rw [Category.assoc, ← hnat, ← Category.assoc, ← R.map_comp, hf]

end AlgebraicallyClosed

variable {k : Type u} [Field k]
variable {P G : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G)

/-- An actual Borel subgroup of the ambient group, with a factor through the
specified original inclusion. -/
structure IsParabolicSubgroup.BorelFactorization where
  B : GroupScheme (Spec (CommRingCat.of k))
  inclusion : B ⟶ G
  factor : B ⟶ P
  isBorel : IsBorelSubgroup inclusion
  factor_comp : factor ≫ i = inclusion

/-- Choose an actual Borel factorization over an algebraically closed base. -/
def IsParabolicSubgroup.borelFactorizationOfIsAlgClosed [IsAlgClosed k]
    (hi : IsParabolicSubgroup i) : IsParabolicSubgroup.BorelFactorization i :=
  Classical.choice (show Nonempty (IsParabolicSubgroup.BorelFactorization i) from by
    obtain ⟨B, j, f, hj, hf⟩ := hi.exists_isBorelSubgroup_factor
    exact ⟨⟨B, j, f, hj, hf⟩⟩)

/-- The chosen Borel lies in the specified subgroup on every test scheme. -/
theorem IsParabolicSubgroup.BorelFactorization.range_le
    (d : IsParabolicSubgroup.BorelFactorization i) :
    SubgroupFunctor.range d.inclusion ≤ SubgroupFunctor.range i :=
  SubgroupFunctor.range_le_of_factor d.factor d.factor_comp

/-- The factor is a Borel subgroup in the original closed overgroup as well. -/
theorem IsParabolicSubgroup.BorelFactorization.factor_isBorel
    (d : IsParabolicSubgroup.BorelFactorization i) (hi : IsClosedSubgroup i) :
    IsBorelSubgroup d.factor := by
  apply IsBorelSubgroup.of_comp hi
  rw [d.factor_comp]
  exact d.isBorel

end Langlands.GroupScheme
