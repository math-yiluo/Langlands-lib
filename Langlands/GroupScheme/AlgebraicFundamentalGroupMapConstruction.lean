import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctor
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.SimplyConnected.HomLift
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType

/-! # Actual torus factorizations and derived-cover lifts for fundamental-group maps -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k H) (b : Choice k G) (f : H ⟶ G)

/-- The actual map between the supplied full derived subgroups. -/
def derivedMap : a.derived ⟶ b.derived :=
  a.isCover.isDerivedSubgroup.map b.isCover.isDerivedSubgroup f

@[reassoc] theorem derivedMap_comp :
    a.derivedMap b f ≫ b.derivedInclusion = a.derivedInclusion ≫ f :=
  a.isCover.isDerivedSubgroup.map_comp b.isCover.isDerivedSubgroup f

/-- The actual lift of a reductive morphism to the simply connected derived covers. -/
def coverMap : a.cover ⟶ b.cover :=
  letI := b.isCover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.isAffineHom
  SimplyConnectedHomLift.liftHom (a.covering ≫ a.derivedMap b f) b.covering
    b.isCover.isSimplyConnectedCover.isCentralIsogeny
    a.isCover.isSimplyConnectedCover.isSimplyConnected
    b.isCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
    inferInstance

@[reassoc] theorem coverMap_comp :
    a.coverMap b f ≫ b.covering = a.covering ≫ a.derivedMap b f := by
  let := b.isCover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.isAffineHom
  exact SimplyConnectedHomLift.liftHom_comp _ _ _ _ _ _

@[reassoc] theorem coverMap_comp_ambient :
    a.coverMap b f ≫ (b.covering ≫ b.derivedInclusion) =
      (a.covering ≫ a.derivedInclusion) ≫ f := by
  rw [← Category.assoc, coverMap_comp, Category.assoc, derivedMap_comp,
    ← Category.assoc]

include b in
/-- A homomorphism has an actual containing maximal-torus factorization over `k`. -/
theorem exists_torusFactorization :
    ∃ (b : Choice k G) (e : a.torus ⟶ b.torus),
      a.inclusion ≫ f = CommGroupScheme.groupHom e ≫ b.inclusion := by
  let := a.isCover.isConnectedReductive.smooth
  let := b.isCover.isConnectedReductive.smooth
  let := b.isCover.isConnectedReductive.isAffineHom
  obtain ⟨T, i, q, hT, hi, hq⟩ := torusImageClosedTorusStatement k G a.torus.toGrp
    a.isMaximal.1 (a.inclusion ≫ f)
  obtain ⟨M, j, hj, r, hr⟩ := exists_maximalTorus_extension_of_finiteType G i hT hi
  let c : Choice k G := { b with torus := M, inclusion := j, isMaximal := hj }
  refine ⟨c, Additive.ofMul (q ≫ r), ?_⟩
  change a.inclusion ≫ f = (q ≫ r) ≫ j
  rw [Category.assoc, hr, hq]

variable (E : Type u) [Field E] [Algebra k E]

include b in
/-- Every reductive morphism has a geometric torus factorization of the exact
kind required by `IsInducedMap`. -/
theorem exists_isTorusFactorization :
    ∃ (c : Choice k G)
      (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus),
      a.IsTorusFactorization E c f e := by
  obtain ⟨c, e, he⟩ := a.exists_torusFactorization b f
  refine ⟨c, (CommGroupScheme.baseChange (algebraBaseMap k E)).map e, ?_⟩
  change (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map f =
    (GroupScheme.baseChange (algebraBaseMap k E)).map (CommGroupScheme.groupHom e) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion
  rw [← Functor.map_comp, ← Functor.map_comp, he]

/-- Quotient representatives and a single torus factorization determine an
induced map uniquely. -/
theorem IsInducedMap.ext {m n : a.atChoice E →ₗ[ℤ] b.atChoice E}
    (hm : a.IsInducedMap E b f m) (hn : a.IsInducedMap E b f n) : m = n := by
  obtain ⟨c, e, he⟩ := hm.1
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  exact (hm.2 c e he ν).trans (hn.2 c e he ν).symm

end Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice
