import Langlands.GroupScheme.Rational.FiniteFieldNormalSylowStatement
import Langlands.GroupScheme.Rational.FiniteFieldSylowBorelStatement
import Langlands.GroupScheme.Rational.SplitSeriesPointCount
import Langlands.GroupScheme.Rational.UnipotentPointsPGroup
import Langlands.GroupScheme.Rational.ReductiveSolvableTorus
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Dynamic.SignedParabolicComparison
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Normal maximal p-subgroups contained in Borel subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace RelativeRoot

/-- Trivial rational points detect triviality of an affine split-unipotent
group over a finite field by the finite Ga-series point count. -/
theorem IsSplitUnipotent.range_id_eq_bot_of_subsingleton_rationalPoints
    {k : Type u} [Field k] [Finite k]
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
    (hU : IsSplitUnipotent U) [Subsingleton (rationalPoints U)] :
    SubgroupFunctor.range (𝟙 U) = ⊥ := by
  obtain ⟨n, hn⟩ := hU
  have hcard : Nat.card k ^ n = Nat.card k ^ 0 := by
    rw [← HasSplitSeries.card_rationalPoints n U hn, pow_zero]
    exact Nat.card_unique
  have hn0 : n = 0 := Nat.pow_right_injective Finite.one_lt_card hcard
  subst n
  exact hn

end RelativeRoot

section NormalBorel

variable {k : Type u} [Field k] [Finite k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (H : Subgroup (rationalPoints G))
    (hH : IsPGroup (ringChar k) H)
    (hmax : ∀ H' : Subgroup (rationalPoints G),
      H ≤ H' → IsPGroup (ringChar k) H' → H' = H)
    (hnormal : H.Normal) (i : B ⟶ G) (hi : IsGeometricBorelSubgroup i)
    (hHB : H ≤ (rationalPoints.map i).range)

include hG hH hmax hnormal hi hHB in
/-- A geometric Borel containing a normal maximal p-subgroup of the actual
rational-point group of a reductive finite-field group is the entire group. -/
theorem range_borel_eq_top_of_normal_maximalPSubgroup :
    SubgroupFunctor.range i = ⊤ := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  let : H.Normal := hnormal
  obtain ⟨χ, hχ⟩ :=
    ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup
      hG i hi.isParabolicSubgroup
  let χminus := Dynamic.oppositeCocharacter χ
  let U := Dynamic.Affine.unipotentScheme χminus
  let j : U ⟶ G := Dynamic.Affine.unipotentHom χminus
  have hj : (Dynamic.unipotent χminus).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χminus
  have hjc : IsClosedSubgroup j :=
    Dynamic.Affine.isClosedSubgroup_unipotentHom χminus
  let : Mono j.hom.hom := hj.1
  let : IsAffineHom U.X.hom := hjc.isAffineHom
  let : Smooth U.X.hom := (dynamicSmooth k G χminus U j).2.2 hj
  have hU : IsUnipotent U :=
    Dynamic.isUnipotent_of_isRepresentedBy_unipotent χminus hj hjc
  have hUs : RelativeRoot.IsSplitUnipotent U :=
    Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent χminus hj hjc
  let T₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let K : Subgroup (rationalPoints G) := (Dynamic.unipotent χminus).carrier T₀
  have hK : IsPGroup (ringChar k) K := by
    change IsPGroup (ringChar k) ((Dynamic.unipotent χminus).carrier T₀)
    rw [← hj.2]
    exact isPGroup_range_testPoints_of_isUnipotent (ringChar k) hU j T₀
  have hsup : H ⊔ K = H := hmax _ le_sup_left (hH.to_sup_of_normal_left hK)
  have hKH : K ≤ H := by rw [← hsup]; exact le_sup_right
  have hpoint : ∀ x : rationalPoints U, x = 1 := by
    intro x
    have hx : x ≫ j.hom.hom ∈ (Dynamic.unipotent χminus).carrier T₀ := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    have hxB := hHB (hKH hx)
    have hxP : x ≫ j.hom.hom ∈ (Dynamic.parabolic χ).carrier T₀ := by
      rw [← hχ]
      exact hxB
    have hx1 : x ≫ j.hom.hom = 1 :=
      Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hx hxP
    apply (cancel_mono j.hom.hom).mp
    rw [MonObj.one_comp]
    exact hx1
  let : Subsingleton (rationalPoints U) := ⟨fun x y => (hpoint x).trans (hpoint y).symm⟩
  have hUid := hUs.range_id_eq_bot_of_subsingleton_rationalPoints
  have hUbot : Dynamic.unipotent χminus = ⊥ := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro g
    constructor
    · intro hg
      rw [← hj.2] at hg
      obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
      have hx : x ∈ (SubgroupFunctor.range (𝟙 U)).carrier T :=
        SubgroupFunctor.mem_range.mpr ⟨x, by
          rw [Grp.id_hom_hom, Category.comp_id]⟩
      rw [hUid] at hx
      change x = 1 at hx
      change x ≫ j.hom.hom = 1
      rw [hx, MonObj.one_comp]
    · intro hg
      change g = 1 at hg
      rw [hg]
      exact Subgroup.one_mem _
  have htop := Dynamic.parabolic_neg_eq_top_of_unipotent_eq_bot
    isSplitTorus_gm χ (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) hUbot
  rw [Gm.powerHom_apply, neg_one_zsmul, neg_neg] at htop
  change Dynamic.parabolic χ = ⊤ at htop
  exact hχ.trans htop

/-- The inclusion of a geometric Borel containing a normal maximal p-subgroup
is the homomorphism of an actual isomorphism to the ambient reductive group. -/
def normalMaximalPSubgroupBorelIso : B ≅ G := by
  have : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hir : (⊤ : SubgroupFunctor G).IsRepresentedBy i :=
    ⟨inferInstance,
      range_borel_eq_top_of_normal_maximalPSubgroup hG H hH hmax hnormal i hi hHB⟩
  exact hir.topIso

@[simp] theorem normalMaximalPSubgroupBorelIso_hom :
    (normalMaximalPSubgroupBorelIso hG H hH hmax hnormal i hi hHB).hom = i := by
  exact SubgroupFunctor.IsRepresentedBy.topIso_hom _

include hG hH hmax hnormal hi hHB in
/-- A reductive finite-field group with such a Borel is a torus. -/
theorem isTorus_of_normal_maximalPSubgroup_le_borel : IsTorus G := by
  let e := normalMaximalPSubgroupBorelIso hG H hH hmax hnormal i hi hHB
  exact hG.isTorus_of_isSolvableGroupScheme
    (hi.1.isSolvableGroupScheme.of_iso e.symm)

end NormalBorel

/-- The Sylow/Borel classification implies the normal-Sylow torus criterion.
The classification remains an explicit input. -/
theorem finiteFieldNormalSylowTorus_of_sylowBorel
    (hsylow : FiniteFieldSylowBorelStatement.{u}) :
    FiniteFieldNormalSylowTorusStatement.{u} := by
  intro k _ _ G hG H hH hmax hnormal
  obtain ⟨B, U, i, j, hi, _, hHU⟩ := (hsylow k G hG H).mp ⟨hH, hmax⟩
  apply isTorus_of_normal_maximalPSubgroup_le_borel hG H hH hmax hnormal i hi
  intro x hx
  rw [hHU] at hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y ≫ j.hom.hom, ?_⟩
  change (y ≫ j.hom.hom) ≫ i.hom.hom = y ≫ (j ≫ i).hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

end Langlands.GroupScheme
