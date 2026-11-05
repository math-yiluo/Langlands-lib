import Langlands.GroupScheme.Derived.SemisimpleReflectionReduction
import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Langlands.GroupScheme.Rational.RootSubgroupStabilityProof

/-! # Torus containment from actual opposite-root factor pairs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

namespace RelativeRoot

variable {a : characterLattice T} {x : rationalPoints G}
  {p : rationalPoints G × rationalPoints G}

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] in
/-- A subgroup containing both root functors contains the commutators of an
actual normalizing opposite product with every torus point. -/
theorem IsOppositeFactorPair.torusCommutatorEnd_mem
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hp : IsOppositeFactorPair i a x p) {F : SubgroupFunctor G}
    (hplus : subgroup i a ≤ F) (hminus : subgroup i (-a) ≤ F)
    {U : Over (Spec (CommRingCat.of k))} (t : U ⟶ T.X) :
    t ≫ (CommGroupScheme.groupHom
      (torusCommutatorEnd i ⟨p.1 * x * p.2, hp.2.2⟩)).hom.hom ≫ i.hom.hom ∈
      F.carrier U := by
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  let b := AutomorphicAction.conjugation i
  have hconst {c : characterLattice T} {y : rationalPoints G}
      (hy : y ∈ (subgroup i c).carrier (Over.mk (𝟙 _))) :
      G.constantPoint y U ∈ (subgroup i c).carrier U :=
    (subgroup i c).comp_mem (T := Over.mk (𝟙 _)) (T' := U) (x := y)
      (Over.homMk U.hom (by simp)) hy
  have h1 := hconst hp.1
  have h2 := hconst hx
  have h3 := hconst hp.2.1
  have hn : G.constantPoint n.val U ∈ F.carrier U := by
    change G.constantPoint (p.1 * x * p.2) U ∈ F.carrier U
    rw [constantPoint_mul, constantPoint_mul]
    exact (F.carrier U).mul_mem
      ((F.carrier U).mul_mem (hminus U h1) (hplus U h2)) (hminus U h3)
  have hc : b.act t (G.constantPoint n.val U) ∈ F.carrier U := by
    change b.act t (G.constantPoint (p.1 * x * p.2) U) ∈ F.carrier U
    rw [constantPoint_mul, constantPoint_mul, b.act_mul_right, b.act_mul_right]
    exact (F.carrier U).mul_mem
      ((F.carrier U).mul_mem
        (hminus U (subgroup_isStable i (-a) U t _ h1))
        (hplus U (subgroup_isStable i a U t _ h2)))
      (hminus U (subgroup_isStable i (-a) U t _ h3))
  rw [comp_torusCommutatorEnd]
  have he :
      G.constantPoint n.val U * (t ≫ i.hom.hom) *
          (G.constantPoint n.val U)⁻¹ * (t ≫ i.hom.hom)⁻¹ =
        G.constantPoint n.val U * (b.act t (G.constantPoint n.val U))⁻¹ := by
    rw [AutomorphicAction.conjugation_act]
    group
  rw [he]
  exact (F.carrier U).mul_mem hn ((F.carrier U).inv_mem hc)

end RelativeRoot

omit [Mono i.hom.hom.left] in
/-- A representative-specific commutator containment suffices to put its
coroot in a closed subgroup; no other ambient commutators are needed. -/
theorem IsRootDatumOf.coroot_mem_of_torusCommutators
    {J : Type*} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (a : J) (n : normalizerPoints i)
    (hn : characterAut (normalizingAut i n) = P.reflection a)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hcomm : ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X),
      t ≫ (CommGroupScheme.groupHom (torusCommutatorEnd i n)).hom.hom ≫ i.hom.hom ∈
        (SubgroupFunctor.range j).carrier U) :
    P.coroot a ∈ cocharactersLandingIn i (SubgroupFunctor.range j) := by
  have hinv : P.coroot a ≫ (normalizingAut i n).hom = -P.coroot a :=
    hP.cocharacterAut_coroot i a (normalizingAut i n) hn
  have he : P.coroot a ≫ torusCommutatorEnd i n = (-2 : ℤ) • P.coroot a := by
    rw [torusCommutatorEnd, Preadditive.comp_sub, Category.comp_id, hinv]
    module
  apply mem_cocharactersLandingIn_of_zsmul_mem i hj (m := (-2 : ℤ)) (by norm_num)
  rw [← he]
  intro U z
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_comp, Category.assoc]
  exact hcomm U (z ≫ (CommGroupScheme.groupHom (P.coroot a)).hom.hom)

/-- Actual opposite-pair existence supplies torus containment in every closed
subgroup containing all actual roots of a split closed torus in a semisimple
group. Maximality and reducedness of the root system are not needed. -/
theorem IsSemisimple.range_torus_le_of_oppositeFactorPairs
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hroots : ∀ a ∈ relativeRoots i,
      RelativeRoot.subgroup i a ≤ SubgroupFunctor.range j) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range j := by
  classical
  have := hG.isConnectedReductive.smooth
  choose x hx hx1 using fun α : relativeRoots i =>
    RelativeRoot.exists_rootPoint_actual hT i α.property
  choose p hp using fun α : relativeRoots i => hE α.val α.property (x α) (hx α) (hx1 α)
  let D : RelativeRootReflectionData i :=
    { coroot := fun α => (hp α).coroot i hT α.property.1 (hx α) (hx1 α)
      representative := fun α => ⟨(p α).1 * x α * (p α).2, (hp α).2.2⟩
      pair_self := fun α => ((hp α).coroot_spec i hT α.property.1 (hx α) (hx1 α)).1
      action := fun α => ((hp α).coroot_spec i hT α.property.1 (hx α) (hx1 α)).2 }
  have hfinite := hT.finite_relativeRoots i
  have hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤ := by
    apply top_unique
    rw [← hG.relativeRootSpan_eq_top hT hi]
    exact Submodule.span_mono (Set.image_mono Set.subset_union_left)
  let P := D.rootDatum hT hfinite hspan
  have hP : IsRootDatumOf i P := D.isRootDatumOf_rootDatum hT hfinite hspan
  have : Finite (relativeRoots i) := hfinite.to_subtype
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  have : Finite (cocharacterLattice T ⧸ P.corootSpan ℤ) :=
    P.finite_quotient_rootSpan_iff_corootSpan.mp (hG.finite_quotient_rootSpan hT hi hP)
  have hcoroot (α : relativeRoots i) :
      P.coroot α ∈ cocharactersLandingIn i (SubgroupFunctor.range j) := by
    apply hP.coroot_mem_of_torusCommutators i α (D.representative α)
      (D.rootDatum_reflection hT hfinite hspan α).symm hj
    intro U t
    have hneg : -α.val ∈ relativeRoots i := by
      have hn := weylAction_mapsTo_relativeRoots i (D.representative α) α.property
      have hflip : weylAction i (D.representative α) α.val = -α.val :=
        (hp α).weylAction_eq_neg i hT α.property.1 (hx α) (hx1 α)
      rwa [hflip] at hn
    exact (hp α).torusCommutatorEnd_mem i (hx α)
      (hroots α.val α.property) (hroots (-α.val) hneg) t
  have hle : P.corootSpan ℤ ≤ cocharactersLandingIn i (SubgroupFunctor.range j) := by
    apply Submodule.span_le.mpr
    rintro ν ⟨α, rfl⟩
    exact hcoroot α
  have htotal : cocharactersLandingIn i (SubgroupFunctor.range j) = ⊤ := by
    apply top_unique
    intro ν _
    obtain ⟨m, hm, hmν⟩ :=
      (isOfFinAddOrder_of_finite ((P.corootSpan ℤ).mkQ ν)).exists_nsmul_eq_zero
    have hmν' : (m : ℤ) • ν ∈ P.corootSpan ℤ := by
      apply (Submodule.Quotient.mk_eq_zero (P.corootSpan ℤ)).mp
      change (P.corootSpan ℤ).mkQ ((m : ℤ) • ν) = 0
      rw [map_zsmul, natCast_zsmul]
      exact hmν
    exact mem_cocharactersLandingIn_of_zsmul_mem i hj
      (Int.natCast_ne_zero.mpr hm.ne') (hle hmν')
  exact hT.range_le_of_cocharacters i (SubgroupFunctor.range j) htotal

/-- The actual factorization of the torus inclusion through a closed subgroup
containing every root, under opposite-pair existence. -/
def torusLiftOfOppositeFactorPairs
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hroots : ∀ a ∈ relativeRoots i,
      RelativeRoot.subgroup i a ≤ SubgroupFunctor.range j) :
    T.toGrp ⟶ H := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact (show (SubgroupFunctor.range j).IsRepresentedBy j from ⟨inferInstance, rfl⟩).liftOfLE
    i (hG.range_torus_le_of_oppositeFactorPairs i hT hi hE hj hroots)

/-- The constructed torus homomorphism has the original ambient inclusion. -/
theorem torusLiftOfOppositeFactorPairs_comp
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hroots : ∀ a ∈ relativeRoots i,
      RelativeRoot.subgroup i a ≤ SubgroupFunctor.range j) :
    torusLiftOfOppositeFactorPairs i hG hT hi hE hj hroots ≫ j = i := by
  unfold torusLiftOfOppositeFactorPairs
  exact SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _

end Langlands.GroupScheme
