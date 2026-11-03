import Langlands.GroupScheme.Rational.RelativeTitsSystemStatement
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Relative Tits nondegeneracy from actual nontrivial simple-root points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] (ν : cocharacterLattice T)

/-- Actual nontrivial rational points of the simple-root subgroup functors.
This is input data; its intrinsic existence is a separate geometric obligation. -/
structure RelativeSimpleRootPointData where
  point : simpleRelativeRoots i ν →
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
  mem : ∀ a, point a ∈ (RelativeRoot.subgroup i a.val).carrier (Over.mk (𝟙 _))
  ne_one : ∀ a, point a ≠ 1

omit [IsAffineHom G.X.hom] in
/-- Negating a cocharacter is inversion of its Gm parameter. -/
theorem groupHom_neg_comp_eq_oppositeCocharacter :
    CommGroupScheme.groupHom (-ν) ≫ i =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i) := by
  have hν : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ν = -ν := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  rw [Dynamic.oppositeCocharacter, ← Category.assoc]
  change CommGroupScheme.groupHom (-ν) ≫ i =
    CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ i
  rw [hν]

variable [Mono i.hom.hom.left]

/-- A root-span reflection represented by a normalizing point sends the actual
character to its negative when the torus is split. -/
theorem IsRelativeReflection.weylAction_apply_self (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (n : normalizerPoints i)
    (hn : IsRelativeReflection i a (QuotientGroup.mk n)) :
    weylAction i n a = -a := by
  apply hT.character_toRat_injective
  have h := congrArg Subtype.val hn.relativeWeylAction_apply_self
  change toRat (weylAction i n a) = -toRat a at h
  rw [map_neg]
  exact h

/-- Every nontrivial rational point of a simple positive root subgroup witnesses
nondegeneracy for every representative of its relative reflection. -/
theorem relativeTits_conj_not_mem_of_rootPoint (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (ha : a ∈ simpleRelativeRoots i ν)
    (n : normalizerPoints i) (hn : IsRelativeReflection i a (QuotientGroup.mk n))
    {b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hb : b ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))) (hb1 : b ≠ 1) :
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b *
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∉
      standardParabolicPoints i ν ∅ := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hna := hn.weylAction_apply_self i hT n
  have hroot : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b *
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∈
      (RelativeRoot.subgroup i (-a)).carrier (Over.mk (𝟙 _)) := by
    have h := RelativeRoot.normalizer_conj_mem i a n hb
    simpa only [G.constantPoint_self, hna] using h
  have hpos : 0 < latticePairing T (-a) (-ν) := by
    simpa using ha.1.2
  have hminus := RelativeRoot.subgroup_le_dynamicUnipotent i (-ν) hpos _ hroot
  rw [groupHom_neg_comp_eq_oppositeCocharacter i ν] at hminus
  intro hB
  have hplus := standardParabolic_empty_le i ν _ hB
  have h1 := Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
    (CommGroupScheme.groupHom ν ≫ i) hminus hplus
  apply hb1
  have h := congrArg (fun x =>
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ * x *
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) h1
  simpa [mul_assoc] using h

/-- Actual nontrivial simple-root points imply the full representative-form
nondegeneracy field of the relative Tits system. -/
theorem RelativeSimpleRootPointData.conj_not_le
    (D : RelativeSimpleRootPointData i ν) (hT : IsSplitTorus T.toGrp) :
    ∀ s ∈ simpleRelativeReflections i ν, ∀ n : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
        ∃ b ∈ standardParabolicPoints i ν ∅,
          (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b *
            (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∉
            standardParabolicPoints i ν ∅ := by
  intro s hs n hn
  obtain ⟨a, ha, has⟩ := hs
  have hna : IsRelativeReflection i a (QuotientGroup.mk n) := by
    change IsRelativeReflection i a
      (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n)
    rw [hn]
    exact has
  exact ⟨D.point ⟨a, ha⟩,
    RelativeRoot.subgroup_le_standardParabolic_empty i ν ha _ (D.mem ⟨a, ha⟩),
    relativeTits_conj_not_mem_of_rootPoint i ν hT ha n hna (D.mem ⟨a, ha⟩)
      (D.ne_one ⟨a, ha⟩)⟩

end Langlands.GroupScheme
