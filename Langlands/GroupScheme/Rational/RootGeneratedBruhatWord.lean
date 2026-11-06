import Langlands.GroupScheme.Rational.RootGeneratedBruhatCovering
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductReduction

/-! # The actual simple-root step in the Bruhat word argument -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)

/-- The factorization of `U(ν)` used by the simple-root word step. -/
def HasSimpleRootUnipotentFactorization : Prop :=
  ∀ a ∈ simpleRelativeRoots i ν, ∀ n : normalizerPoints i,
    IsRelativeReflection i a (QuotientGroup.mk n) →
    ∀ u ∈ RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i),
      ∃ q ∈ RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i),
        n.val * q * n.val⁻¹ ∈ RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i) ∧
        ∃ x ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)), u = q * x

/-- Put the simple root last in an ordered root-point product. All preceding
factors stay positive under the simple reflection. -/
theorem hasSimpleRootUnipotentFactorization_of_orderedRootPoints
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ a ∈ relativeRoots i, -a ∈ relativeRoots i)
    (hli : LinearIndependent ℚ
      (fun a : simpleRelativeRoots i ν => toRat (a : characterLattice T)))
    (hfin : (relativeRoots i).Finite)
    (hprod : HasOrderedRootPointFactorization i ν) :
    HasSimpleRootUnipotentFactorization i ν := by
  intro a ha n hs u hu
  classical
  have haI := simpleRelativeRoot_mem_indivisiblePositiveRoots hli ha
  obtain ⟨l, e0, hinj, hrange⟩ :=
    RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots i ν hfin
  obtain ⟨r₀, hr₀⟩ : a ∈ Set.range e0 := by rw [hrange]; exact haI
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by have := r₀.pos; omega⟩
  let e1 : Fin (m + 1) → characterLattice T := e0 ∘ Equiv.swap r₀ (Fin.last m)
  have hinj1 : Function.Injective e1 := hinj.comp (Equiv.injective _)
  have hrange1 : Set.range e1 = RelativeRoot.indivisiblePositiveRoots i ν := by
    rw [← hrange]
    exact EquivLike.range_comp e0 (Equiv.swap r₀ (Fin.last m))
  have hlast : e1 (Fin.last m) = a := by
    simp only [e1, Function.comp_apply, Equiv.swap_apply_right, hr₀]
  obtain ⟨g, hg, hgu⟩ := hprod (m + 1) e1 hinj1 hrange1 u hu
  rw [List.ofFn_succ', List.prod_concat] at hgu
  refine ⟨(List.ofFn fun r : Fin m => g r.castSucc).prod, ?_, ?_,
    g (Fin.last m), ?_, hgu⟩
  · refine list_prod_mem fun x hx => ?_
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx
    have hc : e1 r.castSucc ∈ RelativeRoot.indivisiblePositiveRoots i ν := by
      rw [← hrange1]
      exact ⟨_, rfl⟩
    exact RelativeRoot.subgroup_le_dynamicUnipotent i ν hc.2 _ (hg r.castSucc)
  · rw [← MulAut.conj_apply, map_list_prod]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
    rw [MulAut.conj_apply]
    have hc := RelativeRoot.normalizer_conj_mem i _ n (hg r.castSucc)
    simp only [GroupScheme.constantPoint_self] at hc
    refine RelativeRoot.subgroup_le_dynamicUnipotent i ν ?_ _ hc
    refine pairing_weylAction_pos_of_isRelativeReflection hν hneg hli ha n hs ?_ ?_
    · rw [← hrange1]
      exact ⟨_, rfl⟩
    · rw [← hlast]
      exact fun h => (Fin.castSucc_lt_last r).ne (hinj1 h)
  · rw [← hlast]
    exact hg (Fin.last m)

/-- The actual-root rank-one step, with the middle subgroup kept arbitrary.
The opposite-pair and middle-subgroup containment inputs remain explicit. -/
theorem mul_mem_rootGenerated_doubleCosets_of_simpleReflection
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (hfac : HasSimpleRootUnipotentFactorization i ν)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    (M : Subgroup (rationalPoints G)) (hMN : M ≤ normalizerPoints i)
    {a : characterLattice T} (ha : a ∈ simpleRelativeRoots i ν)
    (n : normalizerPoints i) (hs : IsRelativeReflection i a (QuotientGroup.mk n))
    (hnM : n.val ∈ M)
    (hM : normalizerPoints i ⊓ Subgroup.closure
      (((RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) : Set (rationalPoints G)) ∪
        (RelativeRoot.subgroup i (-a)).carrier (Over.mk (𝟙 _))) ≤ M)
    {g : rationalPoints G}
    (hg : g ∈ Langlands.Group.RankOneBruhat.doubleCosets
      (RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)) M) :
    n.val * g ∈ Langlands.Group.RankOneBruhat.doubleCosets
      (RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)) M := by
  have hflip : weylAction i n a = -a := by
    apply hT.character_toRat_injective
    have h := congrArg Subtype.val hs.relativeWeylAction_apply_self
    change toRat (weylAction i n a) = -toRat a at h
    simpa only [map_neg] using h
  refine Langlands.Group.RankOneBruhat.mul_mem_doubleCosets_of_rankOne hnM
    ((RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)))
    ((RelativeRoot.subgroup i (-a)).carrier (Over.mk (𝟙 _)))
    {q | n.val * q * n.val⁻¹ ∈
      RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)} ?_ ?_ ?_ ?_ ?_ hg
  · intro u hu
    obtain ⟨q, -, hq, x, hx, heq⟩ := hfac a ha n hs u hu
    exact ⟨q, hq, x, hx, heq⟩
  · intro q hq
    exact hq
  · intro x hx
    have hc := RelativeRoot.normalizer_conj_mem i (-a) n hx
    simp only [GroupScheme.constantPoint_self, map_neg, hflip, neg_neg] at hc
    exact RelativeRoot.subgroup_le_dynamicUnipotent i ν ha.1.2 _ hc
  · exact RelativeRoot.rootPoint_factorization_of_oppositeFactorPairs i hE M ha.1.1 hM
  · intro n' hn'
    exact RelativeRoot.rootPoint_conjugation_sign i ν hν ha.1.1 ⟨n', hMN hn'⟩

end Langlands.GroupScheme
