import Langlands.GroupScheme.Reductive.NormalRootDichotomyProof
import Langlands.GroupScheme.Reductive.RootGenerationProof
import Langlands.GroupScheme.Reductive.RootGeneratedCentralizer
import Langlands.GroupScheme.Reductive.NormalSemisimpleProof
import Langlands.GroupScheme.Reductive.MinimalNormalFactor
import Langlands.GroupScheme.Reductive.NormalCentralizer
import Langlands.GroupScheme.Reductive.RootPairNoncommutation
import Langlands.GroupScheme.Reductive.AlmostSimple

/-! # Almost simplicity from linked roots

Let `G` be a nontrivial semisimple group over an algebraically closed field with a split maximal
torus `t`. Call two roots linked when their root subgroups fail to commute on some test scheme.
If every two roots are joined by a chain of linked roots, then `G` is almost simple
(`isAlmostSimple_of_rootsLinked`).

For a smooth connected closed normal subgroup `H`, the Library's normal-root dichotomy puts
every root subgroup inside `H` or in the centralizer of `H`. Two linked roots cannot be of
different kinds, so either every root subgroup lies in `H`, and root generation gives `H = G`,
or every root subgroup centralizes `H`, and then `H` is central, semisimple and commutative,
hence trivial.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

section Linked

variable [IsAffineHom G.X.hom]

/-- Two roots of `t` are linked when their root subgroups do not commute on some test scheme. -/
def RootsLinked (t : T.toGrp ⟶ G) (α β : characterLattice T) : Prop :=
  α ∈ relativeRoots t ∧ β ∈ relativeRoots t ∧
    ∃ Z : Over (Spec (CommRingCat.of k)), RootPairNoncommutation.NotCommuteOver
      (RelativeRoot.subgroup t α) (RelativeRoot.subgroup t β) Z

/-- Linking is symmetric. -/
theorem RootsLinked.symm {t : T.toGrp ⟶ G} {α β : characterLattice T}
    (h : RootsLinked t α β) : RootsLinked t β α := by
  obtain ⟨hα, hβ, Z, x, hx, y, hy, hxy⟩ := h
  exact ⟨hβ, hα, Z, y, hy, x, hx, fun hyx => hxy hyx.symm⟩

/-- A coordinate functional detects the strict-combination condition: if `f β = -1`, `f β' = 2`
and `f ≥ -2` on all roots, then no strict combination `n β - m β'` is zero or a root. -/
theorem strict_combinations_of_coordinate {i : T.toGrp ⟶ G} (f : characterLattice T →+ ℤ)
    {β β' : characterLattice T} (hβ : f β = -1) (hβ' : f β' = 2)
    (hbound : ∀ χ ∈ roots i, -2 ≤ f χ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • β + m • (-β') ≠ 0 ∧ n • β + m • (-β') ∉ roots i := by
  have hf : f (n • β + m • (-β')) = -(n : ℤ) - 2 * m := by
    rw [map_add, map_nsmul, map_nsmul, map_neg, hβ, hβ', nsmul_eq_mul, nsmul_eq_mul]
    ring
  refine ⟨fun h0 => ?_, fun hmem => ?_⟩
  · rw [h0, map_zero] at hf
    omega
  · have := hbound _ hmem
    omega

/-- **Linked roots from an obtuse pair.** Over an infinite field, let `β = P.root r` and
`β' = P.root r'` be roots of a split maximal torus of a connected reductive group, realized by
a root datum `P`, with `⟨β, β'^∨⟩ = -1` and no strict combination `n β - m β'` zero or a root.
Then `β` and `β'` are linked. -/
theorem rootsLinked_of_pairing_eq_neg_one [Infinite k] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i) {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    {r r' : J} (hpair : P.pairing r r' = -1)
    (hstrict : ∀ n m : ℕ, 0 < n → 0 < m →
      n • P.root r + m • (-P.root r') ≠ 0 ∧ n • P.root r + m • (-P.root r') ∉ roots i) :
    RootsLinked i (P.root r) (P.root r') := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, -1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  let Z : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let φ : k ≃+* Γ(Z.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have hc0 : φ c ≠ 0 := fun h => hc.1 (φ.injective (h.trans (map_zero φ).symm))
  have hu : IsUnit (1 + φ c) := by
    rw [← map_one φ, ← map_add]
    refine IsUnit.map φ (Ne.isUnit fun h => hc.2 ?_)
    linear_combination h
  refine ⟨(show P.root r ∈ roots i from hP.2.1 ▸ Set.mem_range_self r),
    (show P.root r' ∈ roots i from hP.2.1 ▸ Set.mem_range_self r'), Z,
    RootPairNoncommutation.exists_not_commute hG hT hi hP hpair hstrict (φ c) hc0 hu⟩

end Linked

section Noncommuting

variable {H : GroupScheme (Spec (CommRingCat.of k))} (h : H ⟶ G)
  {F F' : SubgroupFunctor G} {Z : Over (Spec (CommRingCat.of k))}

/-- A subgroup functor inside the range of `h` commutes with one centralizing `h`. -/
theorem RootPairNoncommutation.NotCommuteOver.false_of_le_range_of_le_fixedSubgroup
    (hnc : RootPairNoncommutation.NotCommuteOver F F' Z)
    (hF : F ≤ SubgroupFunctor.range h)
    (hF' : F' ≤ (AutomorphicAction.conjugation h).fixedSubgroup) : False := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 (hF Z hx)
  have hc := (mem_conjugation_fixedSubgroup_iff h y).mp (hF' Z hy) Z (𝟙 Z) z
  rw [Category.id_comp] at hc
  exact hxy hc

/-- A subgroup functor centralizing `h` commutes with one inside the range of `h`. -/
theorem RootPairNoncommutation.NotCommuteOver.false_of_le_fixedSubgroup_of_le_range
    (hnc : RootPairNoncommutation.NotCommuteOver F F' Z)
    (hF : F ≤ (AutomorphicAction.conjugation h).fixedSubgroup)
    (hF' : F' ≤ SubgroupFunctor.range h) : False := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 (hF' Z hy)
  have hc := (mem_conjugation_fixedSubgroup_iff h x).mp (hF Z hx) Z (𝟙 Z) z
  rw [Category.id_comp] at hc
  exact hxy hc.symm

end Noncommuting

variable [IsAlgClosed k]

/-- **Almost simplicity from linked roots.** A nontrivial semisimple group over an
algebraically closed field is almost simple when, for a split maximal torus, every two roots are
joined by a chain of roots whose consecutive root subgroups do not commute. -/
theorem isAlmostSimple_of_rootsLinked (hG : IsSemisimple G) (t : T.toGrp ⟶ G)
    (hsplit : IsSplitSubtorus t) (hmax : IsMaximalTorus t)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥)
    (hlink : letI : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
      ∀ α ∈ relativeRoots t, ∀ β ∈ relativeRoots t,
        Relation.ReflTransGen (RootsLinked t) α β) :
    IsAlmostSimple G := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  refine ⟨hG, hG.noncommutative_of_range_ne_bot hnt, ?_⟩
  intro H h hh hs hc hn
  let : Smooth H.X.hom := hs
  let : ConnectedSpace H.X.left := hc
  let : IsAffineHom H.X.hom := hh.isAffineHom
  let : IsClosedImmersion h.hom.hom.left := hh
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  have hdich := semisimpleNormalRootDichotomy k G hG T t hsplit hmax H h hh hn
  -- Containment in `H` propagates along linked roots.
  have hprop : ∀ α β, Relation.ReflTransGen (RootsLinked t) α β →
      RelativeRoot.subgroup t α ≤ SubgroupFunctor.range h →
      RelativeRoot.subgroup t β ≤ SubgroupFunctor.range h := by
    intro α β hαβ hα
    induction hαβ with
    | refl => exact hα
    | tail _ hbc ih =>
      obtain ⟨-, hc', Z, hnc⟩ := hbc
      rcases hdich _ hc' with hIn | hFix
      · exact hIn
      · exact (hnc.false_of_le_range_of_le_fixedSubgroup h ih hFix).elim
  by_cases hex : ∃ α ∈ relativeRoots t, RelativeRoot.subgroup t α ≤ SubgroupFunctor.range h
  · right
    obtain ⟨α, hα, hαH⟩ := hex
    exact semisimpleRootGeneration k G hG T t hsplit hmax H h hh fun β hβ =>
      hprop α β (hlink α hα β hβ) hαH
  · left
    have hfixed : ∀ β ∈ relativeRoots t,
        RelativeRoot.subgroup t β ≤ (AutomorphicAction.conjugation h).fixedSubgroup :=
      fun β hβ => (hdich β hβ).resolve_left fun hIn => hex ⟨β, hβ, hIn⟩
    have hcentral : (AutomorphicAction.conjugation h).fixedSubgroup = ⊤ :=
      (AutomorphicAction.conjugation h).fixedSubgroup_eq_top_of_rootGeneration
        semisimpleRootGeneration hG T t hsplit hmax inferInstance hfixed
    have hH : IsSemisimple H := hG.of_normalSubgroup h hh hn
    have hcomm : ∀ (W : Over (Spec (CommRingCat.of k))) (x y : W ⟶ H.X), Commute x y := by
      intro W x y
      apply (commute_iff_eq _ _).mpr
      apply (cancel_mono h.hom.hom).mp
      have hm : y ≫ h.hom.hom ∈
          (AutomorphicAction.conjugation h).fixedSubgroup.carrier W := by
        rw [hcentral]
        trivial
      have he := (mem_conjugation_fixedSubgroup_iff h _).mp hm W (𝟙 W) x
      simpa only [Category.id_comp, MonObj.mul_comp] using he.eq
    have hzH : SubgroupFunctor.range (𝟙 H) = ⊥ := by
      by_contra hnt'
      exact hH.noncommutative_of_range_ne_bot hnt' hcomm
    simpa only [Category.id_comp] using
      (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) h).mpr hzH

end Langlands.GroupScheme
