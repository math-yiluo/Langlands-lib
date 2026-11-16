import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationProof
import Langlands.GroupScheme.Reductive.TitsIndexRankOneOrbit
import Langlands.GroupScheme.Quaternionic.LocalScalarQuadraticWittIndexOne
import Langlands.Algebra.LocalUnitaryResidue

/-! # The exact marked vertex and quaternionic spin model in local rank-one type D -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An actual spin presentation by a quaternionic quadratic form in `n`
variables, with an orthogonal first-kind involution and Witt index one. -/
structure LocalRankOneTypeDPresentation (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ) where
  divisionAlgebra : Type u
  [divisionRing : DivisionRing divisionAlgebra]
  [algebra : Algebra K divisionAlgebra]
  [finiteDimensional : FiniteDimensional K divisionAlgebra]
  [central : Algebra.IsCentral K divisionAlgebra]
  finrank_eq_four : Module.finrank K divisionAlgebra = 4
  involution : Quaternionic.FirstKindInvolution K divisionAlgebra
  symmetric_finrank : Module.finrank K involution.symmetricSubspace = 3
  form : involution.QuadraticForms (Fin n)
  nondegenerate : involution.IsNondegenerateQuadratic form
  wittIndex_eq_one : involution.quadraticWittIndex form = 1
  cover : G ⟶ involution.isometryGroup form
  isSpinCover : involution.IsSpinCover form cover

attribute [instance] LocalRankOneTypeDPresentation.divisionRing
  LocalRankOneTypeDPresentation.algebra LocalRankOneTypeDPresentation.finiteDimensional
  LocalRankOneTypeDPresentation.central

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- For a local simply connected absolutely almost-simple group of type
`D_n`, `n ≥ 4`, whose full star action fixes the nonfork vertices, split rank
one supplies a quaternionic spin model and precisely vertex 2 marked.
This theorem does not bound `n` from above or determine the action on the fork. -/
theorem localRankOneTypeD_presentation_and_marking
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 4 ≤ n)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hfix : ∀ (γ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star γ a = a)
    (hrank : splitRank G = 1) :
    Nonempty (LocalRankOneTypeDPresentation K G n) ∧
      d.IsNumberingOf (CartanMatrix.D n) (fun i => i.val = 1) e := by
  obtain ⟨D, _, _, _, _, degree, m, hdegree, hfin, hmd, σ, hsym, q,
      hq, hw, hmarked, π, hπ⟩ :=
    classicalTypeDSpinPresentation K G d n e hn hsc haas hcartan hfix
  have hw1 : σ.quadraticWittIndex q = 1 := by
    rw [hrank] at hw
    exact_mod_cast hw
  have hτ : Langlands.IsUnitaryInvolution (⇑(RingHom.id K)) (⇑σ) :=
    ⟨σ.map_add, σ.map_mul, σ.apply_apply, σ.map_algebraMap⟩
  have hbound : degree ∣ 2 := by
    have h := Langlands.UnitaryInvolution.reducedDegree_dvd_two
      (L := K) (D := D) (σ := RingHom.id K) (τ := ⇑σ) (fun _ => rfl) hτ
    simpa [Langlands.CentralSimple.reducedDegree, hfin, pow_two, Nat.sqrt_eq] using h
  have hd2 : degree = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hbound with hd1 | hd2
    · have hD1 : Module.finrank K D = 1 := by simpa [hd1] using hfin
      have hm6 := σ.card_le_six_of_finrank_one_and_quadraticWittIndex_one hD1 hq hw1
      simp only [Fintype.card_fin] at hm6
      rw [hd1, mul_one] at hmd
      omega
    · exact hd2
  have hmn : m = n := by
    rw [hd2] at hmd
    omega
  subst m
  have hD4 : Module.finrank K D = 4 := by simpa [hd2] using hfin
  have hσ3 : Module.finrank K σ.symmetricSubspace = 3 := by simpa [hd2] using hsym
  refine ⟨⟨{
    divisionAlgebra := D
    finrank_eq_four := hD4
    involution := σ
    symmetric_finrank := hσ3
    form := q
    nondegenerate := hq
    wittIndex_eq_one := hw1
    cover := π
    isSpinCover := hπ }⟩, hcartan, ?_⟩
  let v : d.Vertex := e.symm ⟨1, by omega⟩
  have hv : (e v).val = 1 := by simp [v]
  have hvnonfork : (e v).val + 2 < n := by omega
  have hvmarked : v ∈ d.distinguishedVertices := by
    apply (hmarked v hvnonfork).mpr
    exact ⟨1, by omega, by omega, by omega⟩
  intro a
  constructor
  · intro ha
    obtain ⟨γ, hγ⟩ := d.exists_star_eq_of_rank_one hrank ⟨v, hvmarked⟩ ⟨a, ha⟩
    change d.star γ v = a at hγ
    rw [hfix γ v hvnonfork] at hγ
    rwa [← hγ]
  · intro ha
    apply (hmarked a (by omega)).mpr
    exact ⟨1, by omega, by omega, by omega⟩

/-- Choose the actual quaternionic spin presentation supplied by the local
rank-one theorem for a type-D numbering with fixed nonfork vertices. -/
def localRankOneTypeDPresentation
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 4 ≤ n)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hfix : ∀ (γ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star γ a = a)
    (hrank : splitRank G = 1) : LocalRankOneTypeDPresentation K G n :=
  Classical.choice
    (localRankOneTypeD_presentation_and_marking d e hn hsc haas hcartan hfix hrank).1

end Langlands.GroupScheme
