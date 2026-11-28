import Langlands.GroupScheme.Rational.TripleParabolicDescent
import Langlands.GroupScheme.Rational.SplitTorusGaloisComparison
import Langlands.GroupScheme.Rational.TrialitarianStarLeafCycle
import Langlands.GroupScheme.Reductive.TypeD4LeafCoweightOrbits
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient

/-! # Descent of the Levi subgroup cut out by the three leaf parabolics of a trialitarian group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [Algebra K (SeparableClosure F)] [IsScalarTower F K (SeparableClosure F)]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj H).X.hom]

/-- The inverse ordinary Galois action of a lift whose star permutation sends one leaf to
another carries the corresponding leaf cocharacters into one Weyl orbit. -/
theorem TitsIndexData.exists_weyl_galoisAction_inv_leafCoweights (d : TitsIndexData H)
    (hsc : IsSimplyConnected H) (q : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b))
    (τ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (k k' : Fin 3)
    (hk : d.star τ (q.symm (d4LeafParabolicVertex k)) = q.symm (d4LeafParabolicVertex k')) :
    ∃ w : d.pinning.toSplitPinning.rootDatum.Aut,
      w ∈ d.pinning.toSplitPinning.rootDatum.weylGroup ∧
      ((d.pinning.galoisAction τ)⁻¹).coweightEquiv
          (d4LeafParabolicCoweights d.pinning.toSplitPinning.rootDatum
            d.pinning.toSplitPinning.base q k) =
        w.coweightEquiv (d4LeafParabolicCoweights d.pinning.toSplitPinning.rootDatum
          d.pinning.toSplitPinning.base q k') := by
  have hspan := d.pinning_corootSpan_eq_top hsc
  have : d.pinning.toSplitPinning.rootDatum.IsReduced := d.pinning.isReduced
  have hD' : ∀ i j : d.pinning.toSplitPinning.base.support,
      d.pinning.toSplitPinning.rootDatum.pairing i.val j.val = CartanMatrix.D 4 (q i) (q j) :=
    fun i j => hD i j
  set x := (d.pinning.starAction τ).val with hxdef
  have hx : ∀ a, a ∈ d.pinning.toSplitPinning.base.support ↔
      x.indexEquiv a ∈ d.pinning.toSplitPinning.base.support :=
    (d.pinning.starAction τ).property
  have hxk : x.indexEquiv (q.symm (d4LeafParabolicVertex k)).val =
      (q.symm (d4LeafParabolicVertex k')).val :=
    congrArg Subtype.val hk
  obtain ⟨w₁, hw₁, h₁⟩ := exists_weyl_inv_coweightEquiv_leafParabolicCoweights
    d.pinning.toSplitPinning.rootDatum d.pinning.toSplitPinning.base hspan q hD' x hx k k' hxk
  obtain ⟨wτ, hwτ⟩ := d.pinning.exists_weyl_mul_galoisAction_eq_starAction τ
  have hg : (d.pinning.galoisAction τ)⁻¹ = x⁻¹ * wτ.val := by
    rw [hxdef, ← hwτ]
    group
  refine ⟨w₁ * wτ.val, mul_mem hw₁ wτ.property, ?_⟩
  rw [hg]
  change wτ.val.coweightEquiv ((x⁻¹).coweightEquiv _) = wτ.val.coweightEquiv (w₁.coweightEquiv _)
  rw [h₁]

/-- Roots of a split torus with an actual root datum, read through a root-matching lattice
isomorphism. -/
theorem exists_root'_of_mem_relativeRoots {L : Type u} [Field L]
    {G : GroupScheme (Spec (CommRingCat.of L))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of L))} {s : S.toGrp ⟶ G}
    {J I Y' : Type*} [AddCommGroup Y'] {X' : Type*} [AddCommGroup X']
    {P : RootDatum J (characterLattice S) (cocharacterLattice S)} (hP : IsRootDatumOf s P)
    (Q : RootDatum I X' Y') (e : J ≃ I) (θ : cocharacterLattice S ≃+ Y')
    (hroot : ∀ j ν, P.root' j ν = Q.root' (e j) (θ ν))
    {α : characterLattice S} (hα : α ∈ relativeRoots s) :
    ∃ i : I, ∀ ν, latticePairing S α ν = Q.root' i (θ ν) := by
  rw [relativeRoots_eq_roots, ← hP.2.1] at hα
  obtain ⟨j, rfl⟩ := hα
  refine ⟨e j, fun ν => ?_⟩
  rw [← hroot, ← hP.1]

set_option maxHeartbeats 1600000 in
omit [IsScalarTower F K (SeparableClosure F)] in
/-- The Levi descent of the first stage: for a simply connected group of type `D₄` whose
star action is the leaf three-cycle for a lift of a generator of a cyclic cubic Galois group,
comparison data for a split maximal torus over the cubic field give a closed connected
reductive subgroup over the ground field whose base change is a rational conjugate of the
dynamic centralizer of the difference of the first two leaf cocharacters. -/
theorem TitsIndexData.exists_leafLevi_descent [Infinite F] [FiniteDimensional F K]
    [IsGalois F K] (d : TitsIndexData H) (hsc : IsSimplyConnected H) (q : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b))
    {S : CommGroupScheme (Spec (CommRingCat.of K))} (hS : IsSplitTorus S.toGrp)
    (s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj H)
    {J : Type u} {P : RootDatum J (characterLattice S) (cocharacterLattice S)}
    (hP : IsRootDatumOf s P) (e : J ≃ d.pinning.rootIndex)
    (θ : cocharacterLattice S ≃+ cocharacterLattice d.pinning.toSplitPinning.torus)
    (hroot : ∀ j ν, P.root' j ν = d.pinning.toSplitPinning.rootDatum.root' (e j) (θ ν))
    (htrans : ∀ (σ : K ≃ₐ[F] K) (τ : SeparableClosure F ≃ₐ[F] SeparableClosure F),
      (∀ x : K, τ (algebraMap K (SeparableClosure F) x) =
        algebraMap K (SeparableClosure F) (σ x)) →
      ∀ (ν ν' : cocharacterLattice S) (w : d.pinning.toSplitPinning.rootDatum.Aut),
        w ∈ d.pinning.toSplitPinning.rootDatum.weylGroup →
        ((d.pinning.galoisAction τ)⁻¹).coweightEquiv (θ ν) = w.coweightEquiv (θ ν') →
        ∃ m : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj H),
          SubgroupFunctor.galoisTransport F K H σ
              (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ s)) =
            Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ s ≫
              (((GroupScheme.baseChange (algebraBaseMap F K)).obj H).innerIso m).hom))
    (σ : K ≃ₐ[F] K) (τ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (hστ : ∀ x : K, τ (algebraMap K (SeparableClosure F) x) =
      algebraMap K (SeparableClosure F) (σ x))
    (hgen : ∀ ρ : K ≃ₐ[F] K, ∃ n : ℕ, ρ = σ ^ n) (hσ3 : σ ^ 3 = 1)
    (h01 : (1 : K ≃ₐ[F] K) ≠ σ) (h02 : (1 : K ≃ₐ[F] K) ≠ σ ^ 2) (h12 : σ ≠ σ ^ 2)
    (hτ0 : d.star τ (q.symm 0) = q.symm 2) (hτ2 : d.star τ (q.symm 2) = q.symm 3) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of F))) (j : C ⟶ H)
      (h : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj H)),
      IsClosedSubgroup j ∧ IsConnectedReductive C ∧
        SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F K)).map j) =
          Dynamic.centralizer (CommGroupScheme.groupHom
              (θ.symm (d4LeafParabolicCoweights d.pinning.toSplitPinning.rootDatum
                  d.pinning.toSplitPinning.base q 0 -
                d4LeafParabolicCoweights d.pinning.toSplitPinning.rootDatum
                  d.pinning.toSplitPinning.base q 1)) ≫ s ≫
            (((GroupScheme.baseChange (algebraBaseMap F K)).obj H).innerIso h).hom) := by
  classical
  set Q := d.pinning.toSplitPinning.rootDatum with hQ
  set b := d.pinning.toSplitPinning.base
  have hspan : Q.corootSpan ℤ = ⊤ := d.pinning_corootSpan_eq_top hsc
  have : Q.IsReduced := d.pinning.isReduced
  have hD' : ∀ i j : b.support, Q.pairing i.val j.val = CartanMatrix.D 4 (q i) (q j) :=
    fun i j => hD i j
  have hM : IsConnectedReductive H := hsc.isSemisimple.isConnectedReductive
  let lam : Fin 3 → cocharacterLattice d.pinning.toSplitPinning.torus :=
    d4LeafParabolicCoweights Q b q
  let ν : Fin 3 → cocharacterLattice S := fun k => θ.symm (lam k)
  have hθν (k : Fin 3) : θ (ν k) = lam k := AddEquiv.apply_symm_apply θ (lam k)
  have hsum : ν 0 + ν 1 + ν 2 = 0 := by
    have h := d4LeafParabolicCoweights_sum Q b q
    rw [Fin.sum_univ_three] at h
    simp only [ν, ← map_add]
    rw [show lam 0 + lam 1 + lam 2 = 0 from h, map_zero]
  have hneg : ∀ α ∈ relativeRoots s, (∀ i, latticePairing S α (ν i) = 0) ∨
      ∃! i, latticePairing S α (ν i) < 0 := by
    intro α hα
    obtain ⟨i, hi⟩ := exists_root'_of_mem_relativeRoots hP Q e θ hroot hα
    simp only [hi, hθν]
    exact d4LeafParabolicCoweights_negative_unique Q b hspan q hD' i
  have hzero : ∀ α ∈ relativeRoots s, latticePairing S α (ν 0 - ν 1) = 0 →
      ∀ i, latticePairing S α (ν i) = 0 := by
    intro α hα
    obtain ⟨i, hi⟩ := exists_root'_of_mem_relativeRoots hP Q e θ hroot hα
    intro hz k
    rw [hi, map_sub θ, hθν, hθν] at hz
    rw [hi, hθν]
    exact (d4LeafParabolicCoweights_difference_eq_zero_iff Q b hspan q hD' i).mp hz k
  -- The types of the transported leaf parabolics.
  have hστ2 : ∀ x : K, (τ ^ 2) (algebraMap K (SeparableClosure F) x) =
      algebraMap K (SeparableClosure F) ((σ ^ 2) x) := by
    intro x
    rw [pow_two, pow_two, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hστ, hστ]
  have hτ2' : d.star (τ ^ 2) (q.symm 0) = q.symm 3 := by
    rw [pow_two, d.star_mul, hτ0, hτ2]
  obtain ⟨v₁, hv₁, hcv₁⟩ := d.exists_weyl_galoisAction_inv_leafCoweights hsc q hD τ 0 1 hτ0
  obtain ⟨v₂, hv₂, hcv₂⟩ := d.exists_weyl_galoisAction_inv_leafCoweights hsc q hD (τ ^ 2) 0 2
    hτ2'
  obtain ⟨m₁, hm₁⟩ := htrans σ τ hστ (ν 0) (ν 1) v₁ hv₁ (by rw [hθν, hθν]; exact hcv₁)
  obtain ⟨m₂, hm₂⟩ := htrans (σ ^ 2) (τ ^ 2) hστ2 (ν 0) (ν 2) v₂ hv₂
    (by rw [hθν, hθν]; exact hcv₂)
  obtain ⟨C, j, h, hj, hC, hrange⟩ := exists_tripleParabolic_descent σ hgen hσ3 h01 h02 h12 H hM
    hS s ν hsum hneg hzero m₁ m₂ hm₁ hm₂
  refine ⟨C, j, h, hj, hC, ?_⟩
  rw [hrange, map_sub]

end Langlands.GroupScheme
