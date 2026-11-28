import Langlands.GroupScheme.Rational.TrialitarianLeafDescent
import Langlands.GroupScheme.Absolute.RegularCocharacterBorel
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.LinearAlgebra.TypeA2ParabolicTriple

/-! # Split maximal-torus descent from a cubic-split Levi with six coroots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra

namespace Langlands.GroupScheme

variable {F K E : Type u} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
  [Algebra K E] [IsScalarTower F K E]
  {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.hom]
  (p : GaloisPinningData F E M)

private theorem exists_weyl_galoisAction_inv_a2ParabolicCocharacters
    (a b : p.rootIndex) (hab : p.rootDatum.pairing a b = -1)
    (hba : p.rootDatum.pairing b a = -1)
    (hcase : ∀ i, ∃ j, p.rootDatum.coroot i =
      a2Coroots (p.rootDatum.coroot a) (p.rootDatum.coroot b) j)
    (τ : E ≃ₐ[F] E) (hτ : (p.starAction τ) ^ 3 = 1) (k : Fin 3) :
    ∃ w : p.toSplitPinning.rootDatum.Aut, w ∈ p.toSplitPinning.rootDatum.weylGroup ∧
      ((p.galoisAction τ)⁻¹).coweightEquiv
          (a2ParabolicCocharacters (p.rootDatum.coroot a) (p.rootDatum.coroot b) 0) =
        w.coweightEquiv
          (a2ParabolicCocharacters (p.rootDatum.coroot a) (p.rootDatum.coroot b) k) := by
  let Q := p.toSplitPinning.rootDatum
  let x := (p.starAction τ)⁻¹
  have hx : x ^ 3 = 1 := by
    change (p.starAction τ)⁻¹ ^ 3 = 1
    rw [inv_pow, hτ, inv_one]
  have hx' : x.val ^ 3 = 1 :=
    congrArg (fun z : p.toSplitPinning.basedRootDatumAut => z.val) hx
  let lam := a2ParabolicCocharacters (Q.coroot a) (Q.coroot b)
  have hlam : lam 0 ∈ Q.corootSpan ℤ := by
    change (2 : ℤ) • Q.coroot a + Q.coroot b ∈ Q.corootSpan ℤ
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a)))
      (Submodule.subset_span (Set.mem_range_self b))
  have hfix := coweightEquiv_eq_self_of_a2_of_cube_eq_one Q a b hcase p.base x.val x.property
    hx' (lam 0) hlam
  obtain ⟨v, hv, hc⟩ := exists_weyl_coweightEquiv_a2ParabolicCocharacters Q a b hab hba k
  obtain ⟨wτ, hwτ⟩ := p.exists_weyl_mul_galoisAction_eq_starAction τ
  have hg : (p.galoisAction τ)⁻¹ = x.val * wτ.val := by
    change (p.galoisAction τ)⁻¹ = ((p.starAction τ).val)⁻¹ * wτ.val
    rw [← hwτ]
    group
  refine ⟨v * wτ.val, mul_mem hv wτ.property, ?_⟩
  rw [hg]
  change wτ.val.coweightEquiv (x.val.coweightEquiv (lam 0)) =
    wτ.val.coweightEquiv (v.coweightEquiv (lam k))
  rw [hfix, hc]

section CubicDescent

variable [Infinite F] [FiniteDimensional F K] [IsGalois F K]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}

set_option maxHeartbeats 1200000 in
omit [LocallyOfFiniteType M.X.hom] in
private theorem exists_conjugate_baseChange_of_regular_triple
    (σ : K ≃ₐ[F] K) (hgen : ∀ ρ : K ≃ₐ[F] K, ∃ n : ℕ, ρ = σ ^ n) (hσ3 : σ ^ 3 = 1)
    (h01 : (1 : K ≃ₐ[F] K) ≠ σ) (h02 : (1 : K ≃ₐ[F] K) ≠ σ ^ 2) (h12 : σ ≠ σ ^ 2)
    (hM : IsConnectedReductive M) (hS : IsSplitTorus S.toGrp)
    (s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj M) (hs : IsMaximalTorus s)
    (ν : Fin 3 → cocharacterLattice S) (hsum : ν 0 + ν 1 + ν 2 = 0)
    (hneg : ∀ α ∈ relativeRoots s, ∃! i, latticePairing S α (ν i) < 0)
    (hreg : IsRegularCocharacter s (ν 0 - ν 1))
    (m₁ m₂ : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M))
    (h₁ : SubgroupFunctor.galoisTransport F K M σ
        (Dynamic.parabolic (CommGroupScheme.groupHom (ν 0) ≫ s)) =
      Dynamic.parabolic (CommGroupScheme.groupHom (ν 1) ≫ s ≫
        (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso m₁).hom))
    (h₂ : SubgroupFunctor.galoisTransport F K M (σ ^ 2)
        (Dynamic.parabolic (CommGroupScheme.groupHom (ν 0) ≫ s)) =
      Dynamic.parabolic (CommGroupScheme.groupHom (ν 2) ≫ s ≫
        (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso m₂).hom)) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ M),
      IsMaximalTorus t ∧ SubgroupConjugate ((GroupScheme.baseChange (algebraBaseMap F K)).map t) s := by
  let B := GroupScheme.baseChange (algebraBaseMap F K)
  have hMK : IsConnectedReductive (B.obj M) := connectedReductiveFieldExtensionStatement F K M hM
  obtain ⟨D, i, g, hi, hD, hrange⟩ := exists_tripleParabolic_descent σ hgen hσ3 h01 h02 h12
    M hM hS s ν hsum (fun α hα => Or.inr (hneg α hα))
    (fun α hα h => (hreg α ((relativeRoots_eq_roots s) ▸ hα) h).elim) m₁ m₂ h₁ h₂
  have hz := centralizer_comp_eq_range_of_isRegular hMK hS s hs (ν 0 - ν 1) hreg
  let c := (B.obj M).innerIso g
  let s' := s ≫ c.hom
  have hs' : IsMaximalTorus s' := hs.comp_iso c
  have : IsClosedImmersion s.hom.hom.left := hs.2.1
  have : Mono s.hom.hom := Over.mono_of_mono_left _
  have heq : SubgroupFunctor.range (B.map i) = SubgroupFunctor.range s' := by
    rw [hrange, ← Category.assoc]
    exact (range_comp_iso_eq_centralizer hz.symm c).symm
  have hiK : IsClosedSubgroup (B.map i) := hi.baseChange _
  let d := hiK.sourceIsoOfRangeEq hs'.2.1 heq
  have hd : d.hom ≫ s' = B.map i := hiK.sourceIsoOfRangeEq_hom_comp hs'.2.1 heq
  have : Smooth D.X.hom := hD.smooth
  have : IsAffineHom D.X.hom := hD.isAffineHom
  obtain ⟨T, t, ht⟩ := maximalTorusExistence F D
  let TK := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T
  have htK : IsMaximalTorus (T := TK) (B.map t) :=
    (maximalTorusBaseChange F K D T t ht.1 ht.2.1).mp ht
  have he : IsIso (B.map t ≫ d.hom) := (htK.comp_iso d).isIso_of_torus hS.isTorus
  let e : TK.toGrp ≅ S.toGrp := @asIso _ _ _ _ (B.map t ≫ d.hom) he
  have hcomp : B.map (t ≫ i) = e.hom ≫ s' := by
    rw [B.map_comp]
    change B.map t ≫ B.map i = (B.map t ≫ d.hom) ≫ s'
    rw [Category.assoc, hd]
  have hmax : IsMaximalTorus (T := TK) (B.map (t ≫ i)) := hcomp ▸ hs'.iso_comp e
  have hclosed := ht.2.1.comp hi
  have : Smooth M.X.hom := hM.smooth
  refine ⟨T, t ≫ i, (maximalTorusBaseChange F K M T (t ≫ i) ht.1 hclosed).mpr hmax, ?_⟩
  rw [hcomp]
  exact (SubgroupConjugate.iso_source e s').trans (SubgroupConjugate.conjugate s g).symm

set_option maxHeartbeats 1400000 in
omit [IsScalarTower F K E] in
/-- A split maximal torus of `M_K` descends up to conjugacy when the pinning has the
six coroots of type `A₂` and the split torus has the Galois comparison data. The order-three
star action fixes the coroot span, so the three line parabolics have the same rational
conjugacy type after each Galois transport. -/
theorem exists_a2_maximalTorus_descent
    (hM : IsConnectedReductive M)
    (s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj M) (hs : IsMaximalTorus s)
    (hS : IsSplitTorus S.toGrp) (hcmp : SplitTorusGaloisComparison F K E M p s)
    (a b : p.rootIndex) (hab : p.rootDatum.pairing a b = -1)
    (hba : p.rootDatum.pairing b a = -1)
    (hcase : ∀ i, ∃ j, p.rootDatum.coroot i =
      a2Coroots (p.rootDatum.coroot a) (p.rootDatum.coroot b) j)
    (σ : K ≃ₐ[F] K) (τ : E ≃ₐ[F] E)
    (hστ : ∀ x : K, τ (algebraMap K E x) = algebraMap K E (σ x))
    (hgen : ∀ ρ : K ≃ₐ[F] K, ∃ n : ℕ, ρ = σ ^ n) (hσ3 : σ ^ 3 = 1)
    (h01 : (1 : K ≃ₐ[F] K) ≠ σ) (h02 : (1 : K ≃ₐ[F] K) ≠ σ ^ 2) (h12 : σ ≠ σ ^ 2) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ M),
      IsMaximalTorus t ∧ SubgroupConjugate ((GroupScheme.baseChange (algebraBaseMap F K)).map t) s := by
  obtain ⟨J, P, hP, e, θ, hroot, _, hkernel, htrans⟩ := hcmp
  let Q := p.toSplitPinning.rootDatum
  let lam : Fin 3 → cocharacterLattice p.toSplitPinning.torus :=
    a2ParabolicCocharacters (Q.coroot a) (Q.coroot b)
  let ν : Fin 3 → cocharacterLattice S := fun k => θ.symm (lam k)
  have hθν (k : Fin 3) : θ (ν k) = lam k := θ.apply_symm_apply (lam k)
  have hsum : ν 0 + ν 1 + ν 2 = 0 := by
    simp only [ν, ← map_add]
    rw [a2ParabolicCocharacters_sum (Q.coroot a) (Q.coroot b), map_zero]
  have hroot' (α : characterLattice S) (hα : α ∈ relativeRoots s) :
      (∃! k, latticePairing S α (ν k) < 0) ∧ latticePairing S α (ν 0 - ν 1) ≠ 0 := by
    obtain ⟨i, hi⟩ := exists_root'_of_mem_relativeRoots hP Q e θ hroot hα
    simp only [hi, map_sub θ, hθν]
    exact a2ParabolicCocharacters_negative_and_regular Q a b hab hba hcase i
  have hcompat (n : ℕ) (x : K) : (τ ^ n) (algebraMap K E x) = algebraMap K E ((σ ^ n) x) := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih => simp only [pow_succ, AlgEquiv.mul_apply, hστ, ih]
  have hτ3 : (p.starAction τ) ^ 3 = 1 := by
    rw [← map_pow]
    apply (p.starAction_eq_one_iff _).mpr
    apply hkernel
    intro x
    rw [hcompat 3 x, hσ3]
    rfl
  have hτ2 : (p.starAction (τ ^ 2)) ^ 3 = 1 := by
    rw [map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hτ3, one_pow]
  obtain ⟨w₁, hw₁, hcw₁⟩ := exists_weyl_galoisAction_inv_a2ParabolicCocharacters
    p a b hab hba hcase τ hτ3 1
  obtain ⟨w₂, hw₂, hcw₂⟩ := exists_weyl_galoisAction_inv_a2ParabolicCocharacters
    p a b hab hba hcase (τ ^ 2) hτ2 2
  obtain ⟨m₁, hm₁⟩ := htrans σ τ hστ (ν 0) (ν 1) w₁ hw₁ (by rw [hθν, hθν]; exact hcw₁)
  obtain ⟨m₂, hm₂⟩ := htrans (σ ^ 2) (τ ^ 2) (hcompat 2) (ν 0) (ν 2) w₂ hw₂
    (by rw [hθν, hθν]; exact hcw₂)
  exact exists_conjugate_baseChange_of_regular_triple σ hgen hσ3 h01 h02 h12 hM hS s hs ν hsum
    (fun α hα => (hroot' α hα).1)
    (fun α hα => (hroot' α ((relativeRoots_eq_roots s).symm ▸ hα)).2) m₁ m₂ hm₁ hm₂

end CubicDescent

end Langlands.GroupScheme
