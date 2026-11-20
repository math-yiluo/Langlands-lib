import Langlands.GroupScheme.Reductive.TitsTransferMatrix
import Langlands.GroupScheme.Reductive.TitsTransferBaseChange
import Langlands.Algebra.BrauerCorestriction.Hom
import Langlands.GroupScheme.Reductive.StarFixedDominantDecomposition

/-! # The transfer law for the Tits obstruction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix Langlands.Brauer
  Langlands.BrauerCorestriction Langlands.Algebra.CorestrictionTwistedFixed

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G)

/-- A weight whose transport to the base change `G_E` is star-fixed is fixed by the star action
of every `h ∈ Gal(K/E)`, viewed in `Gal(K/k)`. -/
theorem starAction_restrictScalars_smul_eq {E : Type u} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] {lam : characterLattice d.toSplitPinning.torus}
    (hfixE : (d.baseChange E).IsStarFixedWeight (d.weightTransport E lam)) (h : K ≃ₐ[E] K) :
    (d.starAction (h.restrictScalars k)).val • lam = lam := by
  have h1 := hfixE h
  rw [d.baseChange_starAction_weightTransport E h lam] at h1
  rw [smul_eq_weightEquiv]
  exact (d.weightTransport E).injective h1

/-- The star action preserves dominance. -/
theorem isDominantWeight_starAction_smul (σ : K ≃ₐ[k] K)
    {lam : characterLattice d.toSplitPinning.torus} (h : d.toSplitPinning.IsDominantWeight lam) :
    d.toSplitPinning.IsDominantWeight ((d.starAction σ).val • lam) := by
  rw [smul_eq_weightEquiv]
  exact (SplitPinning.isDominantWeight_weightMap_iff (d.starAction σ).val (d.starAction σ).2
    lam).mpr h

/-- Sums of conjugates of a dominant weight are dominant. -/
theorem isDominantWeight_sum_starAction_smul {ι : Type*} (s : Finset ι)
    (τ : ι → (K ≃ₐ[k] K)) {lam : characterLattice d.toSplitPinning.torus}
    (h : d.toSplitPinning.IsDominantWeight lam) :
    d.toSplitPinning.IsDominantWeight (∑ i ∈ s, (d.starAction (τ i)).val • lam) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact d.isDominantWeight_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact d.isDominantWeight_add (d.isDominantWeight_starAction_smul (τ i) h) ih

/-- The sum `∑_σ ε σ ⋆ lam` of the star conjugates of a weight over the `k`-embeddings
`σ : E → N`, indexed by `Fin (m + 1)` through `e`, where `ε σ ∈ Gal(K/k)` is a chosen
automorphism attached to `σ` (in the transfer law, one extending `σ`). -/
def embeddingConjSum {E N : Type u} [Field E] [Field N] [Algebra k E] [Algebra k N] {m : ℕ}
    (e : (E →ₐ[k] N) ≃ Fin (m + 1)) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
    (lam : characterLattice d.toSplitPinning.torus) : characterLattice d.toSplitPinning.torus :=
  ∑ i, (d.starAction (ε (e.symm i))).val • lam

theorem embeddingConjSum_eq {E N : Type u} [Field E] [Field N] [Algebra k E] [Algebra k N]
    {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin (m + 1)) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
    (lam : characterLattice d.toSplitPinning.torus) :
    d.embeddingConjSum e ε lam = ∑ i, (d.starAction (ε (e.symm i))).val • lam :=
  rfl

/-- **Star invariance of the conjugate sum.** For a weight fixed by the star action of
`Gal(K/E)`, the sum of its conjugates by extensions `ε σ` of the embeddings `σ : E → N` is fixed
by the star action of `Gal(K/k)`: `τ ε σ = ε (τ σ) h` with `h ∈ Gal(K/E)`, and `τ` permutes the
embeddings. -/
theorem isStarFixedWeight_sum_conj {E N : Type u} [Field E] [Field N] [Algebra k E] [Algebra k N]
    [Algebra E K] [Algebra N K] [IsScalarTower k E K] [IsScalarTower k N K] [Normal k N]
    {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin (m + 1)) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
    (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))
    {lam : characterLattice d.toSplitPinning.torus}
    (hfixE : (d.baseChange E).IsStarFixedWeight (d.weightTransport E lam)) :
    d.IsStarFixedWeight (∑ i, (d.starAction (ε (e.symm i))).val • lam) := by
  intro τ
  rw [← smul_eq_weightEquiv, Finset.smul_sum]
  have key : ∀ σ : E →ₐ[k] N, (d.starAction τ).val • (d.starAction (ε σ)).val • lam =
      (d.starAction (ε (galPerm (τ.restrictNormal N) σ))).val • lam := by
    intro σ
    rw [← mul_smul, ← Subgroup.coe_mul, ← map_mul, stabCorrection_restrictScalars ε hε τ σ,
      map_mul, Subgroup.coe_mul, mul_smul, d.starAction_restrictScalars_smul_eq hfixE]
  simp_rw [key]
  exact Fintype.sum_equiv ((e.symm.trans (galPerm (τ.restrictNormal N))).trans e) _ _
    (fun i => by simp)

variable [IsGalois k K] (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)

/-- **Transfer law for dominant weights.** Let `E/k` be finite separable and `N/k` finite
Galois with `[E : k]` embeddings `σ : E → N`, indexed by `Fin (m + 1)` through `e`, each extended
to `ε σ ∈ Gal(K/k)`. For a dominant weight `lam` fixed by the star action of `Gal(K/E)`, if the
sum of the conjugates `ε σ ⋆ lam` is star-fixed, its Tits obstruction is the corestriction of the
Tits obstruction of the base change `G_E` at the transported weight. -/
theorem titsObstructionValue_transfer_of_isDominantWeight
    {E N : Type u} [Field E] [Field N] [Algebra k E] [Algebra k N] [Algebra E K] [Algebra N K]
    [IsScalarTower k E K] [IsScalarTower k N K] [FiniteDimensional k E] [Algebra.IsSeparable k E]
    [FiniteDimensional k N] [IsGalois k N] [IsGalois E K]
    (hN : Nat.card (E →ₐ[k] N) = Module.finrank k E)
    (hspanE : (d.baseChange E).toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin (m + 1)) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
    (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))
    {lam : characterLattice d.toSplitPinning.torus} (hdom : d.toSplitPinning.IsDominantWeight lam)
    (hfixE : (d.baseChange E).IsStarFixedWeight (d.weightTransport E lam))
    (hfix : d.IsStarFixedWeight (∑ i, (d.starAction (ε (e.symm i))).val • lam)) :
    d.titsObstructionValue hspan (∑ i, (d.starAction (ε (e.symm i))).val • lam) hfix =
      corHom k E ((d.baseChange E).titsObstructionValue hspanE (d.weightTransport E lam) hfixE) := by
  obtain ⟨r, ρ, hρ⟩ := (splitHighestWeightClassification K _ d.toSplitPinning).1 lam hdom
  have := d.nonempty_of_isHighestWeight hρ
  choose Q hQ hQu using fun h : K ≃ₐ[E] K =>
    d.exists_intertwiner_galoisTwist_of_smul hρ (h.restrictScalars k)
      (d.starAction_restrictScalars_smul_eq hfixE h)
  obtain ⟨hQspan, hE⟩ := d.titsObstructionValue_baseChange_eq_classOf E hspanE hρ Q hQu hQ hfixE
  rw [hE, corHom_apply, classOf, cor_mk_eq_of_closure k E N hN,
    d.titsObstructionValue_eq_classOf_corCSAOf hspan e ε hε hρ.hasTopWeight Q hQu hQ hQspan hfix]
  rfl

/-- **Transfer law.** Let `E/k` be finite separable and `N/k` finite Galois with `[E : k]`
embeddings `σ : E → N`, indexed by `Fin (m + 1)` through `e`, each extended to `ε σ ∈ Gal(K/k)`.
For every weight `lam` fixed by the star action of `Gal(K/E)`, the Tits obstruction of the sum
of the conjugates `ε σ ⋆ lam` is the corestriction of the Tits obstruction of the base change
`G_E` at the transported weight. -/
theorem titsObstructionValue_transfer
    {E N : Type u} [Field E] [Field N] [Algebra k E] [Algebra k N] [Algebra E K] [Algebra N K]
    [IsScalarTower k E K] [IsScalarTower k N K] [FiniteDimensional k E] [Algebra.IsSeparable k E]
    [FiniteDimensional k N] [IsGalois k N] [IsGalois E K]
    (hN : Nat.card (E →ₐ[k] N) = Module.finrank k E)
    (hspanE : (d.baseChange E).toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin (m + 1)) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
    (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))
    {lam : characterLattice d.toSplitPinning.torus}
    (hfixE : (d.baseChange E).IsStarFixedWeight (d.weightTransport E lam)) :
    d.titsObstructionValue hspan (∑ i, (d.starAction (ε (e.symm i))).val • lam)
        (d.isStarFixedWeight_sum_conj e ε hε hfixE) =
      corHom k E ((d.baseChange E).titsObstructionValue hspanE (d.weightTransport E lam) hfixE) := by
  obtain ⟨a, b, ha, hb, hfa, hfb, hab⟩ := (d.baseChange E).exists_dominant_sub hspanE hfixE
  set a' := (d.weightTransport E).symm a with ha'def
  set b' := (d.weightTransport E).symm b with hb'def
  have hwa : d.weightTransport E a' = a := (d.weightTransport E).apply_symm_apply a
  have hwb : d.weightTransport E b' = b := (d.weightTransport E).apply_symm_apply b
  have hdom : ∀ c, (d.baseChange E).toSplitPinning.IsDominantWeight (d.weightTransport E c) →
      d.toSplitPinning.IsDominantWeight c := fun c hc =>
    (SplitPinning.isDominantWeight_weightMap_iff (d.baseChangeRootDatumEquiv E)
      (d.mem_baseChange_base_support_iff E) c).mp hc
  have ha' : d.toSplitPinning.IsDominantWeight a' := hdom a' (by rw [hwa]; exact ha)
  have hb' : d.toSplitPinning.IsDominantWeight b' := hdom b' (by rw [hwb]; exact hb)
  have hfa' : (d.baseChange E).IsStarFixedWeight (d.weightTransport E a') := by rw [hwa]; exact hfa
  have hfb' : (d.baseChange E).IsStarFixedWeight (d.weightTransport E b') := by rw [hwb]; exact hfb
  have hlam : lam = a' - b' := (d.weightTransport E).injective (by rw [map_sub, hwa, hwb, hab])
  have hsum : (∑ i, (d.starAction (ε (e.symm i))).val • lam) =
      (∑ i, (d.starAction (ε (e.symm i))).val • a') -
        ∑ i, (d.starAction (ε (e.symm i))).val • b' := by
    rw [hlam, ← Finset.sum_sub_distrib]
    simp only [smul_sub]
  have hfA := d.isStarFixedWeight_sum_conj e ε hε hfa'
  have hfB := d.isStarFixedWeight_sum_conj e ε hε hfb'
  have hdA := d.isDominantWeight_sum_starAction_smul Finset.univ (fun i => ε (e.symm i)) ha'
  have hdB := d.isDominantWeight_sum_starAction_smul Finset.univ (fun i => ε (e.symm i)) hb'
  rw [d.titsObstructionValue_eq_sub hspan _ hdA hdB hfA hfB hsum,
    ← d.titsObstructionValue_of_isDominantWeight hspan hfA hdA,
    ← d.titsObstructionValue_of_isDominantWeight hspan hfB hdB,
    d.titsObstructionValue_transfer_of_isDominantWeight hspan hN hspanE e ε hε ha' hfa' hfA,
    d.titsObstructionValue_transfer_of_isDominantWeight hspan hN hspanE e ε hε hb' hfb' hfB,
    ← map_sub]
  congr 1
  have hdA' : (d.baseChange E).toSplitPinning.IsDominantWeight (d.weightTransport E a') := by
    rw [hwa]; exact ha
  have hdB' : (d.baseChange E).toSplitPinning.IsDominantWeight (d.weightTransport E b') := by
    rw [hwb]; exact hb
  rw [(d.baseChange E).titsObstructionValue_eq_sub hspanE hfixE hdA' hdB' hfa' hfb'
      (by rw [hwa, hwb]; exact hab),
    (d.baseChange E).titsObstructionValue_of_isDominantWeight hspanE hfa' hdA',
    (d.baseChange E).titsObstructionValue_of_isDominantWeight hspanE hfb' hdB']

/-- The transfer law stated with `embeddingConjSum`. -/
theorem titsObstructionValue_embeddingConjSum
    {E N : Type u} [Field E] [Field N] [Algebra k E] [Algebra k N] [Algebra E K] [Algebra N K]
    [IsScalarTower k E K] [IsScalarTower k N K] [FiniteDimensional k E] [Algebra.IsSeparable k E]
    [FiniteDimensional k N] [IsGalois k N] [IsGalois E K]
    (hN : Nat.card (E →ₐ[k] N) = Module.finrank k E)
    (hspanE : (d.baseChange E).toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin (m + 1)) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
    (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))
    {lam : characterLattice d.toSplitPinning.torus}
    (hfixE : (d.baseChange E).IsStarFixedWeight (d.weightTransport E lam)) :
    d.titsObstructionValue hspan (d.embeddingConjSum e ε lam)
        (d.isStarFixedWeight_sum_conj e ε hε hfixE) =
      corHom k E ((d.baseChange E).titsObstructionValue hspanE (d.weightTransport E lam) hfixE) :=
  d.titsObstructionValue_transfer hspan hN hspanE e ε hε hfixE

end Langlands.GroupScheme.GaloisPinningData
