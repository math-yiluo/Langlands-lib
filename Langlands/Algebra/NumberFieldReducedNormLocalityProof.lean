import Langlands.Algebra.LocalReducedCharpolyNeighborhood
import Langlands.Algebra.LocalReducedNormRegular
import Langlands.Algebra.NumberFieldBrauerFiniteSupport
import Langlands.Algebra.NumberFieldReducedNormLocality
import Langlands.Algebra.ReducedCharpolyFromSplitFactors
import Langlands.ClassFieldTheory.Global.IdeleLocalInjectivity
import Langlands.Global.Arithmetic.NumberFieldPolynomialApproximation

/-! # Locality of the actual reduced norm over a number field -/

noncomputable section

open CategoryTheory NumberField Polynomial
open Langlands.Global.AdelicFunctoriality
open scoped TensorProduct NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.CentralSimple

universe u

variable {F : Type u} [Field F] [NumberField F] (A : CSA.{u, u} F)

private theorem exists_local_regular_norm (K : Type u) [NontriviallyNormedField K]
    [CompleteSpace K] [Algebra F K] (a : Fˣ)
    (ha : Units.map (algebraMap F K).toMonoidHom a ∈ Set.range (reducedNormUnits F A K)) :
    ∃ z : Brauer.baseChange K A,
      reducedNorm K (Brauer.baseChange K A) K (1 ⊗ₜ[K] z) = algebraMap F K (a : F) ∧
      (reducedCharpoly K (Brauer.baseChange K A) z).Separable := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  obtain ⟨x, hx⟩ := ha
  let b : Brauer.baseChange K A := x.val
  have hb : reducedNorm K (Brauer.baseChange K A) K (1 ⊗ₜ[K] b) = algebraMap F K (a : F) :=
    (reducedNorm_baseChange A K x.val).trans (congrArg Units.val hx)
  have hb0 : reducedNorm K (Brauer.baseChange K A) K (1 ⊗ₜ[K] b) ≠ 0 := by
    rw [hb]
    simpa only [map_zero] using (algebraMap F K).injective.ne a.ne_zero
  obtain ⟨z, hz, hs⟩ := exists_norm_eq_with_separable_reducedCharpoly b hb0
  exact ⟨z, hz.trans hb, hs⟩

private def splitsOverRoot {K : Type u} [Field K] (B : CSA.{u, u} K) (p : K[X]) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra K E] [Algebra.IsAlgebraic K E] (r : E),
    aeval r p = 0 → Brauer.IsSplit (Brauer.baseChange E B)

private theorem isSplit_adjoinRoot_of_local (S : Finset (Langlands.Global.FinitePlace F))
    (hS : ∀ v : Langlands.Global.FinitePlace F, v ∉ S →
      Brauer.IsSplit (Brauer.baseChange (v.adicCompletion F) A))
    (g p : F[X]) [hp : Fact (Irreducible p)] (hpg : p ∣ g)
    (hfin : ∀ v : S, splitsOverRoot (Brauer.baseChange (v.val.adicCompletion F) A)
      (g.map (algebraMap F (v.val.adicCompletion F))))
    (hinf : ∀ v : InfinitePlace F, splitsOverRoot (Brauer.baseChange v.Completion A)
      (g.map (algebraMap F v.Completion))) :
    Brauer.IsSplit (Brauer.baseChange (AdjoinRoot p) A) := by
  let L := AdjoinRoot p
  let : FiniteDimensional F L := (AdjoinRoot.powerBasis hp.out.ne_zero).finite
  let : NumberField L := NumberField.of_module_finite F L
  have hr : aeval (AdjoinRoot.root p) g = 0 := by
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.mpr hpg
  have hroot (K M : Type u) [Field K] [Field M] [Algebra F K] [Algebra F M]
      [Algebra K M] [Algebra L M] [IsScalarTower F K M] [IsScalarTower F L M] :
      aeval (algebraMap L M (AdjoinRoot.root p)) (g.map (algebraMap F K)) = 0 := by
    rw [aeval_map_algebraMap]
    change aeval (IsScalarTower.toAlgHom F L M (AdjoinRoot.root p)) g = 0
    rw [aeval_algHom_apply, hr, map_zero]
  have htransfer (K M : Type u) [Field K] [Field M] [Algebra F K] [Algebra F M]
      [Algebra K M] [Algebra L M] [IsScalarTower F K M] [IsScalarTower F L M]
      (h : Brauer.IsSplit (Brauer.baseChange M (Brauer.baseChange K A))) :
      Brauer.IsSplit (Brauer.baseChange M (Brauer.baseChange L A)) := by
    obtain ⟨n, hn, ⟨e⟩⟩ := h
    exact ⟨n, hn, ⟨(Brauer.baseChangeTowerEquiv L M A).trans
      ((Brauer.baseChangeTowerEquiv K M A).symm.trans e)⟩⟩
  apply Brauer.numberFieldBrauerSplitting L (Brauer.baseChange L A)
  · intro w
    let v := Langlands.ClassFieldTheory.Global.placeBelow F w
    let : w.asIdeal.LiesOver v.asIdeal := Langlands.ClassFieldTheory.Global.liesOver_placeBelow F w
    let K := v.adicCompletion F
    let M := w.adicCompletion L
    let : Module.Finite K M := FiniteExtension.local_finite v w
    apply htransfer K M
    by_cases hv : v ∈ S
    · exact hfin ⟨v, hv⟩ M (algebraMap L M (AdjoinRoot.root p)) (hroot K M)
    · exact (hS v hv).baseChange M
  · intro w
    let v := w.comap (algebraMap F L)
    let : w.LiesOver v := ⟨rfl⟩
    let K := v.Completion
    let M := w.Completion
    let : Module.Finite K M := InfiniteExtension.local_finite v w
    let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply F K M]
      exact NumberField.LiesOver.completionMap_coe (v := v) (w := w) (WithAbs.toAbs v.1 x)
    apply htransfer K M
    exact hinf v M (algebraMap L M (AdjoinRoot.root p)) (hroot K M)

/-- Local reduced norms of a field unit give a global reduced norm of a unit. -/
theorem numberFieldReducedNormLocality : NumberFieldReducedNormLocalityStatement.{u} := by
  intro F D _ _ _ _ _ _ _ a ha
  classical
  let A : CSA.{u, u} F := { toAlgCat := AlgCat.of F D }
  let d := reducedDegree F A
  let c : F := (-1 : F) ^ d * (a : F)
  let S := (Brauer.finite_nonsplitFinitePlaces A).toFinset
  have hS (v : Langlands.Global.FinitePlace F) (hv : v ∉ S) :
      Brauer.IsSplit (Brauer.baseChange (v.adicCompletion F) A) := by
    by_contra h
    apply hv
    change v ∈ (Brauer.finite_nonsplitFinitePlaces A).toFinset
    simpa only [Set.Finite.mem_toFinset, Brauer.nonsplitFinitePlaces, Set.mem_ofPred_eq] using h
  have hfin (v : S) :
      ∃ z : Brauer.baseChange (v.val.adicCompletion F) A,
        reducedNorm (v.val.adicCompletion F) (Brauer.baseChange (v.val.adicCompletion F) A)
          (v.val.adicCompletion F) (1 ⊗ₜ[v.val.adicCompletion F] z) =
            algebraMap F (v.val.adicCompletion F) (a : F) ∧
        (reducedCharpoly (v.val.adicCompletion F) (Brauer.baseChange (v.val.adicCompletion F) A) z).Separable := by
    let K := v.val.adicCompletion F
    let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (WithZero (Multiplicative ℤ))
    exact exists_local_regular_norm A K a (ha (.inr v.val))
  have hinf (w : InfinitePlace F) :
      ∃ z : Brauer.baseChange w.Completion A,
        reducedNorm w.Completion (Brauer.baseChange w.Completion A) w.Completion
          (1 ⊗ₜ[w.Completion] z) = algebraMap F w.Completion (a : F) ∧
        (reducedCharpoly w.Completion (Brauer.baseChange w.Completion A) z).Separable := by
    let : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := by
          refine ⟨2, ?_⟩
          have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero (InfinitePlace.Completion.extensionEmbedding w)) (2 : w.Completion)
          rw [← h]
          norm_num only [map_ofNat, Complex.norm_ofNat] }
    exact exists_local_regular_norm A w.Completion a (ha (.inl w))
  choose x hnx hsx using hfin
  choose y hny hsy using hinf
  let p (v : S) := reducedCharpoly (v.val.adicCompletion F)
    (Brauer.baseChange (v.val.adicCompletion F) A) (x v)
  let q (w : InfinitePlace F) := reducedCharpoly w.Completion (Brauer.baseChange w.Completion A) (y w)
  have hdata (K : Type u) [Field K] [Algebra F K] (z : Brauer.baseChange K A)
      (hz : reducedNorm K (Brauer.baseChange K A) K (1 ⊗ₜ[K] z) = algebraMap F K (a : F)) :
      (reducedCharpoly K (Brauer.baseChange K A) z).Monic ∧
        (reducedCharpoly K (Brauer.baseChange K A) z).natDegree = d ∧
        (reducedCharpoly K (Brauer.baseChange K A) z).coeff 0 = algebraMap F K c := by
    have hdK : reducedDegree K (Brauer.baseChange K A) = d := reducedDegree_baseChange F A K
    refine ⟨reducedCharpoly_monic K _ z, (reducedCharpoly_natDegree K _ z).trans hdK, ?_⟩
    rw [reducedCharpoly_coeff_zero, hz, hdK]
    simp [c]
  have hp (v : S) := hdata (v.val.adicCompletion F) (x v) (hnx v)
  have hq (w : InfinitePlace F) := hdata w.Completion (y w) (hny w)
  have hpn (v : S) : ReducedCharpolySplitNeighborhood
      (K := v.val.adicCompletion F) (Brauer.baseChange (v.val.adicCompletion F) A) (p v) :=
    reducedCharpolySplitNeighborhood_finite v.val _ (x v) (hsx v)
  have hqn (w : InfinitePlace F) :
      ReducedCharpolySplitNeighborhood (Brauer.baseChange w.Completion A) (q w) :=
    reducedCharpolySplitNeighborhood_infinite w _ (y w) (hsy w)
  choose ε hε hεg using hpn
  choose η hη hηg using hqn
  obtain ⟨g, hgm, hgd, hgc, hgf, hgi⟩ := Langlands.Global.exists_monic_polynomial_approximation d
    (reducedDegree_pos F A) c S p q hp hq ε η hε hη
  have hnearFin (v : S) := hεg v (g.map (algebraMap F (v.val.adicCompletion F)))
    (hgm.map _) ((hgm.natDegree_map _).trans (hgd.trans (hp v).2.1.symm)) (hgf v)
  have hnearInf (w : InfinitePlace F) := hηg w (g.map (algebraMap F w.Completion))
    (hgm.map _) ((hgm.natDegree_map _).trans (hgd.trans (hq w).2.1.symm)) (hgi w)
  let w₀ : InfinitePlace F := Classical.choice inferInstance
  have hgs : g.Separable := (Polynomial.separable_map (algebraMap F w₀.Completion)).mp (hnearInf w₀).1
  obtain ⟨z, hz⟩ := exists_reducedCharpoly_eq_of_split_factors A g hgm hgs hgd
    (fun r _ hr hrg => by
      let : Fact (Irreducible r) := ⟨hr⟩
      exact isSplit_adjoinRoot_of_local A S hS g r hrg
        (fun v => (hnearFin v).2) (fun w => (hnearInf w).2))
  have hcoeff := congrArg (fun f : F[X] => f.coeff 0) hz
  change (reducedCharpoly F A z).coeff 0 = g.coeff 0 at hcoeff
  rw [reducedCharpoly_coeff_zero, hgc] at hcoeff
  have hnorm : reducedNorm F A F (1 ⊗ₜ[F] z) = (a : F) :=
    mul_left_cancel₀ (pow_ne_zero d (neg_ne_zero.mpr one_ne_zero)) hcoeff
  have hu := (isUnit_iff_reducedNorm_ne_zero A F (1 ⊗ₜ[F] z)).mpr (hnorm ▸ a.ne_zero)
  exact ⟨hu.unit, Units.ext hnorm⟩

end Langlands.CentralSimple
