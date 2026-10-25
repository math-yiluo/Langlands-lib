import Langlands.Global.Arithmetic.KummerRadical
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexReduction
import Langlands.ClassField.Global.LocalPowerIndex
import Langlands.ClassField.Global.IdeleCohomology
import Langlands.ClassField.Global.IdeleArchimedean

/-! # Ideles that are norms from a Kummer extension of prime degree

Let `K` contain a primitive `p`-th root of unity for a prime `p`, and let `L = K(β)` be Galois of
degree `p` over `K` with `β ^ p = a ∈ K`. Let `S` be a finite set of finite places of `K` outside
which `p` is a unit and `a` has valuation one. An idele `y` of `K` is a norm from the ideles of `L`
if its coordinates have valuation one outside `S`, and at each place in `S` and each infinite place
either `a` is a local `p`-th power or the coordinate of `y` is a local `p`-th power.
-/

noncomputable section

namespace Langlands.Global.Arithmetic.KummerNormLift

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassField.Global
open Langlands.Global.Arithmetic.KummerRadical

section Conditions

variable {K : Type*} [Field K] [NumberField K]

/-- The Kummer norm condition at a finite place `v`: either `a` is a `p`-th power in `K_v`, or the
`v`-coordinate of the idele `y` is a `p`-th power in `K_vˣ`. -/
def FiniteRadicalCondition (p : ℕ) (a : K) (y : IdeleGroup (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) a) ∨
    ideleCoordinate v y ∈ localPowers v p

/-- The Kummer norm condition at an infinite place `w`: either `a` is a `p`-th power in `K_w`, or
the `w`-coordinate of the idele `y` is a `p`-th power in `K_wˣ`. -/
def InfiniteRadicalCondition (p : ℕ) (a : K) (y : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) :
    Prop :=
  (∃ c : w.Completion, c ^ p = algebraMap K w.Completion a) ∨
    ideleInfiniteCoordinate w y ∈ infiniteUnitPowers w p

end Conditions

section Local

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L] {p : ℕ} [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
  (hdeg : Module.finrank K L = p) {β : L} (hβ : Algebra.adjoin K {β} = ⊤) {a : K}
  (hβa : β ^ p = algebraMap K L a)

include hζ hdeg hβ hβa in
/-- **Local norms at a finite place of a Kummer extension.** At a finite place `v` satisfying the
Kummer norm condition, the `v`-coordinate of `y` is the local norm of a unit at every place
`q ∣ v`. -/
theorem exists_localNorm_eq_of_finiteRadicalCondition (y : IdeleGroup (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver v.asIdeal]
    (h : FiniteRadicalCondition p a y v) :
    ∃ c : (q.adicCompletion L)ˣ, FiniteExtension.localNorm v q (c : q.adicCompletion L) =
      (ideleCoordinate v y : v.adicCompletion K) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rcases h with ⟨c, hc⟩ | ⟨u, hu⟩
  · exact exists_localNorm_eq_of_finrank_eq_one v q
      (finrank_adicCompletion_eq_one hζ hβ hβa v q hc) _
  · obtain ⟨c, hc⟩ := exists_localNorm_eq_pow hdeg v q u
    refine ⟨c, ?_⟩
    rw [hc]
    exact congrArg Units.val hu

omit [NumberField L] [IsGalois K L] in
include hζ hβ hβa in
/-- **Local norms at an infinite place of a Kummer extension.** At an infinite place `w`
satisfying the Kummer norm condition, the `w`-coordinate of `y` is the local norm of a unit at
every place `u ∣ w`. -/
theorem exists_infinite_localNorm_eq_of_infiniteRadicalCondition (y : IdeleGroup (𝓞 K) K)
    (w : InfinitePlace K) (u : InfinitePlace L) [u.LiesOver w]
    (h : InfiniteRadicalCondition p a y w) :
    ∃ d : (u.Completion)ˣ, InfiniteExtension.localNorm w u (d : u.Completion) =
      (ideleInfiniteCoordinate w y : w.Completion) := by
  rcases h with ⟨c, hc⟩ | ⟨t, ht⟩
  · exact exists_infinite_localNorm_eq_of_isUnramified w u
      (isUnramified_of_pow_eq hζ w u hβ hβa hc) _
  · obtain ⟨d, hd⟩ := exists_infinite_localNorm_eq_pow hζ w u t
    refine ⟨d, ?_⟩
    rw [hd]
    exact congrArg Units.val ht

end Local

section Global

/-- **Ideles that are norms from a Kummer extension.** Let `K` contain a primitive `p`-th root of
unity `ζ` for a prime `p`, and let `L = K(β)` be Galois of degree `p` over `K` with
`β ^ p = a ∈ K`. Let `S` be a finite set of finite places of `K` outside which `p` is a unit and `a`
has valuation one. If an idele `y` of `K` has coordinates of valuation one outside `S`, and at each
place of `S` and each infinite place either `a` or the coordinate of `y` is a local `p`-th power,
then `y` is the norm of an idele of `L`. -/
theorem mem_range_ideleNorm_of_radical {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [IsGalois K L] {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hdeg : Module.finrank K L = p) {β : L}
    (hβ : Algebra.adjoin K {β} = ⊤) {a : K} (hβa : β ^ p = algebraMap K L a)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v ∉ S, IsUnit (p : v.adicCompletionIntegers K))
    (haS : ∀ v ∉ S, Valued.v (algebraMap K (v.adicCompletion K) a) = 1)
    (y : IdeleGroup (𝓞 K) K)
    (hyS : ∀ v ∉ S, Valued.v (ideleCoordinate v y : v.adicCompletion K) = 1)
    (hyfin : ∀ v ∈ S, (∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) a) ∨
      ideleCoordinate v y ∈ localPowers v p)
    (hyinf : ∀ w : InfinitePlace K, (∃ c : w.Completion, c ^ p = algebraMap K w.Completion a) ∨
      ideleInfiniteCoordinate w y ∈ infiniteUnitPowers w p) :
    y ∈ (ideleNorm (K := K) (L := L)).toMonoidHom.range := by
  classical
  let wf : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L v := fun v => placeAbove L v
  let wi : ∀ w : InfinitePlace K, InfinitePlacesAbove L w := fun w => infinitePlaceAbove L w
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ c : ((wf v).1.adicCompletion L)ˣ,
      (v ∉ S → Valued.v (c : (wf v).1.adicCompletion L) = 1) ∧
      FiniteExtension.localNorm v (wf v).1 (c : (wf v).1.adicCompletion L) =
        (y : AdeleRing (𝓞 K) K).2 v := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨c, hc⟩ := exists_localNorm_eq_of_finiteRadicalCondition hζ hdeg hβ hβa y v
        (wf v).1 (hyfin v hv)
      exact ⟨c, fun h => absurd hv h, hc⟩
    · obtain ⟨c, hc, hcn⟩ := exists_localNorm_eq_of_valued_eq_one hζ hdeg hβ hβa v (wf v).1
        (hpS v hv) (haS v hv) (ideleCoordinate v y) (hyS v hv)
      exact ⟨c, fun _ => hc, hcn⟩
  choose c hc hcn using hfin
  have hinf : ∀ w : InfinitePlace K, ∃ d : ((wi w).1.Completion)ˣ,
      InfiniteExtension.localNorm w (wi w).1 (d : (wi w).1.Completion) =
        (y : AdeleRing (𝓞 K) K).1 w := fun w =>
    exists_infinite_localNorm_eq_of_infiniteRadicalCondition hζ hβ hβa y w (wi w).1 (hyinf w)
  choose d hdn using hinf
  refine mem_range_ideleNorm_of_local wf wi y c ?_ hcn d hdn
  refine (S.finite_toSet.eventually_cofinite_notMem).mono fun v hv => ?_
  have h1 := hc v hv
  refine ⟨(mem_adicCompletionIntegers (𝓞 L) L (wf v).1).2 (le_of_eq h1), ?_⟩
  rw [mem_adicCompletionIntegers (𝓞 L) L (wf v).1, Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]

end Global

end Langlands.Global.Arithmetic.KummerNormLift
