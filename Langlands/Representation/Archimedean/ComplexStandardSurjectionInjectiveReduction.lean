import Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-!
# Reduction of `ComplexStandardSurjectionInjectiveStatement`

`ComplexStandardSurjectionInjectiveStatement` (V2) says: if an irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module parameter of some list of complex characters,
every surjective intertwining map onto it from the `U(n)`-finite functions of a
Langlands-ordered standard module is injective. This file splits V2 into three statements:

* `ComplexLanglandsQuotientUniqueStatement` (Knapp 1994, Theorem 4 (a) and (c)): two
  Langlands-ordered lists of `n` characters whose standard modules both map nonzero into the
  same irreducible admissible module are permutations of each other;
* `ComplexStandardPermutationStatement` (Knapp 1986, Proposition 10.18, Theorem 10.6 and
  Corollary 10.42, applied to `SL_n(ℂ)` after restricting from `GL_n(ℂ)`): if the standard
  module of `ds` is irreducible, the standard module of every permutation of `ds` is
  isomorphic to it;
* `ComplexStandardNontrivialStatement`: the standard module of `n` characters has a nonzero
  `U(n)`-finite function.

`complexStandardSurjectionInjectiveReduction` proves that the three imply V2. On the way,
`isIrreducibleGKModule_of_injective` and `injective_of_isIrreducibleGKModule` transfer
irreducibility along intertwining maps out of standard modules.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

universe uV

/-! ## The three statements -/

/-- Uniqueness half of the Langlands classification for `GL_n(ℂ)` (Knapp 1994, Theorem 4 (a)
and (c), due to Želobenko and Naimark), in the form needed here: if two lists `ds`, `es` of `n`
complex characters in the Langlands order both have nonzero intertwining maps from the
`U(n)`-finite functions of their standard modules into the same irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module, then `ds` is a permutation of `es`. -/
def ComplexLanglandsQuotientUniqueStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds es : List ComplexCharacterData)
    (A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V)
    (B : kFiniteFunctions (complexStandardModule n es) (unitaryCompact ℂ n) →ₗ[ℂ] V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ds.length = n → es.length = n →
        IsComplexLanglandsOrdered ds → IsComplexLanglandsOrdered es →
          A ≠ 0 → IsComplexStandardIntertwining n ρ π ds A →
            B ≠ 0 → IsComplexStandardIntertwining n ρ π es B →
              ds.Perm es

/-- Permutation invariance of irreducible principal series of `GL_n(ℂ)` (Knapp 1986,
Proposition 10.18 with Theorem 10.6 and Corollary 10.42, stated there for semisimple groups
and applied to `SL_n(ℂ)`: principal series whose parameters differ by a Weyl group element
have the same global character, hence the same composition factors; the passage between
`GL_n(ℂ)` and `SL_n(ℂ)` is by restriction, the centre acting by the same scalars on both
sides, see the paired Markdown): if the `U(n)`-finite functions of the standard module of a list `ds` of `n` complex
characters form an irreducible `(𝔤𝔩_n(ℂ), U(n))`-module, then for every permutation `es` of
`ds` there is a bijective intertwining map from the `U(n)`-finite functions of the standard
module of `es` onto those of `ds`. -/
def ComplexStandardPermutationStatement : Prop :=
  ∀ (n : ℕ) (ds es : List ComplexCharacterData), ds.length = n → es.Perm ds →
    IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) →
      ∃ T : kFiniteFunctions (complexStandardModule n es) (unitaryCompact ℂ n) →ₗ[ℂ]
          kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
        Function.Bijective T ∧
          IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds)
            es T

/-- The principal series of `n` complex characters is nonzero: the `U(n)`-finite functions of
the standard module of a list of `n` complex characters form a nontrivial space. -/
def ComplexStandardNontrivialStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    Nontrivial (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))

/-- The three statements above imply `ComplexStandardSurjectionInjectiveStatement`. -/
def ComplexStandardSurjectionInjectiveReductionStatement : Prop :=
  ComplexLanglandsQuotientUniqueStatement.{uV} → ComplexStandardPermutationStatement →
    ComplexStandardNontrivialStatement → ComplexStandardSurjectionInjectiveStatement.{uV}

/-! ## Intertwining maps out of standard modules -/

section Intertwining

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ds : List ComplexCharacterData}
  {A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V}

/-- An intertwining map carries the right translation `complexStandardRep n ds k` to `ρ k`. -/
theorem IsComplexStandardIntertwining.map_rep (hA : IsComplexStandardIntertwining n ρ π ds A)
    (k : Matrix.unitaryGroup (Fin n) ℂ)
    (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :
    A (complexStandardRep n ds k f) = ρ k (A f) := by
  obtain ⟨hf, h⟩ := hA.1 ⟨Unitary.toUnits k, k.2⟩ f
  exact (congrArg A (Subtype.ext rfl)).trans h

/-- An intertwining map carries the Lie algebra action `complexStandardLie n ds Y` to
`π Y`, for every `Y ∈ ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)`. -/
theorem IsComplexStandardIntertwining.map_lie (hA : IsComplexStandardIntertwining n ρ π ds A)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :
    A (complexStandardLie n ds Y f) = π Y (A f) := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    obtain ⟨hf, h⟩ := hA.2 X f
    have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hD : complexStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) f = ⟨_, hf⟩ :=
      Subtype.ext (principalSeriesLie_one_tmul_apply_coe ℂ n _ X f)
    rw [hz, map_smul, LinearMap.smul_apply, map_smul, hD, h, map_smul, LinearMap.smul_apply]
  | add Y₁ Y₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, map_add, h₁, h₂, map_add, LinearMap.add_apply]

/-- Composition with an equivariant map preserves the intertwining property. -/
theorem IsComplexStandardIntertwining.comp {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ' : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W}
    {π' : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (hA : IsComplexStandardIntertwining n ρ π ds A) (B : V →ₗ[ℂ] W)
    (hBρ : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (v : V), B (ρ k v) = ρ' k (B v))
    (hBπ : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (v : V), B (π (1 ⊗ₜ X) v) = π' (1 ⊗ₜ X) (B v)) :
    IsComplexStandardIntertwining n ρ' π' ds (B ∘ₗ A) := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, h⟩ := hA.1 k f
    exact ⟨hf, by rw [LinearMap.comp_apply, h, hBρ, LinearMap.comp_apply]⟩
  · obtain ⟨hf, h⟩ := hA.2 X f
    exact ⟨hf, by rw [LinearMap.comp_apply, h, hBπ, LinearMap.comp_apply]⟩

/-- If `A` is an injective intertwining map from the nonzero `U(n)`-finite functions of the
standard module of `ds` into an irreducible module, then that standard module is irreducible:
the image of an invariant subspace is invariant. -/
theorem isIrreducibleGKModule_of_injective (hirr : IsIrreducibleGKModule ρ π)
    (hA : IsComplexStandardIntertwining n ρ π ds A) (hinj : Function.Injective A)
    (hnt : Nontrivial (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))) :
    IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) := by
  refine ⟨hnt, fun W hWk hWX => ?_⟩
  have hmap : W.map A = ⊥ ∨ W.map A = ⊤ := by
    apply hirr.2
    · rintro k _ ⟨f, hf, rfl⟩
      exact ⟨_, hWk k f hf, hA.map_rep k f⟩
    · rintro Y _ ⟨f, hf, rfl⟩
      exact ⟨_, hWX Y f hf, hA.map_lie Y f⟩
  rcases hmap with h | h
  · left
    rw [eq_bot_iff]
    intro f hf
    have : A f ∈ W.map A := ⟨f, hf, rfl⟩
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact hinj (by rw [this, map_zero])
  · right
    rw [eq_top_iff]
    intro f _
    have : A f ∈ W.map A := by rw [h]; exact Submodule.mem_top
    obtain ⟨g, hg, hgf⟩ := this
    rwa [← hinj hgf]

/-- A nonzero intertwining map out of an irreducible standard module is injective: its kernel
is an invariant subspace. -/
theorem injective_of_isIrreducibleGKModule
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds))
    (hA : IsComplexStandardIntertwining n ρ π ds A) (h0 : A ≠ 0) : Function.Injective A := by
  have hker : LinearMap.ker A = ⊥ ∨ LinearMap.ker A = ⊤ := by
    apply hirr.2
    · intro k f hf
      rw [LinearMap.mem_ker] at hf ⊢
      rw [hA.map_rep, hf, map_zero]
    · intro Y f hf
      rw [LinearMap.mem_ker] at hf ⊢
      rw [hA.map_lie, hf, map_zero]
  rcases hker with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) h0

end Intertwining

/-! ## The reduction -/

/-- The relation "the real part of the exponent does not increase", as a boolean relation for
sorting. -/
def complexLanglandsLE (d e : ComplexCharacterData) : Bool :=
  decide (e.exponent.re ≤ d.exponent.re)

/-- Sorting by `complexLanglandsLE` puts a list in the Langlands order. -/
theorem isComplexLanglandsOrdered_mergeSort (ds : List ComplexCharacterData) :
    IsComplexLanglandsOrdered (ds.mergeSort complexLanglandsLE) := by
  have h := List.pairwise_mergeSort (le := complexLanglandsLE)
    (fun a b c hab hbc => by
      simp only [complexLanglandsLE, decide_eq_true_eq] at hab hbc ⊢
      exact hbc.trans hab)
    (fun a b => by
      simp only [complexLanglandsLE, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _)
    ds
  exact h.imp fun hab => by simpa [complexLanglandsLE] using hab

/-- Proof of the reduction. Let `B` be the injective intertwining map from the standard module
of `ds'`. It is nonzero, hence bijective, so the standard module of `ds'` is irreducible. Let
`es` be `ds'` sorted into the Langlands order. By permutation invariance the standard module of
`es` is isomorphic to that of `ds'`, so it maps nonzero into `V`. `A` is nonzero because it is
onto the nonzero `V`. Uniqueness gives that `ds` is a permutation of `es`, hence of `ds'`.
Permutation invariance again makes the standard module of `ds` isomorphic to the irreducible
one of `ds'`, so it is irreducible, and the nonzero `A` is injective. -/
theorem complexStandardSurjectionInjectiveReduction :
    ComplexStandardSurjectionInjectiveReductionStatement.{uV} := by
  intro hU hP hN n V _ _ ρ π ds A hgk hirr hadm hds' hlen hord hsurj hA
  obtain ⟨ds', hlen', B, hBinj, hB⟩ := hds'
  have hB' : IsComplexStandardIntertwining n ρ π ds' B := hB
  -- The standard module of `ds'` is irreducible.
  have hirr' : IsIrreducibleGKModule (complexStandardRep n ds') (complexStandardLie n ds') :=
    isIrreducibleGKModule_of_injective hirr hB' hBinj (hN n ds' hlen')
  -- Sort `ds'` into the Langlands order.
  set es := ds'.mergeSort complexLanglandsLE with hes
  have hperm : es.Perm ds' := List.mergeSort_perm ds' complexLanglandsLE
  have hlenes : es.length = n := hperm.length_eq.trans hlen'
  obtain ⟨T, hTbij, hT⟩ := hP n ds' es hlen' hperm hirr'
  have hC : IsComplexStandardIntertwining n ρ π es (B ∘ₗ T) :=
    hT.comp B (fun k v => hB'.map_rep k v) (fun X v => hB'.map_lie (1 ⊗ₜ X) v)
  have hC0 : B ∘ₗ T ≠ 0 := by
    have := hN n es hlenes
    obtain ⟨f, hf⟩ := exists_ne (0 : kFiniteFunctions (complexStandardModule n es)
      (unitaryCompact ℂ n))
    intro h
    apply hf
    apply (hBinj.comp hTbij.1)
    simpa using LinearMap.congr_fun h f
  have hA0 : A ≠ 0 := by
    have := hirr.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h
    obtain ⟨f, rfl⟩ := hsurj v
    exact hv (by rw [h, LinearMap.zero_apply])
  -- Uniqueness: `ds` is a permutation of `es`, hence of `ds'`.
  have hdses : ds.Perm es := hU n V ρ π ds es A (B ∘ₗ T) hgk hirr hadm hlen hlenes hord
    (isComplexLanglandsOrdered_mergeSort ds') hA0 hA hC0 hC
  have hdsds' : ds.Perm ds' := hdses.trans hperm
  -- The standard module of `ds` is isomorphic to that of `ds'`, hence irreducible.
  obtain ⟨T₂, hT₂bij, hT₂⟩ := hP n ds' ds hlen' hdsds' hirr'
  have hirrds : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) :=
    isIrreducibleGKModule_of_injective hirr' hT₂ hT₂bij.1 (hN n ds hlen)
  exact injective_of_isIrreducibleGKModule hirrds hA hA0

end Langlands.Archimedean
