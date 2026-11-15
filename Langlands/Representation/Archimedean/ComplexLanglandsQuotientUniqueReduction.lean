import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction

/-!
# Reduction of `ComplexLanglandsQuotientUniqueStatement`

`ComplexLanglandsQuotientUniqueStatement` (LU) says: two Langlands-ordered lists of `n` complex
characters whose standard modules both map nonzero into the same irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module are permutations of each other. This file reduces LU to

* the Library's `ComplexLanglandsSubrepresentationStatement` (Wallach 1979, Theorems 4.18 and
  6.7): every irreducible admissible module embeds into the standard module of a list of `n`
  characters whose exponents have non-decreasing real parts; and
* the new `ComplexStandardOppositeOrderHomStatement`: a nonzero intertwining map from the
  standard module of a Langlands-ordered list `ds` (real parts non-increasing) into the
  standard module of a list `cs` with non-decreasing real parts exists only if `ds` is a
  permutation of `cs`.

`complexLanglandsQuotientUniqueReduction` proves that the two imply LU.
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

/-! ## The new statement -/

/-- Intertwining maps between principal series in opposite orders (derived from the Langlands
classification of `GL_n(ℂ)` and the Bruhat `G`-order; see the paired Markdown for its
provenance): let `ds`
and `cs` be lists of `n` complex characters, `ds` in the Langlands order (real parts of the
exponents non-increasing) and `cs` in the opposite order (real parts non-decreasing). If some
nonzero linear map `T` from the `U(n)`-finite functions of the standard module of `ds` to those
of the standard module of `cs` intertwines the actions of `U(n)` and of `𝔤𝔩_n(ℂ)`, then `ds` is
a permutation of `cs`. -/
def ComplexStandardOppositeOrderHomStatement : Prop :=
  ∀ (n : ℕ) (ds cs : List ComplexCharacterData)
    (T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n cs) (unitaryCompact ℂ n)),
    ds.length = n → cs.length = n →
      IsComplexLanglandsOrdered ds → cs.Pairwise (fun d e => d.exponent.re ≤ e.exponent.re) →
        T ≠ 0 →
          IsComplexStandardIntertwining n (complexStandardRep n cs) (complexStandardLie n cs)
            ds T →
            ds.Perm cs

/-- `ComplexLanglandsSubrepresentationStatement` and `ComplexStandardOppositeOrderHomStatement`
imply `ComplexLanglandsQuotientUniqueStatement`. -/
def ComplexLanglandsQuotientUniqueReductionStatement : Prop :=
  ComplexLanglandsSubrepresentationStatement.{uV} → ComplexStandardOppositeOrderHomStatement →
    ComplexLanglandsQuotientUniqueStatement.{uV}

/-! ## Embeddings into standard modules -/

section Embedding

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {cs : List ComplexCharacterData}
  {E : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule n cs) (unitaryCompact ℂ n)}

/-- An embedding into a standard module carries `ρ k` to the right translation
`complexStandardRep n cs k`. -/
theorem IsComplexStandardEmbedding.map_rep (hE : IsComplexStandardEmbedding n ρ π cs E)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (v : V) :
    E (ρ k v) = complexStandardRep n cs k (E v) :=
  Subtype.ext ((hE.1 ⟨Unitary.toUnits k, k.2⟩ v).trans
    (principalSeriesRep_apply_coe ℂ n _ k (E v)).symm)

/-- An embedding into a standard module carries `π (1 ⊗ X)` to the right derivative
`complexStandardLie n cs (1 ⊗ X)`. -/
theorem IsComplexStandardEmbedding.map_lie_one_tmul (hE : IsComplexStandardEmbedding n ρ π cs E)
    (X : Matrix (Fin n) (Fin n) ℂ) (v : V) :
    E (π (1 ⊗ₜ X) v) = complexStandardLie n cs (1 ⊗ₜ X) (E v) :=
  Subtype.ext ((hE.2 X v).trans (principalSeriesLie_one_tmul_apply_coe ℂ n _ X (E v)).symm)

end Embedding

/-! ## The reduction -/

/-- Proof of the reduction. Embed `V` by `E` into the standard module of a list `cs` with
non-decreasing real parts. The nonzero intertwining map `A` into the irreducible `V` is onto,
so `E ∘ A` is a nonzero intertwining map from the standard module of `ds` into that of `cs`,
and `ds` is a permutation of `cs`. In the same way `es` is a permutation of `cs`. -/
theorem complexLanglandsQuotientUniqueReduction :
    ComplexLanglandsQuotientUniqueReductionStatement.{uV} := by
  intro hS hO n V _ _ ρ π ds es A B hgk hirr hadm hds hes hods hoes hA0 hA hB0 hB
  obtain ⟨cs, hcs, hocs, E, hE0, hE⟩ := hS n V ρ π hgk hirr hadm
  -- `E ∘ C` is a nonzero intertwining map into the standard module of `cs`, for `C = A, B`.
  have key : ∀ (ds' : List ComplexCharacterData)
      (C : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n) →ₗ[ℂ] V),
      ds'.length = n → IsComplexLanglandsOrdered ds' → C ≠ 0 →
        IsComplexStandardIntertwining n ρ π ds' C → ds'.Perm cs := by
    intro ds' C hlen hord hC0 hC
    have hCs := surjective_of_isComplexStandardIntertwining n hirr hC hC0
    have hEC : IsComplexStandardIntertwining n (complexStandardRep n cs)
        (complexStandardLie n cs) ds' (E ∘ₗ C) :=
      hC.comp E hE.map_rep hE.map_lie_one_tmul
    have hEC0 : E ∘ₗ C ≠ 0 := by
      intro h
      apply hE0
      ext v : 1
      obtain ⟨f, rfl⟩ := hCs v
      exact LinearMap.congr_fun h f
    exact hO n ds' cs (E ∘ₗ C) hlen hcs hord hocs hEC0 hEC
  exact (key ds A hds hods hA0 hA).trans (key es B hes hoes hB0 hB).symm

end Langlands.Archimedean
