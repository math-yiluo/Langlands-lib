import Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalization
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality

/-!
# The principal ideal theorem

This file belongs to the Library. It states the principal ideal theorem of the NYLL library (the
copy under `Nyll/`) in Mathlib's vocabulary, with NYLL's types hidden behind an existential: every
number field `K` has a finite extension `H`, unramified at every finite place of `K`, in which
every ideal of `𝓞 K` becomes principal.

The field `H` is NYLL's small Hilbert class field `smallHilbertClassField K` with its structure of
`K`-algebra `smallHilbertClassFieldAlgebraOverOriginal`. NYLL proves that it is unramified at every
finite place (`smallHilbertClassField_isUnramifiedAtFinitePlaces`, stated for the primes of the
ring of integers of the extension) and that every ideal of `𝓞 K` becomes principal in it
(`allIdealsBecomePrincipalInSmallHilbertClassField`, by Artin reciprocity and the vanishing of the
transfer to the commutator subgroup). Both statements are about the same `K`-algebra structure.

## Main declarations

* `exists_unramified_extension_forall_isPrincipal K`: a finite extension `H` of `K` such that
  `Algebra.IsUnramifiedIn (𝓞 H) v.asIdeal` for every finite place `v` of `K` and such that
  `I.map (algebraMap (𝓞 K) (𝓞 H))` is principal for every ideal `I` of `𝓞 K`.
-/

namespace Langlands.ClassFieldTheory.Global.Artin

open NumberField IsDedekindDomain

universe u

/-- **The principal ideal theorem.** Every number field `K` has a finite extension `H`, unramified
at every finite place of `K`, in which every ideal of `𝓞 K` becomes principal. The field `H` is
the Hilbert class field of `K` constructed by the NYLL library (`smallHilbertClassField K`). -/
theorem exists_unramified_extension_forall_isPrincipal (K : Type u) [Field K] [NumberField K] :
    ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : FiniteDimensional K H),
      (∀ v : HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 H) v.asIdeal) ∧
        ∀ I : Ideal (𝓞 K), (I.map (algebraMap (𝓞 K) (𝓞 H))).IsPrincipal := by
  refine ⟨GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K, inferInstance,
    inferInstance, inferInstance, inferInstance, fun v P hP hPv => ?_,
    GlobalClassFieldTheory.IdealClassFieldTheory.allIdealsBecomePrincipalInSmallHilbertClassField K⟩
  exact GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_isUnramifiedAtFinitePlaces K
    ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩

end Langlands.ClassFieldTheory.Global.Artin
