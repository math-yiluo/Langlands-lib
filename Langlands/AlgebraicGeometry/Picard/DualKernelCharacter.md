# The intrinsic character of an actual dual-kernel point

This internal construction composes the published Poincaré pullback
trivialization with the published intrinsic kernel character and its
independence laws. It supplies beta as a function on actual points of the
dual kernel. The output is the character produced by the canonical kernel
translation action; no character, pairing or comparison isomorphism is
supplied as input.

Let `f : A ⟶ B` be a homomorphism of abelian schemes over a scheme `S`,
retain `hA : HasDualScheme A`, `hB : HasDualScheme B`, and
`stability : PicardZeroPullbackStatement`, and let `p : T → B^∨` satisfy
`p ; f^∨ = T → S → 0_(A^∨)`. Here the dual parameter schemes, dual
map and Poincaré families are precisely the existing constructions.
`dualPointFamily B hB p` is their actual rigidified representative on
`T ×_S B`. The published `dualKernelPullbackModuleIso` proves and
chooses a trivialization of its pullback along the actual `f_T`.

`dualKernelPullbackClass` forgets rigidification and takes the class of
this line bundle in the existing `TrivialHomPullbackClasses f T`. This
quotient consists of isomorphism classes of actual line bundles whose
homomorphism pullback is trivial. Its input property is only existence
of an actual trivialization. `dualKernelCharacter` applies
`trivialHomPullbackClassCharacter` to this class. It supplies the proved
`universalGlobalFunctions A`, so no global-functions hypothesis remains
as an additional parameter.

`dualKernelCharacter_eq_intrinsic` identifies the output with
`intrinsicKernelCharacter f α (universalGlobalFunctions A)` for every
actual trivialization `α` of the representative pullback. The proof
applies the imported independence theorem to the chosen and arbitrary
trivializations. `dualKernelCharacter_eq_of_iso` permits any module
isomorphic to the representative and any trivialization of its pullback,
using imported module-isomorphism invariance.
`dualKernelCharacter_eq_of_family_class` permits any actual rigidified
family in the same rigidified Picard class, together with existence of
its pullback trivialization. Equality in the existing class quotient
gives an actual rigidified isomorphism; forgetting rigidification and
using bundle-isomorphism invariance proves the formula.

`dualKernelCharacterHom` is the corresponding actual homomorphism
`ker(f)_T → Gm_T` under `Cartier.characterHomEquiv`.
`dualKernelCharacterHom_eq_intrinsic` identifies this presentation with
the intrinsic homomorphism using any actual trivialization. For every
scheme `U` over `T` and point `k` of `ker(f)_T` on `U`,
`dualKernelCharacterHom_points` states

```text
Gm.pointsEquiv (k ; beta(p))
  = kernelTranslationUnit f α (universalGlobalFunctions A) a k₀,
```

where `a : U → T` is `kernelCharacterParameter U`, and `k₀` is the
actual kernel point over `S` obtained by `baseChangePointsEquiv`.
This is a formula on all test schemes, not only on geometric points.
It follows by rewriting to the published intrinsic-character evaluation
formula. Its orientation remains transported action divided by trivial
action, as in `KernelTranslationScalar`; no inversion is introduced.

For `dualKernelPointCharacter`, let `df` be the underlying group-scheme
map of `dualCommGroupSchemeMapFromEvaluation`. Retain the same seven
constructor propositions as that map: tensor-pullback preservation,
composition, unit coherence, associativity, left-unitor comparison,
symmetry and Picard-zero stability. Retain the two actual inverse line
bundles `MA,MB` and their tensor evaluation isomorphisms. For every test
scheme `T` and actual `x : T → ker(df)`, the published
`dualKernelPoint_eq_origin` proves the required origin equation for
`p = x ; kernelι df`. Applying `dualKernelCharacter` defines the
announced function

```text
ker(f^∨)(T) → (Cartier.characters (kernelCommGroupScheme f))(T).
```

`dualKernelPointCharacter_eq_intrinsic` computes it with any actual
trivialization. These are scheme-theoretic kernels of the existing
group-scheme maps, and the output is an actual relative character.

The construction is internally derived from the two imported modules
and makes no new external theorem assertion. Its motivating source is
Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary build
2012-02-08, Chapter VII, §§7.4–7.5, printed pp.99–100 / PDF pp.103–104.
That source constructs beta for an isogeny of abelian varieties over
a field by the same representative and intrinsic-character route.
Here only the map and its independence from trivializations and
isomorphic representatives are constructed, as conditional internal
consequences of the existing dual-family API over `S`.

No isogeny, finiteness, characteristic or base-separation assumption is
needed for this map. This unit does not prove compatibility with
replacement by test-scheme pullback or tensor products, hence does not
package beta as a natural additive map. It asserts no Cartier-duality
isomorphism, perfectness, finite Weil pairing or host-task completion.
Those remain subsequent obligations.
