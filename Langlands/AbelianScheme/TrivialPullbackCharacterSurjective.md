# Surjectivity of the normalized character from effective descent

Author: Worker 934. This module shows that the published normalized character
`trivialHomPullbackClassCharacter f (universalGlobalFunctions A)` on
`TrivialHomPullbackClasses f T` is surjective. It assumes
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement`, and holds for
every base `S`, isogeny `f` and test scheme `T`.

## Character values

Fix `χ : Cartier.CharacterHom (kernelCommGroupScheme f) T`, a homomorphism
`ker(f)_T ⟶ Gm_T` of group schemes over `T.left`.

`characterValue f χ k` is defined for `W : Over T.left` and a kernel point
`k : (Over.map T.hom).obj W ⟶ ker f`. It is the global unit on `W.left`
attached by `Gm.pointsEquiv` to the composite of
`(baseChangePointsEquiv …).symm k` with `χ`. Two properties are proved:

- `characterValue_mul`: the value is multiplicative in `k`. Both point
  equivalences are multiplicative, and composition with a group homomorphism
  preserves products (`MonObj.mul_comp`).
- `characterValue_naturality`: the value is natural in `W`. This follows from
  `baseChangePointsEquiv_naturality` and `Gm.pointsEquiv_naturality`.

## A unit cocycle on equal-composite pairs

`pairCharacterValue f χ U a b h` is defined for every pair
`a b : U ⟶ T ×_S A` with `h : a ≫ f_T = b ≫ f_T`. It is
`characterValue f χ (pairKernelPoint f a b h)`, a unit on `U`.

The two cocycle conditions in the effective descent statement are proved as
follows. Both reduce to identities of kernel points, checked after composing
with the monomorphism `kernelι`:

- `pairCharacterValue_precomp`: precomposing a pair with `q : V ⟶ U` precomposes
  its kernel point with `pairParameterMap q a` (`pairKernelPoint_precomp`).
  Naturality of the character value then gives the pullback along `q`.
- `pairCharacterValue_trans`: for a triple `a, b, d`, `pairKernelPoint_trans`
  gives `k_ad = (e ≫ k_bd) * k_ab`. Here `e = pairParameterEq` is the identity
  of `U` relating the parameters of `a` and `b`. Multiplicativity, naturality
  along the identity and commutativity of units then give
  `c_ab * c_bd = c_ad`.

## Realization by the descended line bundle

`pairKernelPoint_kernelShear` considers the pair formed by the ordinary map
`(relativeSpace A.X.hom).map (kernelCharacterParameter W)` and the kernel
translation `kernelShear f (kernelCharacterParameter W) k`. Its kernel point is
`k`, pulled back along the projection `pairParameterProj W`.

`intrinsicKernelCharacterHom_eq_of_pairCharacterValue` takes a trivialization
`α` whose comparison scalars equal `pairCharacterValue f χ` on all pairs, and
concludes `intrinsicKernelCharacterHom f α h = χ`. The proof compares points
through `hom_ext_points` and `intrinsicKernelCharacterHom_points`. It unfolds
the descended unit `kernelTranslationUnit` to the comparison scalar at the
kernel translation, and replaces that scalar by the hypothesis. By
`pairKernelPoint_kernelShear` and naturality, the result is the projection
pullback `relativeUnitsPullback` of the character value at `k`. The published
`relativeUnitDescend_pullback` then returns that character value.

## The surjectivity theorem

`trivialHomPullbackClassCharacter_surjective_of_effective hE hf T` proves
surjectivity. For a character `χ`, apply `hE` to the affine, flat, surjective
`f_T` and the cocycle `pairCharacterValue f (characterHomEquiv χ)`. The result
is a line bundle `L` and a trivialization `α` with exactly these comparison
scalars. Its class has character `χ`, by `trivialHomPullbackCharacter_eq`,
injectivity of `characterHomEquiv`, and the previous lemma.
