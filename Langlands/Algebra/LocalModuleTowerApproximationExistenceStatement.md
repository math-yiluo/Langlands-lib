# Existence of simultaneous local tower approximations

`Langlands.Algebra.LocalModuleTowerApproximationExistenceStatement` is a
Prop-valued definition of the supporting existence assertion extracted from the
construction in the proof of Stacks Project Lemma 10.128.8, tag
[00R7](https://stacks.math.columbia.edu/tag/00R7). This module states that
assertion; it supplies no proof of it. The published
`LocalAlgebraTowerSystem` and `LocalModuleTowerSystem` interfaces are imported
unchanged.

## Statement

Let `R : Type u`, `S : Type v`, and `T : Type w` be commutative local rings,
and let `M : Type z` be an additive commutative group with a `T`-module
structure. Give the rings algebra structures for `R → S → T` and `R → T`,
with `IsScalarTower R S T`, and assume the two adjacent algebra maps are
local. Suppose

- `EssFinitePresentation R S`;
- `EssFinitePresentation R T`;
- `Module.FinitePresentation T M`.

Then there exist one index type `ι`, a preorder on it, witnesses that it is
nonempty and directed, one `D : LocalAlgebraTowerSystem ι R S T`, and one
`E : LocalModuleTowerSystem D M`, such that the existing proposition
`E.IsApproximation` holds.

The ambient levels `u,v,w,z` are independent. Put `U = max u v w z`.
The existential index and all three component-ring carriers and component-module
carriers are explicitly chosen in `Type U`. The diagram and module witnesses
are chosen jointly. In particular, the statement does not quantify over a
previously fixed tower or require existence in an arbitrary smaller universe.
Only the upper ambient module action is an input. Composite locality follows
from the two local adjacent maps and the scalar tower, as in the imported API.

## Meaning of the conclusion

Write `Rᵢ = D.rs.base i`, `Sᵢ = D.rs.alg i`, `Tᵢ = D.top i`, and
`Mᵢ = E.stModule.obj i`. Unfolding the imported `E.IsApproximation` gives
the following concrete requirements:

- The specified ring cocones identify `R`, `S`, and `T` with the genuine
  ring direct limits. These are bijectivity conditions on the actual
  `Ring.DirectLimit.lift` comparison maps. The middle comparison occurs in
  both `D.rs.IsColimit` and `D.st.IsColimit` using the same rings and cocone.
- Every `Rᵢ` is essentially of finite type over `ℤ`, every `Sᵢ` over `Rᵢ`,
  and every `Tᵢ` over `Sᵢ`.
- For every `i ≤ j`, the canonical maps
  `Sᵢ ⊗[Rᵢ] Rⱼ → Sⱼ`, `Tᵢ ⊗[Sᵢ] Sⱼ → Tⱼ`, and
  `Tᵢ ⊗[Rᵢ] Rⱼ → Tⱼ` present their targets as localizations at prime
  ideals. Each `IsPrimeLocalization` uses the algebra induced by that
  projection's actual `ringBaseChangeMap`, which sends `x ⊗ a` to the
  transition image of `x` multiplied by the image of `a` in the target ring.
- The specified additive module cocone induces a bijection from the actual
  `AddCommGroup.DirectLimit` to `M`, through
  `E.stModule.moduleColimitMap`. The stored semilinearity retains compatibility
  with the varying ring actions.
- Every `Mᵢ` is finite over `Tᵢ`, and every canonical `Tⱼ`-linear map
  `Tⱼ ⊗[Tᵢ] Mᵢ → Mⱼ`, sending `t ⊗ m` to
  `t • E.stModule.map i j h m`, is bijective.

The last tensor is in scalar-first order, matching the published API; tensor
symmetry relates it to the module-first display in the source.
`D.st` uses the actual middle rings from `D.rs`, and `D.rt` uses the
composite component action on the same endpoints. Likewise, `E.rtModule`
uses the identical upper module objects, actions, transitions, cocone, additive
colimit map, and module base-change map as `E.stModule`. No identification
of separately chosen diagrams or arbitrary comparison isomorphism is an input.
The composite ring localization clause is explicitly retained in the imported
predicate, although the construction derives it from the adjacent clauses.

## Source, derivation, and witness size

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The main locator is `00R7.html`, Lemma 10.128.8: its proof from the initial
base-ring approximation through the three ring localization conditions and
the module transition isomorphisms, before the first flatness descent.
Supporting passages are `00QV.html`, Lemma 10.127.11
([00QV](https://stacks.math.columbia.edu/tag/00QV)), and `00QL.html`,
Lemma 10.127.13 ([00QX](https://stacks.math.columbia.edu/tag/00QX)).

This existence assertion is an internal extraction of that construction,
renaming the source's upper ring `S′` as `T`. A prospective proof chooses
finite presentations of the two algebras and the upper module, descends
their finite coefficient data along a base-ring approximation, and restricts
to a common directed tail. Essential finite presentation of `T` over `S`
is a consequence of the two hypotheses over `R`, via tower cancellation;
it is not an extra hypothesis of this statement. The upper module is
constructed from a presentation matrix over the upper stage ring.
The construction gives the three localization comparisons and module
base-change bijections together. Ordinary separate existence results do
not themselves identify their independently chosen middle rings.

For the universe bound, the base approximation may be indexed by finite
subsets of `R`, restricted to a tail after choosing the finite data.
Finite subsets, subtypes, and directed tails fit in `Type U`. Generated
subrings, polynomial rings in finitely many variables, their quotients,
and localizations can all be formed in this same universe: localization
uses pairs of ring elements followed by a quotient. A finite presentation
cokernel is a quotient of a finite power of the upper stage ring, also
in `Type U`. Universe lifting places smaller intermediate carriers and
the index in `Type U` without identifying any ambient levels.
Thus the maximum is a sufficient witness size. This is the mathematical
size rationale for the proposed proposition, not a Lean construction or
an additional formal hypothesis.

No project errata note for this source was found. The official pages and
comments were checked on 2026-10-27: 00R7 and 00QX have no comments;
00QV records a corrected polynomial-map typo and retains its
essential-finite-type condition. Three internal cautions in 00R7 remain
relevant to a future proof: the flattened upper polynomial quotient must
retain the lower relations, the lifted module matrix belongs over `Tᵢ`,
and the final plain tensor identities omit localizations. These are
internal observations, not published errata; those displays are not
encoded as equalities here.

## Scope

The assertion stops at simultaneous approximation. It assumes neither
nonzeroness nor flatness, Noetherian hypotheses, finite presentation of `R`,
flat transition maps, or injective transition maps. It supplies none of the
flatness conclusions of 00R7. Fibre diagrams, residue injectivity,
flatness descent, propagation, and flatness ascent remain separate results.
