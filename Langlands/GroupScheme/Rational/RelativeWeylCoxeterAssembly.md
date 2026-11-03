# Transporting a Coxeter system from the actual root pairing to `N(k)/Z(k)`

This module is a conditional supporting step toward
`RelativeWeylCoxeterStatement`. It works with the existing relative roots,
character and cocharacter lattices, normalizer points, relative Weyl quotient
`relativeWeylGroup i = N(k)/Z(k)`, rational root span, and the root pairing
`D.rootPairing` that `RootReflectionAssembly` builds from integral reflection
data `D`. Its main theorem,
`RelativeRootReflectionData.hasRelativeWeylCoxeterSystem_of_rootPairing`,
proves the published predicate `HasRelativeWeylCoxeterSystem i ν` from these
explicit inputs:

* the published relative-root-system predicate `HasRelativeRootSystem i`;
* a split torus `T` and a finite set of actual relative roots;
* a generic cocharacter `ν`;
* integral reflection data `D` whose chosen representative `n_α` of every
  root `α` centralizes the scheme-theoretic kernel of `α`
  (`RelativeRoot.kernelCentralizer i α`);
* a Coxeter matrix `Mx` and a Coxeter system `cs` on the Weyl group of
  `D.rootPairing`. The system is labelled by Mathlib's base
  `IsAddIndecomposable.baseOf` of the root map for the linear form
  `corootFunctional i ν`. Its simple reflections are the reflections
  `RootPairing.weylGroup.ofIdx` in the base roots. Its length is the number of
  positive, indivisible roots made negative. Its descent criterion is
  `ℓ(w) < ℓ(w s_b) ↔ 0 < corootFunctional i ν (w • root b)`.

The last group of hypotheses has the same form as the conclusion of
`Langlands.Group.RootPairingWeylCoxeterStatement` for this pairing and form.
That abstract statement is a separate artifact and is not imported here.
The module proves neither it nor `HasRelativeRootSystem`, and it does not
prove the existence of reflection data with the kernel-centralizer property.
So it does not prove `RelativeWeylCoxeterStatement`. It is the comparison step
that turns those inputs into that statement's conclusion for one `(i, ν)`.

The setting is an arbitrary universe `u`, a field `k : Type u`, a commutative
group scheme `T` over `Spec k`, a group scheme `G`, and a homomorphism
`i : T.toGrp ⟶ G`. All results except the first kernel-centralizer lemma
assume that `i` is a monomorphism. The reflection-data section also assumes
`G` is affine, as the published normalizer and Weyl-action constructions do.

## Kernel centralizers and dynamic centralizers

`RelativeRoot.kernelCentralizer_le_dynamicCentralizer`: if a character `a`
and a cocharacter `ζ` satisfy `⟨a, ζ⟩ = 0`, then every point centralizing the
kernel of `a` lies in the dynamic centralizer of `ζ ≫ i`. It is the case of
a field `k`, with `a` and `ζ` implicit, of
`RelativeRoot.kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero`
from the published module `Langlands.GroupScheme.Rational.CocharacterCentralizer`.
That lemma holds over any integral domain, and the proof here just applies it.
Its argument: the pairing condition becomes `ζ ≫ a = 0` through the
identification of endomorphisms of `𝔾_m` with `ℤ`, so the universal
`𝔾_m`-point pushed forward by `ζ` factors through the kernel of `a`. A
kernel-centralizing point commutes with this point, and that commutation is
exactly the defining condition of the dynamic centralizer.

`cocharacterAut_normalizingAut_eq_of_mem_dynamicCentralizer`: a rational
normalizing point `n` in the dynamic centralizer of `ζ ≫ i` fixes `ζ` under
its automorphism of `T`. Conjugation by `n` on the universal `ζ`-point equals
that point composed with the automorphism. Centralizing makes the conjugate
equal to the point itself. Cancelling the monomorphism `i` and comparing
points gives the equality of cocharacters.
`latticePairing_weylAction_of_mem_dynamicCentralizer` deduces
`⟨n · χ, ζ⟩ = ⟨χ, ζ⟩` for every character `χ`, from the published invariance
of the lattice pairing under a torus automorphism.

## Transport of Coxeter lengths

`coxeterLength_map_le`: a group homomorphism sending each simple generator of
one Coxeter system to a simple generator of another does not increase length.
It maps a reduced word to a word of the same length.
`coxeterLength_map_eq`: a group isomorphism matching simple generators along
a bijection of labels preserves length. Apply the first lemma in both
directions.

## The actual Weyl group and the pairing's Weyl group

`schemeWeylCharacterAction_mem_relativeRoots` and
`relativeWeylAction_rootVector` record that the actual Weyl action preserves
the relative roots and acts on root vectors `1 ⊗ β` through its action on
characters. For a split torus, `nsmul_rootVector_eq_iff` shows that
`n • (1 ⊗ β) = 1 ⊗ γ` holds exactly when `n • β = γ`, by injectivity of
rationalization. `HasRelativeRootSystem.relativeWeylAction_injective` extracts
the faithfulness clause of the root-system predicate.
`mem_positiveRelativeRoots_of_neg_not_mem` uses genericity and negation
stability: a root whose negative is not positive is itself positive.

Fix reflection data `D`.

* `eq_two_of_nsmul_eq`: if `n • γ = β` for roots `γ, β` and `n ≥ 2`, then
  `n = 2`. Pairing with the coroot of `β` gives `n · ⟨γ, β^∨⟩ = 2`, so `n`
  divides `2`.
* `representative_mem_standardLeviPoints`: if the representative `n_α`
  centralizes the kernel of `α` and `α ∈ J`, then `n_α` lies in the published
  standard Levi points of `J`. Every standard cocharacter `ζ` of `J` pairs to
  zero with `α`, so the first lemma above applies.
* `weylGroup_map_eq_range`: under `HasRelativeRootSystem i`, the image of the
  Weyl group of `D.rootPairing` under its faithful action on the root span is
  the full range of `relativeWeylAction i`. One inclusion is the published
  `D.weylGroup_image`. For the other, the predicate supplies some root
  pairing `P'` with the same root vectors whose Weyl group has image equal to
  that range. Each reflection of `P'` equals a reflection of `D.rootPairing`.
  The two coroots agree by Mathlib's `Module.Dual.eq_of_preReflection_mapsTo`,
  because the roots are a finite spanning set preserved by both reflections.
* `weylGroupEquiv` is the resulting group isomorphism
  `(D.rootPairing hT hfin).weylGroup ≃* relativeWeylGroup i`. It is the
  composite of the injective restriction of `RootPairing.Equiv.weightHom` and
  the inverse of the faithful action on the root span.
  `relativeWeylAction_weylGroupEquiv` states the defining compatibility.
  `weylGroupEquiv_ofIdx` shows that the reflection in root `α` goes to the
  class of the representative `n_α`, using the published
  `D.reflection_eq_relativeWeylAction`. `smul_root` and
  `corootFunctional_smul_root` compute `w · root β` and its value under
  `corootFunctional i ζ` through the actual character action.
* `mem_baseOf_iff`: a root index lies in `IsAddIndecomposable.baseOf` for the
  form `corootFunctional i ν` exactly when its character is an actual simple
  relative root in `simpleRelativeRoots i ν`. Values of the form on roots are
  the integer pairings with `ν`, and additive decompositions of root vectors
  correspond to decompositions of characters. `baseEquiv` is the resulting
  bijection with `SimpleRoot i ν`, the identity on underlying characters.
* `mem_reducedPositiveRelativeRoots_of_mem_simple`: a simple relative root is
  reduced. If it equaled `n • β` with `n ≥ 2`, then `n = 2` and it would be the
  sum `β + β` of two positive roots.

## The main theorem

`hasRelativeWeylCoxeterSystem_of_rootPairing` takes the hypotheses listed at
the top. Its Coxeter system on `relativeWeylGroup i` is
`(cs.reindex σ).map φ`, with `σ := baseEquiv` and `φ := weylGroupEquiv`. Its
simple reflection at `a` is the class of `n_a`. By `coxeterLength_map_eq` its
length agrees with `cs.length` along `φ`. The two finiteness conclusions are
the published `HasRelativeRootSystem.finite_relativeWeylGroup` and
`finite_simpleRelativeRoots`. The five clauses of
`IsRelativeWeylCoxeterRealization` are proved as follows.

1. Reflection formula. The class of `n_a` acts by
   `χ ↦ χ - ⟨χ, a^∨⟩ • a`, which is the reflection law of `D`. The integral form
   is `χ ↦ ⟨χ, a^∨⟩`, with value `2` at `a` by `D.pair_self`.
2. Positive roots other than `a` and `2a`. By the length formula (clause 4),
   the inversion set of the simple reflection has one element. It contains
   `a`, since `a` is reduced and goes to `-a`. So for every other reduced
   positive root, the negative of its image is not positive, and the image
   is positive by `mem_positiveRelativeRoots_of_neg_not_mem`. A non-reduced
   positive root `β` has the form `n • γ` with `n ≥ 2`. Then `n = 2` by
   `eq_two_of_nsmul_eq`, and `γ` is positive. It is reduced, since `γ = m • δ`
   with `m ≥ 2` would give `β = (2m) • δ`. It differs from `a`, because
   `β ≠ 2 • a`. The image of `γ` is positive, hence so is the image of `β`.
3. Descent criterion. This is `hdescent` transported along `φ`, with
   `corootFunctional_smul_root` and positivity of the integer pairing.
4. Length formula. The relative inversion set of `φ w` is the image under the
   injective map `Subtype.val` of the set counted in `hlength`. Positivity,
   indivisibility (via `nsmul_rootVector_eq_iff`) and the sign of the image
   correspond clause by clause. `Set.ncard_image_of_injective` finishes.
5. Parabolic subgroups. Let `I` be a finite set of simple roots. The Coxeter
   standard subgroup generated by the simple reflections in `I` is contained
   in `standardRelativeWeylGroup i ν (rootSet i ν I)`, since each `n_a` with
   `a ∈ I` lies in the standard Levi points
   (`representative_mem_standardLeviPoints`). For the reverse inclusion,
   choose a standard cocharacter `ζ` for the root set of `I`, which exists by
   the published `HasRelativeRootSystem.exists_standardCocharacter`. Every
   element of the standard relative Weyl group has a representative in the
   standard Levi, which lies in the dynamic centralizer of `ζ`. So the
   element preserves all pairings with `ζ`. The proof then shows, by strong
   induction on Coxeter length, that every element `v` preserving all
   pairings with `ζ` lies in the Coxeter standard subgroup of `I`. If `v ≠ 1`,
   take a right descent `s`. By clause 3, `v · s` is not positive, so its
   negative is a positive root. A standard cocharacter pairs non-negatively
   with positive roots, so `⟨s, ζ⟩ = ⟨v · s, ζ⟩ ≤ 0`. Since `ζ` is strictly
   positive on simple roots outside `I`, this forces `s ∈ I`. Then `v s_s`
   is shorter and still preserves pairings with `ζ`. By induction it lies in
   the standard subgroup, and hence so does `v`.

No Levi-generation theorem (Borel–Tits 5.17, `StandardRelativeWeylGeneration`)
is assumed. Clause 5 uses only the stabilizer argument above, so this step
does not depend on the reduction of generation to the Coxeter statement.

## Provenance

The provenance is internal. The two definitions, `weylGroupEquiv` and
`baseEquiv`, are comparison maps between published objects. The theorems are
consequences of the published lattice, normalizer, standard-parabolic,
standard-cocharacter and reflection-data constructions, and of Mathlib's
`RootPairing` and `CoxeterSystem` API. Orientation only: the classical
counterparts of the transported properties are the length formula and
descent criterion of Renard, *Représentations des groupes réductifs
p-adiques*, V.4.6, and Springer, *Linear Algebraic Groups* (1998), 8.3.2.
The parabolic argument in clause 5 is a standard stabilizer argument. It is
the implemented proof, not a quotation of any source.
