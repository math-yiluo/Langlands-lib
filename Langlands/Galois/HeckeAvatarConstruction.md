# The conductor-level construction of adic avatars

This module builds the adic avatars of an algebraic Hecke character of a
totally complex number field `K` from a finite part with a given conductor
support. The three construction steps enter as hypotheses, in the form of the
Library statements `HeckeAvatarIdeleCorrectionStatement` (the idele
correction at one coefficient place), `FiniteGeometricArtinLifting` (unique
geometrically normalized lifts of finite idele-class characters) and
`HeckeAvatarInverseLimitStatement` (the congruence limit). Any coefficient
number field `L` with a complex embedding `ι`, lifts `emb σ` of the complex
embeddings of `K` and a finite part `φ` in the sense of `IsHeckeFinitePart` can
be used. The data need not come from `AlgebraicHeckeFinitePartStatement`. A
family of characters can therefore share one coefficient field, for example a
compositum of their fields of values.

## Exceptional sets

`residueCharacteristic_ne_zero` records that the residue characteristic of a
finite place is nonzero (it is the characteristic of a finite field, hence
prime). `finite_setOf_residueCharacteristic_eq` proves that the finite places of
`K` of a given nonzero residue characteristic `p` form a finite set, because
their prime ideals contain the nonzero integer `p`. The proof uses
`finite_natCast_mem_asIdeal`.

`avatarExceptionalSet S λ` is the union of a finite set `S` of places of `K`
with the places of `K` whose residue characteristic equals that of the finite
place `λ` of `L`. `notMem_avatarExceptionalSet_iff` says that `v` lies outside
it exactly when `v ∉ S` and the residue characteristics of `v` and `λ` differ.

## The integral avatar at one coefficient place

`IsIntegralHeckeAvatarAt t emb φ S λ η ψ` packages the data at one place `λ`.
Here `η` is a continuous character of the actual idele classes into the units
of the completed integer ring at `λ`, and `ψ` is a continuous character of the
absolute Galois group of `K` with the same values. The predicate has five
clauses:

1. on every idele `x`, the image of `η` in `L_λ^×` is the corrected value
   `correctedIdeleValue t emb φ λ x`;
2. at every finite place `v` of residue characteristic different from that of
   `λ`, `η` is the embedded finite part `φ` on one-place ideles;
3. for every level `n`, the reduction of `η` modulo `𝔪_λ^(n+1)` has a unique
   continuous Galois character satisfying `MatchesGeometricArtinOutside` with
   respect to `avatarExceptionalSet S λ`;
4. the reduction of `ψ` modulo `𝔪_λ^(n+1)` is such a character;
5. `ψ` itself satisfies `MatchesGeometricArtinOutside` for `η` and the same
   exceptional set. It kills the actual inertia at each place outside the set.
   It also sends every lift of geometric Frobenius to the value of `η` at any
   uniformizer.

`exists_isIntegralHeckeAvatarAt` constructs such `η` and `ψ`. Its premises are
a prescribed integral infinity type `t`, embeddings with `ι ∘ emb σ = σ`, a finite
part `φ`, and a finite set `S` outside which `χ` is unramified. The correction
statement supplies `η` with clauses 1 and 2. At a place `v` outside the
exceptional set, `χ` is trivial on the local integral units. Injectivity of `ι`
on units makes `φ` trivial there. Clause 2 and injectivity of the inclusion of
completed integer units then make `η` trivial there. The reductions of `η` are
characters into the finite discrete groups `CompletionUnitQuotient λ n`.
`FiniteGeometricArtinLifting` gives each of them a unique lift (clause 3), and
`HeckeAvatarInverseLimitStatement` gives the limit `ψ` with clauses 4 and 5.

`integralAvatarCharacter λ ψ` is the `λ`-adic character obtained by following
`ψ` with the inclusion of completed integer units into `L_λ^×`.
`IsIntegralHeckeAvatarAt.frobenius` reads off the comparison at a place `v ∉ S`
whose residue characteristic differs from that of `λ`. This character is trivial
on inertia at `v`. For every uniformizer `π` of `K_v`, it sends every lift of
geometric Frobenius to the image in `L_λ` of `φ` at the one-place idele of `π`.
The proof combines clause 5 at `π` with clause 2.

## The uniform family

`exists_isUniformHeckeAvatar_of_finitePart` takes in addition the exact
conductor support (`v ∉ S ↔ χ.IsUnramifiedAt v`) and a uniformizer `π v` at
every finite place. It gives a family `ψ` indexed by all finite places `λ` of
`L` with `IsUniformHeckeAvatar ι χ S a ψ`, where `a v` is `φ` at the one-place
idele of `π v`. The complex value of `χ` at `π v` is `ι (a v)` by
`IsHeckeFinitePart`, and the comparison at each `λ` is
`IsIntegralHeckeAvatarAt.frobenius`. The set `S` and the values `a v` do not
depend on `λ`.

`IsUniformHeckeAvatar.isCompatibleLambdaAdicRealization` forgets the exact
conductor support and keeps the common values. A uniform family is thus a
compatible realization in the sense of `IsCompatibleLambdaAdicRealization`, with
the same exceptional set.

## Source

The construction is the rank-one case of Serre, *Abelian l-Adic
Representations and Elliptic Curves*, 1989 reprint
(`serre-abelian-l-adic-1989`), Chapter II §§2.3–2.7. The corrected idelic map is
built in §2.3, pp. II-10–II-12. Proposition b) of §2.5, p. II-18, compares
Frobenius with the uniformizer at places outside the modulus and the
coefficient residue characteristic. The identification with Weil's type `A₀`
characters, via principal cancellation against the archimedean component, is
in §2.7, pp. II-23–II-24. Serre's Frobenius is arithmetic. The Library uses
geometric Frobenius, as normalized in `MatchesGeometricArtinOutside`. Serre
passes to the limit through the groups `S_m`. Here the limit is taken over the
congruence reductions of the integral character.
