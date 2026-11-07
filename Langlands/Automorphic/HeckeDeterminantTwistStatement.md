# Twists by arbitrary Hecke characters

Author: Worker 84. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1, unit U3b of the H3 assembly
(Henniart 2000, §3). Workers 116 (first executor), 44 and 64 raised no objection
to this unit, and no existing statement or task covers it.

The module has two relation definitions, eight proved theorems about them, and three
proposition definitions. Nothing is assumed.

The targets are
`Langlands.Automorphic.CuspidalDeterminantMultipleStatement` and
`Langlands.ClassField.Global.RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement`.
Their conjunction is
`Langlands.ClassField.Global.RelativeWeilGroup.HeckeDeterminantTwistStatement`
(universe parameters `u uV uP uQ`), the declaration of this submission. Each conjunct
is meant to get its own proof task.
Informally, for every Hecke character `χ` of a number field `F`, not necessarily of
finite order and not necessarily unitary:

- every irreducible cuspidal automorphic realization `Π` of `GL_{r+1}(𝔸_F)`, with a
  spectral presentation, has a twist `(χ ∘ det) ⊗ Π` with a matching twisted
  presentation;
- if a representation `S` of a relative Weil group is weakly associated with `Π`,
  then `(χ ∘ τ_F) ⊗ S` is weakly associated with `(χ ∘ det) ⊗ Π`, read through any
  presentation.

The Library already states the second assertion for characters of finite order
(`RelativeWeilGroup.PresentedTwistAssociationStatement`, in
`Langlands/Automorphic/AssociatedDeterminantTwistStatement.lean`). Henniart (2000),
§3.7, twists by an unramified unitary character, which in general has infinite
order.

## Declarations

Notation. `F : Type uF` is a number field. A Hecke character is the published
`HeckeCharacter F`, a continuous homomorphism `C_F → ℂˣ` from the idele class group.
`OperatorRealization F n` is the published type of subspaces of the stable automorphic
function space of `GL_n(𝔸_F)` that are invariant under all concrete operators: finite
adelic translations, standard compact translations and the enveloping algebra. For a
realization `S`, `S.toContinuous` is the published injective linear map sending a
vector to its continuous function on `GL_n(𝔸_F)`. `M_χ` is the published
`ContinuousRationalFunctions.determinantMultiplier n χ`, the map
`f ↦ (g ↦ χ(det g) f(g))` on continuous functions (published lemma
`evaluate_determinantMultiplier`).

### The realization relation

- `OperatorRealization.IsDeterminantMultiple χ S T`, for `S T : OperatorRealization F n`.
  It holds when some linear equivalence `e : S.Space ≃ₗ[ℂ] T.Space` satisfies
  `T.toContinuous (e f) = M_χ (S.toContinuous f)` for every `f`. Since `e` is
  bijective, this says that the functions in `T` are exactly the functions
  `g ↦ χ(det g) f(g)` with `f` in `S`. So `T` is the twist `(χ ∘ det) ⊗ S`, realized
  as an actual space of functions. Nothing is assumed about `χ`.

Proved theorems (namespace `Langlands.Automorphic.OperatorRealization`):

- `val_eq_of_toContinuous_eq`: if vectors `x` of `S` and `y` of `T` have the same
  continuous function, then they are the same stable function. This follows from the
  published injectivity of `automorphicToContinuous` and `stableAutomorphicInclusion`.
- `isDeterminantMultiple_determinantTwist S χ hχ`: for `χ` of finite order, the
  published twist `S.determinantTwist χ hχ` is a determinant multiple of `S`. The
  witness is the published `S.determinantTwistEquiv χ hχ`.
- `isDeterminantMultiple_refl S`: `IsDeterminantMultiple 1 S S`.
- `IsDeterminantMultiple.eq`: a source and a character have at most one target. If
  `IsDeterminantMultiple χ S T` and `IsDeterminantMultiple χ S U`, then `T = U`.
- `isDeterminantMultiple_one_iff`: `IsDeterminantMultiple 1 S T ↔ S = T`.
- `IsDeterminantMultiple.eq_determinantTwist`: for `χ` of finite order, the target is
  the published `S.determinantTwist χ hχ`.
- `IsDeterminantMultiple.isFiniteOrderDeterminantTwist`: for `χ` of finite order,
  `IsDeterminantMultiple χ S T` implies the published
  `IsFiniteOrderDeterminantTwist χ S T`. The converse is not proved here. The
  published relation asks only for an abstract linear equivalence satisfying three
  equations. It does not say that `T` is the multiplied space.

### The presentation relation

- `CuspidalSpectralPresentation.IsDeterminantMultiple χ P P'`, assuming
  `[CompactSpace (AdeleQuotient F)]`, for presentations
  `P : CuspidalSpectralPresentation.{uF, uV} S` and
  `P' : CuspidalSpectralPresentation.{uF, uW} T` of cuspidal realizations
  `S T : CuspidalOperatorRealization F r`. It is the conjunction of three clauses.
  1. `OperatorRealization.IsDeterminantMultiple χ S.realization T.realization`.
  2. For every finite place `v`, there is a published `Representation.Equiv` from
     `Langlands.twist (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
     (P.localComponent v).representation` to `(P'.localComponent v).representation`.
     Here `χ.finiteLocalDeterminant (r + 1) v` is the published restriction of
     `χ ∘ det` to `GL_{r+1}(F_v)`, and `Langlands.twist η ρ` is `g ↦ η(g) ρ(g)`. So
     each local component of `P'` is the corresponding local component of `P`
     twisted by `χ_v ∘ det`.
  3. `(SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).SameEulerPolynomials
     P'.spectralSystem`. Here `χ.finiteUniformizerValue v` is the published value
     `χ_v(ϖ_v)` at the uniformizer of the canonical completion data, and `scale`
     multiplies every Satake parameter at `v` by that value (published
     `scale_eulerPolynomial`: the Euler polynomial `p(X)` becomes `p(χ_v(ϖ_v) X)`).
     `SameEulerPolynomials` asks for equality at all but finitely many places.

Proved theorem: `CuspidalSpectralPresentation.isDeterminantMultiple_determinantTwist P χ hχ`.
For `χ` of finite order, the published twisted presentation `P.determinantTwist χ hχ` is
related to `P` in this sense. The local clause composes the published
`determinantTwistRepresentationEquiv` and `determinantTwistLocalComponentEquiv`; the
spectral clause is the published `sameEulerPolynomials_determinantTwist`.

### The targets

- `CuspidalDeterminantMultipleStatement` (universe parameters `u uP`). For every number
  field `F : Type u` with `[CompactSpace (AdeleQuotient F)]`, every `r`, every
  `S : CuspidalOperatorRealization F r`, every
  `P : CuspidalSpectralPresentation.{u, uP} S` and every `χ : HeckeCharacter F`, there
  exist `T : CuspidalOperatorRealization F r` and
  `P' : CuspidalSpectralPresentation.{u, uP} T` with `P.IsDeterminantMultiple χ P'`.
  By `IsDeterminantMultiple.eq`, the realization of `T` is then unique. The
  presentation `P'` is not.
- `RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement` (universe
  parameters `u uV uP uQ`). For every class family `c` with the published
  `IsArithmeticClassFamily c`, every Galois extension `E / F` of number fields in
  `Type u` with `[CompactSpace (AdeleQuotient F)]`, every `r`, every
  `S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)`, all
  `T T' : CuspidalOperatorRealization F r`, every presentation `P` of `T` (universe
  `uP`), every presentation `P'` of `T'` (universe `uQ`) and every
  `χ : HeckeCharacter F`: if
  `OperatorRealization.IsDeterminantMultiple χ T.realization T'.realization` and
  `IsWeaklyAssociated S P.spectralSystem`, then
  `IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
  P'.spectralSystem`.

The published `reciprocityCharacter c F E χ` is `w ↦ χ(transfer c F E w)⁻¹`, that is
`χ ∘ τ_F` with `τ_F` the pointwise inverse of the transfer `W_{E/F} → C_F`. The
published `IsWeaklyAssociated S s` says: `S` is continuous of rank equal to the rank
of `s`, and at all but finitely many finite places `v` the following holds at every
place `w` of `E` above `v`. Local maps `ι : W_{F_v} → W_{E/F}` with
`IsLocalRelativeWeilMap` exist, and for each of them `S ∘ ι` is unramified, with
Euler polynomial `det(1 - X S(ι Fr_v))` equal to that of `s` at `v`. Here `Fr_v` is
the published geometric Frobenius.

## Relation to the source

Henniart (2000), §2.2, p.444: if `S` and `Π` are associated and `χ` is a
quasicharacter of `𝔸_F^×/F^×`, then `(χ ∘ τ_F) ⊗ S` and `(χ ∘ det) ⊗ Π` are
associated. Henniart allows every quasicharacter, as the targets do here.

1. *Why a new relation.* The published `IsFiniteOrderDeterminantTwist χ S T` asks for
   finite order and a linear equivalence that twists the finite and compact actions by
   `χ ∘ det` and leaves the enveloping-algebra action unchanged. For `χ` of infinite
   order, for example `χ = ‖·‖^{it}` with `t ≠ 0`, the archimedean part `χ_∞ ∘ det`
   is not locally constant. The derivative of `χ_∞ ∘ det` along `X` is
   `dχ_∞(tr X)`, so multiplication changes the action of `X` to
   `X + dχ_∞(tr X)`, and the unchanged-action equation fails for multiplication.
   `IsDeterminantMultiple` instead describes the twist by its functions, which makes
   sense for every `χ`. This
   relation and its presentation version are new definitions of this module. They are
   modelled on the published finite-order twists, which they contain (the two
   `isDeterminantMultiple_determinantTwist` theorems).
2. *The existence statement.* The Library constructs twists only for `χ` of finite
   order. Henniart takes `(χ ∘ det) ⊗ Π` for granted. `CuspidalDeterminantMultipleStatement`
   is that existence, together with the local and spectral description of the twist
   that a presentation carries.
3. *Presentations.* As in the published finite-order statement, association is
   stated through the spectral system of a presentation. The association target
   concludes for every presentation `P'` of `T'`, not only for a twisted one. With
   `χ = 1`, the hypothesis says `T.realization = T'.realization`
   (`isDeterminantMultiple_one_iff`). The target then moves weak association
   between presentations of the same realization, with `S` replaced by its twist by
   the trivial character.
4. *Conventions.* The Weil-side twist is `reciprocityCharacter c F E χ`, the same
   convention as the published `PresentedDeterminantAssociationStatement`
   (`det S = ω ∘ τ_F`). With the published `LocalTransferReciprocityStatement`,
   `reciprocityCharacter c F E χ (ι g) = χ_v(rec_v g)` for a geometric local
   reciprocity `rec_v`. Under the geometric convention, uniformizers correspond to
   geometric Frobenius (Tate 1979, (1.4.1), p.6). So at a place where `χ_v` is
   unramified, the Weil-side twist multiplies `S(ι Fr_v)` by `χ_v(ϖ_v)`. This is
   the scaling `scale χ.finiteUniformizerValue` on the automorphic side.
5. *Arithmetic class family and compactness.* As in the published finite-order
   statement, the association target assumes `IsArithmeticClassFamily c`, which makes
   `W_{E/F}` Tate's relative Weil group. Both targets quantify over
   `[CompactSpace (AdeleQuotient F)]`, which the published
   `Langlands.Global.compactSpace_adeleQuotient` proves.

## Why the targets are true

This is a sketch of the expected proofs. Nothing here is proved in the module.

*Existence.* `|χ|` is trivial on the compact norm-one idele classes (Tate 1979,
§1.4.6, p.7), so `|χ(x)| = ‖x‖^σ` for a real `σ`. Multiplication `M_χ` sends automorphic
forms to automorphic forms: `χ ∘ det` is invariant under `GL_n(F)`; its finite part is
locally constant, because the finite idele group is locally profinite: `ℂˣ` has a
neighbourhood of `1` containing no nontrivial subgroup, so by continuity some compact
open subgroup of the finite ideles is mapped into it, hence into `1`, and its preimage
under the continuous `det` is open in `GL_n` of the finite adeles (total
disconnectedness alone would not suffice); its archimedean part is smooth; it
transforms by a character of the compact group; the enveloping algebra satisfies `X ∘ M_χ = M_χ ∘ (X + dχ_∞(tr X))`,
an algebra automorphism that preserves the centre, so `Z(g)`-finiteness is kept; and
`‖det g‖^σ` is bounded by a power of the height of `g` and `g⁻¹`, so moderate growth is
kept. All concrete operators are conjugated by `M_χ` to concrete operators, so the image
`T` of `S` is a realization, irreducible because `S` is. Constant terms commute with
`M_χ`, because `det(ng) = det g` for unipotent `n`, so `T` is cuspidal. For `P'`,
multiply the finite slice, twist each local factor by `χ_v ∘ det`, and enlarge the
exceptional sets by the finitely many places where `χ` ramifies, as in the published
finite-order construction `CuspidalSpectralPresentation.determinantTwist`. At an
unramified place, `χ_v(det)` takes the value `χ_v(ϖ_v)^i` on the standard diagonal
with `i` uniformizers (published `finiteLocalDeterminant_standardDiagonal`). The
spherical Hecke eigenvalues therefore scale as `scale` describes.

*Association.* Let `T'` be the determinant multiple of `T`, and `P'` any presentation
of `T'`.

- *Automorphic side.* Existence gives a presentation `P''` of the multiple of `T`, with
  the scaled spectral system of `P`. By `IsDeterminantMultiple.eq` that multiple is
  `T'`. `T'` is irreducible, so at almost every place `v` the local component of every
  presentation of `T'` is a sum of copies of one unramified representation. Its
  spherical spectrum, and so its Euler polynomial, does not depend on the presentation.
  Hence `P'` and `P''` have the same Euler polynomials at almost every place.
- *Weil side.* `χ ∘ τ_F` is continuous, and twisting keeps the rank. At almost every
  place `v`, `χ_v` is unramified. For each local map `ι`, by point 4 above,
  `(χ ∘ τ_F) ⊗ S` composed with `ι` is `S ∘ ι` twisted by the unramified character
  `χ_v ∘ rec_v`. It is unramified, and
  `det(1 - X χ_v(ϖ_v) S(ι Fr_v)) = p_v(χ_v(ϖ_v) X)`, where `p_v` is the Euler
  polynomial of `S ∘ ι`. By the association of `S` and `P`, `p_v` is the Euler
  polynomial of `P` at `v`, so the twist matches the scaled system of `P`, which is
  that of `P''` and `P'`.

## Intended use

The proof of the published `Langlands.Global.HenniartGlobalizationStatement` (U2)
follows Henniart (2000), §3.7, p.451. There the local component `S(X)_0` of the
global pair is the induced representation twisted by an unramified unitary character,
and Henniart concludes ("par suite") that the induced representation itself is
reached. This step twists the global pair, as in §2.2, by the inverse of a global
unitary Hecke character whose component at the place `0` is that unramified
character, for example `‖·‖^{it}` for a suitable real `t`. For `t ≠ 0` this character
has infinite order, so the finite-order statements do not apply; both targets here
do. The association target with `χ = 1` also moves association to a presentation with
prescribed local components.

## Sources

- Henniart (2000), *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139: §2.2, p.444 (association and twisting);
  §3.7, p.451 (the unramified twist of `S(X)_0`).
- Tate (1979), *Number theoretic background*, Corvallis Proc. Symp. Pure Math. 33,
  part 2: (1.4.1), p.6 (uniformizers correspond to geometric Frobenius); §1.4.6, p.7
  (the compact kernel of the norm).
