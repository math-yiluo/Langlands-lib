# Uniqueness for weak association

Worker 35 authored this statement unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. All declarations lie in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`.

The module states the two uniqueness assertions of Henniart 2000, §2.2, for
representations `S` of the relative Weil group
`W_{E/F} = RelativeWeilGroup c F E` and actual cuspidal classes of
`GL_{r+1}` over the number field `F`. They are three `Prop`-valued
definitions, with their conjunction `AssociatedUniquenessStatement`:

- the Chebotarev-type rigidity of semisimple representations of `W_{E/F}`
  with the same unramified Euler polynomials;
- the uniqueness of the semisimple representation weakly associated with a
  cuspidal class;
- the uniqueness of the cuspidal class weakly associated with a
  representation.

The module also defines weak equivalence of two representations and proves
four elementary lemmas about it and about weak association. The three
statements are not proved. No representation, cuspidal class or local map
is constructed, and no existence statement is made.

## Objects

- **Fields, class family and Weil group.** Number fields `F E : Type u` with
  `[Algebra F E]` and `[IsGalois F E]`, a class family
  `c : FundamentalClass.ClassFamily.{u}`, and the published relative Weil
  group `RelativeWeilGroup c F E`.
- **Weil-side representations.** `S : FiniteRepresentation.{0, u, uV} ℂ
  (RelativeWeilGroup c F E)` and `S' : FiniteRepresentation.{0, u, uW} ℂ
  (RelativeWeilGroup c F E)` are finite-dimensional complex representations.
  Their carriers lie in the independent universes `uV` and `uW`.
- **Equivalence.** `FiniteRepresentation.Equiv S S'` is the published type of
  invertible linear intertwiners `S → S'`. It permits different carrier
  universes. "Up to isomorphism" is `Nonempty (FiniteRepresentation.Equiv S
  S')`.
- **Semisimplicity and continuity.** `S.IsSemisimple` is the published
  `FiniteRepresentation.IsSemisimple`, Mathlib's
  `Representation.IsSemisimpleRepresentation`: every subrepresentation has a
  complement. `S.IsContinuous` is the published
  `FiniteRepresentation.IsContinuous`: the action is continuous into the
  endomorphisms of the carrier with the finite-dimensional module topology.
- **Cuspidal classes.** Under the explicit assumption
  `[CompactSpace (AdeleQuotient F)]`, which the published automorphic-form
  constructions require,
  `π : Automorphic.CuspidalOperatorRealization.IsoClass F r` is a class of
  actual irreducible cuspidal realizations of `GL_{r+1}` over `F`, up to the
  published equivalence of realizations. The compactness is the conclusion
  of the published `AdeleQuotientCompactStatement` (Cassels §14), which this
  module neither proves nor uses as a theorem.
- **Unramified matching.** The published
  `IsUnramifiedMatchAt S v P`, from
  `Langlands.Automorphic.Unramified.RelativeWeilAssociation`, says the
  following for a finite place `v` of `F` and `P : Polynomial ℂ`. For every
  place `w` of `E` above `v`, some reciprocity candidate `e` of `E_w` and
  some continuous homomorphism `ι : W_{F_v} →ₜ* W_{E/F}` satisfy
  `IsLocalRelativeWeilMap v w.1 e ι`. Every such `(e, ι)` makes `S ∘ ι`
  trivial on the inertia subgroup and gives
  `det(1 - X S(ι Fr)) = P`, where `Fr` is the published geometric Frobenius
  lift of `W_{F_v}`.
- **Weak association.** The published `IsWeaklyAssociated S s`, for a
  spectral system `s : SpectralSystem (FinitePlace F) n`, says that `S` is
  continuous of rank `n` and that, at cofinitely many finite places `v`, the
  spectrum of `s` is defined and `IsUnramifiedMatchAt S v` holds for its
  Euler polynomial `∏ (1 - z X)`. The published
  `IsWeaklyAssociatedClass.{u, uV, uP} S π` says that some spectral system
  attached to `π` by a cuspidal spectral presentation in universe `uP` is
  weakly associated with `S`.

## Declarations

### Weak equivalence

In the section `WeakEquivalence`, `F`, `E` and `c` are fixed, with no
assumption on `c`.

- `IsWeaklyEquivalent S S'` holds when, at cofinitely many finite places `v`
  of `F`, some polynomial `P` satisfies both `IsUnramifiedMatchAt S v P` and
  `IsUnramifiedMatchAt S' v P`. Thus `S` and `S'` are unramified at `v` along
  every local map, and `det(1 - X S(ι Fr)) = det(1 - X S'(ι Fr))` for every
  local map `ι` at every place of `E` above `v`. These are the local Euler
  factors `L(S_v, s) = det(1 - q_v^{-s} S(ι Fr))^{-1}`.
- `IsWeaklyEquivalent.symm` (proved): the relation is symmetric.
- `IsWeaklyEquivalent.of_isWeaklyAssociated` (proved): two representations
  weakly associated with one spectral system `s` are weakly equivalent. The
  common polynomial at `v` is the Euler polynomial of `s` at `v`.
- `IsUnramifiedMatchAt.eq` (proved): if `IsUnramifiedMatchAt S v P` and
  `IsUnramifiedMatchAt S v Q`, then `P = Q`. Some place `w` of `E` lies
  above `v`, by the published instance `finitePlacesAbove_nonempty`, and
  the first clause at `w` supplies a local map `ι` with
  `det(1 - X S(ι Fr))` equal to both.
- `IsWeaklyAssociated.eventually_eulerPolynomial_eq` (proved): if two
  spectral systems `s`, `t` of rank `n` are weakly associated with the same
  `S`, then at cofinitely many `v` both spectra are defined and have equal
  Euler polynomials. It follows from the previous lemma.

### The three statements

- `WeakEquivalenceRigidityStatement`: for every `c` with
  `IsArithmeticClassFamily c`, all `F`, `E` as above, and all
  `S`, `S'` as above, if `S` and `S'` are continuous and semisimple and
  `IsWeaklyEquivalent S S'`, then `Nonempty (FiniteRepresentation.Equiv S
  S')`.
- `AssociatedRepresentationUniquenessStatement`: for every `c` with
  `IsArithmeticClassFamily c`, all `F`, `E` as above with
  `[CompactSpace (AdeleQuotient F)]`, every `r`, every cuspidal class
  `π : Automorphic.CuspidalOperatorRealization.IsoClass F r`, and all `S`,
  `S'` as above, if `S` and `S'` are semisimple,
  `IsWeaklyAssociatedClass.{u, uV, uP} S π` and
  `IsWeaklyAssociatedClass.{u, uW, uQ} S' π`, then
  `Nonempty (FiniteRepresentation.Equiv S S')`.
- `AssociatedClassUniquenessStatement`: for every class family `c`, with no
  arithmetic hypothesis, all `F`, `E` as above with
  `[CompactSpace (AdeleQuotient F)]`, every `r`, every
  `S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)`, and all
  cuspidal classes `π π' : Automorphic.CuspidalOperatorRealization.IsoClass
  F r`, if `IsWeaklyAssociatedClass.{u, uV, uP} S π` and
  `IsWeaklyAssociatedClass.{u, uV, uQ} S π'`, then `π = π'`.
- `AssociatedUniquenessStatement` is the conjunction of the three
  statements above, at the same universe levels.

`IsArithmeticClassFamily c` is the predicate of the published
`Langlands.Automorphic.AssociatedFactorStatement`. It holds when some family
of local invariant maps forms a relative class formation with the arithmetic
normalization at every prime, and `c` satisfies the published generation,
restriction, inflation and local compatibility conditions. These are the
conclusion predicates of the published `GlobalFundamentalClassStatement`.
They make `W_{E/F}` the Weil group of the arithmetic fundamental class.

## Universe levels

The universe parameters are `u` for the fields, `uV` and `uW` for the
carriers of `S` and `S'`, and `uP` and `uQ` for the presentations that
witness the two association hypotheses. They are independent, and each
statement is asserted at every choice of levels:
`WeakEquivalenceRigidityStatement.{u, uV, uW}`,
`AssociatedRepresentationUniquenessStatement.{u, uV, uW, uP, uQ}`,
`AssociatedClassUniquenessStatement.{u, uV, uP, uQ}` and
`AssociatedUniquenessStatement.{u, uV, uW, uP, uQ}`.

## Source correspondence

The statements follow Henniart 2000, §2.2, printed p.444 (PDF p.6),
registered as `henniart-2000-simple-proof`. There `S` is a continuous
complex representation of degree `n` of the absolute Weil group `W_F` and
`Π` an automorphic representation of `GL_n(𝔸_F)`. They are associated if
`L(S_v, s) = L(Π_v, s)` at almost every finite place `v` where `S_v` and
`Π_v` are unramified. Henniart then writes:

> Si S est fixée, il existe, à isomorphisme près, au plus une représentation
> automorphe isobare Π de GL_n(𝔸_F) associée à S : cela découle du théorème
> de rigidité de Jacquet-Shalika [JS, Théorème 4.2]. Si Π est fixée, il
> existe, à isomorphisme près, au plus une représentation complexe continue
> semi-simple S de degré n de W_F associée à Π ; c'est l'une des variantes
> du théorème de Čebotarev, et cela découle d'arguments sur les fonctions L
> analogues à ceux de loc. cit.

Henniart's reference [JS] is Jacquet–Shalika, *On Euler products and the
classification of automorphic forms II* (1981). Its Theorem 4.2 (§4.2,
printed pp.806–807) is the linear independence of the power traces of
distinct cuspidal representations of mixed ranks. If finitely many distinct
cuspidal representations `ρ_j`, unramified outside a finite set `S_0` of
places containing the infinite places, and
complex numbers `c_j` satisfy `Σ_j c_j tr(B_{j,v}^k) = 0` for every `v ∉ S_0`
and every `k ≥ 1`, then every `c_j` is zero. Here `B_{j,v}` is the Satake
class of `ρ_j` at `v`.

- `AssociatedClassUniquenessStatement` is Henniart's first sentence, for
  cuspidal classes.
- `AssociatedRepresentationUniquenessStatement` is the second sentence.
- `WeakEquivalenceRigidityStatement` is the Chebotarev variant that the
  second sentence invokes. It compares two representations directly,
  without a cuspidal class.

The formalization differs from the source in the following derived choices.

1. **Relative Weil group.** Henniart's `S` is a representation of the
   absolute Weil group `W_F`. Here `S` and `S'` are representations of one
   finite-level group `W_{E/F}`, as in the published association relation.
   The library has no absolute global Weil group or inflation maps between
   levels; those belong to Worker 2's construction. Pulled back along the
   surjection `W_F → W_{E/F}`, representations of `W_{E/F}` become
   representations of `W_F` with the same intertwiners, the same
   subrepresentations, and the same local components. So the statements here
   are the special case of Henniart's for representations of `W_F` that
   factor through `W_{E/F}`. This comparison explains the choice and is not
   formalized.
2. **Fundamental class.** `WeakEquivalenceRigidityStatement` and
   `AssociatedRepresentationUniquenessStatement` assume
   `IsArithmeticClassFamily c`, so that `W_{E/F}` is the Weil group of the
   arithmetic fundamental class. For another class family the group
   extension is different and the Frobenius data need not determine the
   representation. `AssociatedClassUniquenessStatement` holds for every `c`.
   By `IsUnramifiedMatchAt.eq`, `S` determines the matching polynomial at
   every place where it matches one. So two classes associated with one `S`
   have equal Euler polynomials at almost every place, whatever group
   extension `W_{E/F}` is.
3. **The Chebotarev variant.** Henniart states only the consequence for two
   representations associated with one `Π`, and says that it follows from
   L-function arguments analogous to Jacquet–Shalika's. Here the
   representation-theoretic input is stated separately and generally, as
   `WeakEquivalenceRigidityStatement`: weakly equivalent continuous
   semisimple representations are equivalent. Every pair of
   representations associated with one spectral system is weakly
   equivalent, by `IsWeaklyEquivalent.of_isWeaklyAssociated`. For `E = F`,
   `W_{F/F}` is an extension of the trivial group by the idele class group
   `C_F`. A continuous semisimple representation of it is then a direct sum
   of continuous characters. The rigidity reduces to the unramified rigidity
   of finite families of Hecke characters, the subject of the published
   `HeckeEulerProductRigidityStatement`. This reduction is not formalized.
4. **Cuspidal classes only.** Henniart's automorphic side is an isobaric
   representation `Π`. Here it is an actual irreducible cuspidal class, the
   only kind that the published association relation covers. Isobaric sums
   are not covered.
5. **Hypotheses on `S`.** Henniart's semisimple `S` is
   `FiniteRepresentation.IsSemisimple`. In the two association statements,
   continuity and the degree `r + 1` are part of the published association
   relation and are not repeated. `WeakEquivalenceRigidityStatement` has no
   association hypothesis, so it assumes continuity of `S` and `S'`
   explicitly. It does not assume equal ranks. Weak equivalence implies
   them, because `det(1 - X A)` has degree equal to the rank for invertible
   `A`. `AssociatedClassUniquenessStatement` makes no semisimplicity
   assumption, as in the source.
6. **Up to isomorphism.** On the Weil side, "à isomorphisme près" is
   `Nonempty (FiniteRepresentation.Equiv S S')`. On the automorphic side it
   is equality in `IsoClass F r`, the quotient by the published equivalence
   of cuspidal realizations.
7. **Presentations.** The two association hypotheses may be witnessed by
   different presentations, in universes `uP` and `uQ`. So the proof of
   `AssociatedRepresentationUniquenessStatement` from the rigidity needs
   one more fact. Different presentations of one cuspidal class must have
   equal spectra at almost every place. That is true, because the
   unramified local components of an irreducible cuspidal representation
   are intrinsic to it. The published `CuspidalSpectralRigidityStatement`
   lists it as a separate obligation, and it is not proved here.
8. **Ranks.** `AssociatedClassUniquenessStatement` compares two classes of
   the same rank `r + 1`. Association with `S` forces the rank to be
   `S.rank` in both cases, so classes of different ranks are never both
   associated with `S`.
9. **Route to class uniqueness.** By
   `IsWeaklyAssociated.eventually_eulerPolynomial_eq`, two classes
   associated with `S` have attached spectral systems with equal Euler
   polynomials at almost every place. Since spectra are multisets of nonzero
   complex numbers, equal Euler polynomials mean equal spectra. The
   conclusion `π = π'` is then Jacquet–Shalika's Theorem 4.2 for the two
   classes. In the published form it is
   `CuspidalPowerTraceIndependenceStatement` with two classes and
   coefficients `1`, `-1`, or `CuspidalEulerConstituentRecoveryStatement`
   with one class on each side. Both are stated for presentations in one
   universe, so the case `uP ≠ uQ` also needs presentations to be compared
   across universes. No implication between these targets is proved here.

## Scope

The module states three unproved theorems, defines weak equivalence, and
proves four elementary lemmas. It does not assert:

- the existence of any weakly associated pair or of local maps `ι`;
- the comparison of spectra of different presentations of one class;
- the consequences of Henniart §2.2 for duals, determinants and central
  characters, and twists by characters;
- uniqueness for isobaric automorphic representations;
- anything about the absolute Weil group `W_F` or about archimedean places.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. Literature ID
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  Section 2.2, printed p.444 (PDF p.6): association, and the two uniqueness
  assertions quoted above. Bibliography entry [JS], printed p.455
  (PDF p.17). PDF page = printed page − 438.
- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic forms II*, Amer. J. Math. 103 (1981), 777–815. Literature ID
  `jacquet-shalika-1981-euler-ii`, SHA256
  `4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.
  Theorem 4.2, §4.2, printed pp.806–807 (PDF pp.31–32): linear independence
  of the power traces of distinct cuspidal representations of mixed ranks.
