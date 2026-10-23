# Recovery of the untwisted inducing tensor at a fixed regular parameter

Authors: Worker 19 and Worker 47. Worker 47 supplied the exact consumer interface
in his shared conditional uniqueness assembly; Worker 19 prepared this separate
statement and its original-source correspondence.

`Langlands.GLRegularLanglandsTensorRecoveryStatement` is a proposition definition.
It isolates the recovery of the inducing representation after the standard
parabolic and real parameter have already been identified. It supplies no proof.

## Exact assertion and actual objects

For every prime `p`, finite extension `F : PadicField p`, topological realization
`T`, positive total rank `n`, and ordered block shape `B`, take two families
`σ`, `σ'` of actual smooth complex representations of the same block groups.
Every factor of both families must be irreducible and analytically tempered.
Take one real exponent function `t` with `StrictAnti t`, and two smooth
representations `π`, `τ` of `GL_n(F)`. If `π` and `τ` are irreducible quotients
of the corresponding standard modules and are isomorphic, then the two
untwisted external tensor representations of `B.Levi F.Carrier` are equivalent.
The conclusion is `Nonempty (Representation.Equiv ...)`; it selects no map.

The two standard modules are built by the existing
`TemperedLanglandsDatum.mk B ... t ht`. Its quotient relation unfolds to
irreducibility of the target and the existence of an actual surjective
intertwiner from its standard module. There is no head premise, chosen
quotient, kernel uniqueness certificate, or assumption of the desired
Levi equivalence. Each block's smoothness is carried by `SmoothRep`.
`T.IsTempered` includes admissibility and a unitary central character, with
all smooth matrix-coefficient norms in `L^(2+ε)` modulo the actual center
for every `ε > 0` and every Borel Haar measure.

The standard module is the actual normalized upper parabolic induction of
`B.blockTensor` applied to the factors twisted by `|det|^(t i)`.
`B.blockTensor` is the published finite external tensor representation on
`PiTensorProduct`: the `i`-th Levi block acts on the `i`-th factor. The output
uses the original factors `(σ i).representation` and `(σ' i).representation`,
with no determinant twist. The single import is the published
`Langlands.Representation.Classification.LanglandsData`; no uniqueness theorem
is imported or used as a proved dependency.

The universes `uF` and `uV` are independent. All block and quotient carriers
are in `Type (max uF uV)`, which is closed under the actual induction carrier.
The two tensor carriers may differ as types. This is not a dimension
restriction. The positive-rank condition matches the existing regular Langlands
statement family. For one block `StrictAnti t` is vacuous, allowing any real
central twist. The exponents need not be individually positive or sum to zero.

## Original sources, specialization and normalization

The retained Silberger article was previously read in full. For this statement,
printed pp.97 and 101–104 were reread, and Proposition 6.1 and its concluding
recovery argument on pp.102–103 were checked in the page images. Kudla's
pp.367–368 and 372–374 were reread directly. No source-specific errata file
was present in the current Library.

| Original source | Exact location | Use |
| --- | --- | --- |
| A. J. Silberger, *The Langlands quotient theorem for p-adic groups* (1978), source `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`, SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5` | §1 pp.96–97; Theorem 4.1 p.99; Lemma 5.6 and Propositions 5.7–5.8 pp.101–102; Proposition 6.1 pp.102–103 (one-based PDF pages 8–9) | The fixed-parabolic, fixed-parameter consequence of recovery of the tempered inducing class, with arbitrary irreducible quotient witnesses. |
| S. S. Kudla, *The local Langlands correspondence: the non-archimedean case* (1994), source `kudla-1994-local-langlands-nonarchimedean`, SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | §1.1 pp.367–368; §2.2 pp.372–374, especially Theorem 2.2.2(a)–(b) (one-based PDF pages 383–384) | Confirms the explicit upper-block formulation, analytic tempered convention, and uniqueness of the tempered factors for strictly descending real determinant twists. |

Silberger's Proposition 6.1 permits two different standard parabolics and
regular-positive parameters and recovers both, together with the tempered
inducing class. Here the parabolic and parameter are fixed from the start,
and only equivalence of that inducing representation is asserted. Passing
from a representation class to `Nonempty Representation.Equiv` expresses the
same equivalence relation on actual modules. The source uses the distinguished
quotient `J`; its unique-irreducible-quotient result in Theorem 4.1(1) and
Lemma 5.6 makes every weak irreducible quotient isomorphic to `J`. This explains
the weaker quotient premises without assuming the uniqueness result as data.

This is a derived GL_n specialization of Proposition 6.1, not a literal
restatement of Proposition 5.7. At the end of Proposition 6.1, after identifying
the Levi and parameter, Silberger uses Proposition 5.8 to obtain a common
inner-induction support condition and then Proposition 5.7 to recover the
tempered class. Proposition 5.7 has specific inner cuspidal support and
intermediate discrete-series hypotheses; this pair does not discard them
from a claimed direct transcription. The relative statements encoding that
route remain separate work. In particular, the constituent restriction
identified in `notes/jacquet/silberger-lemma53-scope.md` still governs use of
Lemma 5.3 in that route.

For GL_n the inducing representation of the product Levi is the external
tensor of the tempered block factors. The mathematical specialization needs
irreducibility and temperedness of that product and compatibility of its
induction with block induction. Kudla's explicit Theorem 2.2.2 confirms this
block formulation: equal irreducible quotients recover each tempered factor,
and the tensor of the factor isomorphisms gives the conclusion here. This is
source correspondence, not a formal proof supplied by the definition.
Kudla's account does not replace the original Silberger proof route.

The Library uses `|uniformizer| = q^(-1)`. Upper induction acts by right
translation with positive-half-modulus covariance. Silberger's parameter
`-i λ` gives `q^(<λ,H>)`, represented here by the product of
`|det m_i|^(t_i)`. The positive regular chamber is strict descent of the
`t_i`; on block scalars its exponents are `B.size i * t_i`.
Equal real exponents require the separate GL_n grouping theorem before this
statement applies. No assertion of irreducibility of arbitrary reductive
tempered induction is made. The analytic comparison between Silberger's
weak tempered convention and `L^(2+ε)` remains a separate formal obligation,
as recorded in `TemperedExponentStatement.md` and
`TemperedInductionStatement.md`.

## Use in the uniqueness proof and remaining scope

The statement is intended for use after ordered block sizes and real exponents
have been matched. The published `eq_of_orderIso` in
`Classification/RegularLanglandsRecovery` turns the ordered shape match into
an equality; after transporting along it and the exponent equality, this
proposition has precisely the required input types. Its conclusion feeds the
published `PadicField.TopologicalData.blockIsoOfTensorEquiv`, which recovers
actual smooth isomorphisms of the individual irreducible factors. This
explains the tensor-valued interface rather than asserting an arbitrary
comparison relation or choosing canonical representatives.

The proposition has no proof here. A proof used to assemble full uniqueness
must establish this recovery independently of full data uniqueness to avoid
circular reasoning. Neither the numerical parameter comparison, the detailed
relative comparisons and cosocle multiplicities, semistandard conjugacy, nor
maximal-cone exhaustion is supplied by this pair. Publishing this target
therefore does not complete the broad Jacquet/exponent statement task.
