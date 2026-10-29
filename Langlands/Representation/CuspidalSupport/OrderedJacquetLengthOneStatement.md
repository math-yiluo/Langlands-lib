# An ordered length-one Jacquet criterion

Author: Worker 163; Worker 949 revised the premise description. This is an
internal derived proposition, with all its representation-theoretic
hypotheses explicit. It supplies no proof of those hypotheses or of the
unconditional two-supercuspidal theorem.

`Langlands.CuspidalSupport.NormalizedJacquetOrderedLengthOneCriterion`
quantifies a prime, an actual finite p-adic field extension `F`, compatible
topological data `T`, a rank `n`, a block shape `B`, and an actual smooth complex
representation `A` of `GL_n(F)`. It also quantifies two complex representations
`σ` and `τ` of the actual Levi `B.Levi F.Carrier`, with independent carrier
universes. The coefficient field is Mathlib's complex numbers `ℂ`. The field,
ambient carrier, and two target carriers have four independent universes
`uF`, `uA`, `uW`, and `uZ`. No smoothness hypothesis is imposed on the targets.

The premises are as follows. The first concerns only `σ` and `τ`; the others
are imposed for every actual invariant subspace `S` of `A`
(a `Subrepresentation` of `A.representation`) and every intertwiner `f`.

1. `σ` and `τ` are irreducible and there is no representation equivalence
   `σ ≃ τ`.
2. The intertwiner `f`, from the actual smooth representation on `S` into the
   normalized parabolic induction of `σ`, is nonzero.
3. Each of the actual normalized Jacquet modules of `S` and `A / S` has
   `repLength` one.
4. The actual normalized Jacquet module of `A` has
   `HasJordanHolderMultiplicity` exactly one for the target `τ`.

The last premise is an actual composition-series witness with one occurrence
of `τ`, as defined by `Filtration.MultiplicityStatement`; it is not an assumed
equality of classes. `repLength` is composition length as a module over the
monoid algebra, valued in the extended natural numbers.

The conclusion gives actual `Representation.Equiv` witnesses from the
normalized Jacquet module of `S` to `σ`, and from that of the actual module
quotient `A / S` to `τ`. The source carriers lie in universe `uA`; the target
carriers lie in `uW` and `uZ`. The equivalences therefore allow independent
carrier universes. They intertwine the action of the same actual Levi.
The statement uses the published smooth subrepresentation, quotient and
normalized Jacquet functor, without choosing abstract substitute objects.

## Derived provenance and scope

The motivation is Zelevinsky (1980), Proposition 1.11, printed p.175/PDF p.12,
and the count-one Frobenius argument of Bernstein–Zelevinsky (1977),
section 2.16(1), printed pp.449–450/PDF pp.10–11. The criterion is an
internal algebraic consequence of the explicit premises, rather than a
transcription of an unconditional result from either source.

Evaluation at the identity sends the specified nonzero map to a nonzero
intertwiner from the Jacquet module of `S` to `σ`. Its source is irreducible
by length one, so Schur's lemma gives the first actual equivalence. Exactness
of the actual normalized Jacquet functor gives a short exact sequence from
the Jacquet module of `S`, through that of `A`, to that of `A / S`.
The first term has no factor equivalent to `τ`, since it is equivalent to
the inequivalent irreducible `σ`. Additivity gives multiplicity one for `τ`
in the last term. That term is itself irreducible by length one; its
multiplicity-one witness therefore gives an actual equivalence to `τ`.
Thus the conclusion uses both length-one information and actual exactness,
in addition to multiplicity.

With the Library's upper induction and right translation convention,
evaluation contributes the positive half modulus and normalized Jacquet
contributes its inverse; these factors cancel. In a two-supercuspidal
application `σ` is the tensor in the inducing order and `τ` the reversed
tensor. This criterion proves neither tensor irreducibility or inequivalence,
the two length-one premises, nor the ambient multiplicity-one premise.
Those remain separate obligations, as does the construction of the specified
nonzero map.

Originals: `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`;
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
No segment, derivative, analytic classification or exhaustion theorem is
asserted or assumed as a proved input.
