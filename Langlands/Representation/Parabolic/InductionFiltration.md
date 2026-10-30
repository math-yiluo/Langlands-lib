# Actual normalized induced filtrations

This internal construction packages the published value filtration from
`Parabolic/InductionFactorMatchingProof` for an arbitrary supplied
`ObjectRepFiltration` of an actual Levi representation. It supplies the actual
induced filtration for every Levi representation, and, when the Levi
representation is smooth, equivalences of its graded representations and an
embedding theorem. None of these requires simple graded pieces or finite
length. It does not establish any segment representation theorem or multisegment
exhaustion.

For a block shape `B`, a representation `σ` of its actual Levi subgroup, and a
finite filtration `s` of `σ`, `normalizedInductionFiltration T B σ s` is the
filtration of the actual normalized upper parabolic induction. Its step at `i`
consists of smooth induced functions whose values lie in `s.subrepresentation i`.
The displayed step equality is definitional. Monotonicity and the zero and full
endpoints follow from the corresponding properties of `s` and the published
`Induction.valueFiltration`. This construction and its step equality place no
smoothness restriction on `σ`.

The three declarations described below assume `IsSmooth σ`. An
`ObjectRepFiltration` is a filtration in `Rep`, so smoothness of `σ` is not
implicit in `s` and is an explicit hypothesis of each of them.

`nonempty_normalizedInductionFiltrationGradedEquiv` assumes that `σ` is smooth.
It identifies an induced graded quotient with the normalized induction of any
smooth Levi representation `π` equivalent to the corresponding quotient of `s`.
It applies the published `nonempty_valueQuotient_equiv_induced`, which has the
same hypotheses `IsSmooth σ` and `IsSmooth π`, using the proved generic smooth
induction surjectivity theorem through
`normalizedInducedSurjectivity_of_smoothInductionSurjectivity`. Thus right
exactness is proved upstream, rather than supplied as a new assumption.

`normalizedInductionFiltrationGradedEquiv` also assumes that `σ` is smooth. It
chooses the equivalence with the induction of the actual quotient itself. That
quotient is smooth because `σ` is: its upper filtration step inherits
smoothness from `σ` through its injective inclusion, and the graded projection
is surjective. Classical choice selects an equivalence from the published
nonemptiness result; no canonical formula for this selection is claimed.

`exists_injective_normalizedInduced_graded` assumes that `σ` is smooth and takes
an actual injective intertwiner from an irreducible representation into the
induced ambient representation. The published
`ObjectRepFiltration.exists_injective_graded` gives an injective map into one
actual induced graded piece. Composing with the equivalence chosen by
`normalizedInductionFiltrationGradedEquiv`, which is where `IsSmooth σ` is used,
gives an actual embedding into the normalized induction of the corresponding
original quotient.

Smoothness cannot simply be dropped from the graded equivalences, because
smooth induction only sees smooth vectors. The following informal example,
which is not formalized here, shows this. Take the one-block case of
`GL_1(Q_3)`, where the parabolic subgroup is the whole group and normalized
induction of a representation is isomorphic to its subspace of smooth vectors.
Choose a homomorphism `α` from the multiplicative group `Q_3^×` to the additive
group `ℂ` with `α(4) = 1`; it exists because `4` has infinite order, by
extending a `ℚ`-linear functional from the rationalization of `Q_3^×`. Since
`4^(3^k) → 1` while `α(4^(3^k)) = 3^k`, the kernel of `α` contains no open
subgroup. Let `σ(g)(x, y) = (x + α(g) y, y)` on `ℂ^2`. Its smooth vectors are
exactly `ℂ e_1`. For the filtration `0 ⊂ ℂ e_1 ⊂ ℂ^2`, both induced steps are
the whole induced representation, so the top induced graded piece is zero. The
corresponding quotient of `σ` is the trivial character, whose normalized
induction is one-dimensional. The Lean hypothesis `IsSmooth σ` excludes this
`σ`.

The field and all representation carriers have independent universes. The
induced carrier has the universe determined by the actual smooth induction
construction. The argument covers a filtration of length zero: the construction
still makes sense, and the embedding conclusion would require an element of
`Fin 0`, so its embedding hypotheses cannot hold.

The provenance is an internal assembly of existing constructions and proofs.
The used proof route consists of value subrepresentations, smooth induction
surjectivity, smoothness transfer, and irreducible embeddings into supplied
finite filtrations. It uses no classification conclusion, ordering theorem,
adjacent commutation, or linked-segment filtration. The `GL_1(Q_3)` example
above was raised in the external library audit of 2026-10-29 (finding P2-02)
and checked by hand for this documentation; for one block the parabolic
subgroup is the whole group and the half-modulus character, an empty product,
is trivial.
