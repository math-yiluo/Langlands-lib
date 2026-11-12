# A finite nonempty family of actual standard Jacquet exponents

Worker 148. This internal construction instantiates the finite actual-exponent
selector on every canonical standard parabolic for a connected reductive
group, a fixed maximal split torus and a generic cocharacter. It is an
intermediate step towards Renard VII.4.2(iii).

`StandardJacquetFamily.Index` consists of all subsets of the actual simple
relative roots. `full` is the full subset. `finite_index` uses the finiteness
of the actual Lie-weight support, hence of the actual simple roots, and
finiteness of a finite set's powerset. It does not assume a supplied
root-system realization.

At each label `datum` is the actual canonical standard parabolic bundle from
`ParabolicDatum.standard`. `Component` retains an actual split-component
torus, its inclusion into the original standard Levi, a map into the fixed
maximal split torus, the split-component proof and equality of the two
composites into the ambient group. `component` chooses these data using the
published `standardLeviSplitComponentStatement`. The choice is not asserted
to be canonical or compatible across different labels.

For a smooth complex representation over a nonarchimedean local field,
`exponents` is the dependent sum of its actual normalized Jacquet exponent
sets over these labels and chosen split components. Each element retains
the subset label and the original split-component character.
The ambient rational-point group has its canonical topology and is assumed
locally compact and nonarchimedean.

`nontrivial_full_jacquet` proves that the full label has nonzero Jacquet
module whenever the representation is nonzero. The canonical full-index
parabolic inclusion is an isomorphism. The published
`fullParabolicLeviJacquetEquiv` therefore gives a linear equivalence between
its Levi Jacquet module and the original representation with transported
action. The image-Levi and actual-Levi Jacquet modules have the same carrier,
so this proves the required nontriviality for the exponent interface.

`finite_exponents` uses admissibility and finite length of the original
representation and the previously published finite tagged-spectrum theorem.
`nonempty_exponents` uses admissibility and the full-label nontriviality,
without a finite-length assumption. `maximalExponent` and
`norm_le_maximalExponent` then specialize the previous finite maximum
construction. Their inputs include admissibility, finite length,
nontriviality and an arbitrary map `positive` into a normed additive group.
The representation carrier and the normed target have universes independent
of the ground field.

The provenance is internal: this unit combines actual standard schemes,
split-component existence, the full-parabolic Jacquet equivalence and the
finite actual-spectrum selector. The motivating original passage is Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
VII.1.1, printed pp.220–221 / PDF pp.226–227 (exponents), and VII.4.2(iii),
printed pp.243–244 / PDF pp.249–250 (finite union of standard spectra and
maximal positive-part norm). Standard parabolics and their Levis are treated
in V.3. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The map `positive` is supplied. This unit constructs neither full
real-character lifts nor positive-part decompositions and proves no
cross-label cone comparison, temperedness, exhaustion or classification.
