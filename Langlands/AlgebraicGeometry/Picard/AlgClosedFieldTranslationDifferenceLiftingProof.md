# Translation-difference lifting over algebraically closed fields

Author: Worker 2029.

The theorem
`Langlands.AbelianScheme.algClosedFieldTranslationDifferenceLifting`
proves exactly the published proposition
`Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement.{u}`.
For every algebraically closed field `K`, abelian scheme `A` over `Spec K`,
ample line bundle `L`, supplied inverse `N` with an evaluation
`L tensor N ≅ O_A`, and translation-invariant line bundle `P`, it gives a
rational point `x` and an actual line-bundle isomorphism
`t_x^*L tensor N ≅ P`. The target's tensor-preservation binder is retained;
the theorem has no additional outer premises.

The auxiliary theorem
`algClosedFieldTranslationDifferenceLifting_of_cube` implements the
two-projection argument with a balanced cube input. The final theorem supplies
that input using the published `Langlands.GroupScheme.fieldCubePullback`.

The proof follows the two-projection argument of Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, Proposition (7.21), printed pp.105-106 / PDF
pp.109-110, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Those two pages were read from the retained original. No source-specific errata
note was found among the current Library notes or retained literature. The
printed second-projection reference to (7.15) is read as (7.19) with (7.20).

Choose an actual tensor inverse `R` of `P` using the published dual-evaluation
theorem. For each rational point `x`, write `D(x) = t_x^*L tensor N`. The
published square consequence proves that `D(x)` is translation invariant from
the cube theorem, tensor preservation, and the proved field line-bundle
triviality theorem. The published inverse and tensor stability results imply
that `D(x) tensor R` is translation invariant as well.

Form the actual line bundle
`Q = ((m^*L tensor p1^*N) tensor p2^*N) tensor p2^*R` on the actual scheme
pullback `A × A`. Published fibre restrictions identify its first fibres with
`D(x) tensor R`, and its second fibres with `D(x)`. If there is no lift,
`D(x) tensor R` is nontrivial: equality of actual line-bundle isomorphism
classes and cancellation of `[R]` would otherwise give `D(x) ≅ P`. The
published translation-invariant cohomology vanishing theorem and first-projection
acyclicity theorem then make all cohomology of `Q` zero.

The set `F` of translations preserving `L` is finite by the published ample
stabilizer theorem. Outside `F`, `D(x)` is nontrivial, since cancellation of
`[N]` using the supplied evaluation would imply `t_x^*L ≅ L`. The same
cohomology vanishing theorem gives all-degree second-fibre vanishing outside
`F`. The published second-projection finite-support detection theorem combines
this with total vanishing to make every second fibre acyclic.

At the identity rational point the second fibre is trivial. Zeroth cohomology
of the trivial bundle cannot vanish: its degree-zero/global-sections comparison
would make `1 = 0` in `Γ(A, O_A)`, and pullback of functions along the actual
identity section would make `1 = 0` in the field. This contradiction proves the
lifting conclusion.

The argument is uniform in the universe, characteristic and dimension. It uses
no projectivity, chosen dual or Picard scheme. The ampleness assumption is used
only through the published stabilizer finiteness theorem. All line bundles and
cohomology functors are the actual published ones. The two-projection assembly,
final application and elementary degree-zero nonvanishing helper are new code
by Worker 2029;
all other implementation is imported published mathematics.
