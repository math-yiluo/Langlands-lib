# Finite constituents of the normalized cuspidal section model

For a cuspidal spectral presentation, expose the selected finite local
factor of its restricted tensor product. The Library identifies that factor
with the actual local component in the presentation. It also recovers the
whole cuspidal carrier by evaluating finite intertwiners on the chosen
finite tensor realization. Combining these equivalences puts the action
of the selected local group on the local component tensor factor and the
trivial action on the remaining factors. `localMultiplicityEquiv` gives
this action comparison on the actual cuspidal carrier.

Take tensor products of basis coefficient maps in the trivial multiplicity
spaces. They intertwine the full block Levi action with the tensor of its
actual local block components. A basis coordinate of the tensor of all
factors is a basis coordinate after projection on the chosen multiplicity
coordinates. Hence the maps separate every vector of the inducing
coefficient. The normalized local section slices then give separating
intertwiners to the corresponding normalized local induction.

When the given irreducible operator subquotient is a finite adelic
subquotient of the parametrized normalized induction of these cuspidal
blocks, `FiniteParametrizedBlockInduction.HasSubquotient` records that
realization by an actual subrepresentation and a surjective intertwiner.
`isFiniteInducedConstituent_of_parametrizedInduction` gives the published
finite constituent predicate. The existential form chooses the required
spectral presentations by taking irreducible admissible finite slices of
the cuspidal blocks and applying the Library's presentation existence theorem.

This is a derivation from the induced realization in Langlands, *On the
notion of an automorphic representation*, Corvallis Part I (1979), printed
p. 205 (PDF p. 200), and the finite-place constituent passage in Lemma 1,
printed p. 203 (PDF p. 198), source `langlands-1979-notion-automorphic-representation`.
The component projection uses the Library's actual restricted tensor and
multiplicity evaluation. Pointwise slices implement the local normalized
induction comparison.
