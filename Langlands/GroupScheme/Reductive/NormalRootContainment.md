# Root containment from restriction to a normal subgroup's torus

This internal construction uses the published intrinsic root functor, positive
cocharacter pairing, and contraction into a closed normal subgroup. It does not
prove the full normal-root dichotomy or almost-simple generation.

Let \(f:S\to T\) be a morphism of commutative group schemes over a field,
\(t:T\to G\), \(s:S\to H\), and \(h:H\to G\) actual group homomorphisms with
\(ft=sh\). Assume that \(S\) is a split torus, that \(h\) is a closed subgroup
inclusion, and that its full range is normal on every test scheme. For any
character \(\alpha:T\to\mathbf G_m\) with \(f\alpha\ne0\),
`subgroup_le_range_of_restriction_ne_zero` puts the entire intrinsic
`RelativeRoot.subgroup t α` in the full range of \(h\). No smoothness,
connectedness, semisimplicity, maximality, algebraic closedness, or root
dimension hypothesis is imposed.

The proof chooses a cocharacter of \(S\) pairing positively with \(f\alpha\).
Its composite with \(f\) pairs positively with \(\alpha\), so the published
positive-root contraction theorem puts the root functor in its dynamic
unipotent subgroup. The cocharacter factors through \(h\). The published
normal-subgroup contraction theorem therefore puts this dynamic subgroup in
the full range of \(h\).

The contrapositive says that every outside root restricts to zero on \(S\).
The general-base lemma
`subgroup_le_fixedSubgroup_of_restriction_eq_zero` proves that a root whose
character restricts to zero centralizes the image of \(S\), after every
refinement. It evaluates the defining affine-line orbit extension at the
character value \(1\), both for a point of \(S\) and for the identity. Thus
`subgroup_le_range_or_fixedSubgroup` gives containment in \(H\) or
centralization of this chosen torus. Centralization of the whole of \(H\)
remains a separate obligation.

For any supplied actual representative \(j:U\to G\) of the root functor,
`normalRootLift` constructs a factor \(U\to H\) when the restriction is
nonzero. `normalRootLift_comp` identifies its composite with \(h\) with the
original \(j\). The represented-subgroup lift API supplies this actual
factorization from the proved all-test containment.
