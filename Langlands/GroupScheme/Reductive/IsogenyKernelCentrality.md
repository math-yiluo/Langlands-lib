# Full-kernel torus containment from opposite unipotent injectivity

This internal reduction combines the published full-kernel open-cell factorization
with the actual dynamic opposite intersection and limit decomposition.

The first helper observes that a killed point in a dynamic parabolic has a killed
limit in the dynamic centralizer. Its quotient by that limit is a killed dynamic
unipotent point. If that unipotent kernel is trivial on every test scheme, the
point equals its limit.

For a finite homomorphism, a self-centralizing torus, and a cocharacter whose
dynamic centralizer is that torus, the full kernel lies in the opposite open
cell. Its two coordinates are an opposite unipotent point and a parabolic point.
Their images have product one. Dynamic functoriality and the trivial intersection
of the target opposite unipotent with its parabolic show that the first image
is one. Triviality of the source opposite unipotent kernel kills that coordinate.
The first helper then puts the remaining parabolic coordinate in the torus.

The main theorem assumes a finite homomorphism over an arbitrary field, a smooth
affine source, an affine target, a source torus whose full centralizer equals its
pointwise range, and a cocharacter whose dynamic centralizer is that same range.
The source torus inclusion factors through the dynamic parabolic by this last
equality. Its unit opposite-unipotent coordinate therefore gives the torus
factorization required by `kernelOpenCellLift`. The actual kernel factorization
is then used on arbitrary test schemes, including nonreduced ones.

All unipotent kernel-triviality assumptions quantify over every test scheme.
They require only that a killed point in the indicated source unipotent group
be one. The target cocharacter is the actual composite with the ambient map;
no genericity assumption on it is needed. No smoothness or reducedness is
assumed for the kernel.

The helper is proved for separated group schemes over an arbitrary base. The
main theorem's affine hypotheses supply separatedness and the all-test opposite
intersection theorem. Source smoothness supplies the opposite open cell.
Flatness or surjectivity of the ambient map is not used.

When the torus inclusion is also a closed subgroup,
`kernelTorusFactorOfUnipotentKernels` constructs the actual group-scheme map
from the full kernel to the torus. A closed immersion is a monomorphism, so
the torus represents its pointwise range. The represented-subgroup
`factorHom` construction applies to the containment theorem.
`kernelTorusFactorOfUnipotentKernels_comp` proves that its composite with
the torus inclusion is exactly `kernelι q`.

This derived unit proves containment of the entire kernel in the source torus.
It does not yet prove that this kernel is central, discharge the two unipotent
kernel assumptions from root factors, or prove the full root-datum comparison.
Its provenance is the published dynamic functoriality, limit and opposite-cell
interfaces together with the preceding kernel open-cell factorization.
