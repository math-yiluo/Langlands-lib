# Actual central maximal split-torus quotients and norm-kernel compactness

This internal derived unit constructs the actual algebraic quotient needed by the
compactness route and proves the rational-point adapter, retaining the two
unproved structural obligations explicitly. It imports only named Library
interfaces and the norm-kernel open-central-quotient reduction; no external
source assertion is used independently here.

`exists_smooth_anisotropic_central_split_quotient` works over any field at
arbitrary universe. Given a smooth affine group and a central maximal split
torus inclusion, it constructs a smooth affine actual quotient by the full
all-test range of that torus. The quotient has split rank zero and the
projection is smooth. Normal-subgroup quotient existence gives the actual
quotient. Closedness of the torus makes it a representative of its range,
and affineness gives quasi-compactness of the projection. Smoothness of the
split torus and the represented-kernel descent theorem give smoothness of
the projection. The published maximal-split-quotient theorem gives anisotropy.
This construction does not establish reductivity of the quotient.

`CentralSplitQuotientNormKernelCompactnessStatement` is a proposition that
explicitly assumes the entire `AnisotropicCompactnessStatement`. Over every
nonarchimedean local field in the same arbitrary universe, it takes connected
reductive source and quotient groups, a central maximal split torus inclusion
in the source, and an actual fppf quotient homomorphism by its full range. It
concludes compactness of the actual source rational common norm kernel in
exactly `rationalPointTopology F G.X`. Connected reductivity of the specified
quotient is an input to this conditional adapter.

`centralSplitQuotientNormKernelCompactness` proves that proposition. As in the
construction, the actual projection is smooth because its represented kernel
is the smooth split torus. Smooth rational-point openness makes its point map
open in the two canonical topologies, and functorial continuity bundles that
point map as a continuous homomorphism. The all-test kernel equality implies
centrality of its rational-point kernel. Maximality implies split-rank-zero
anisotropy, so the explicitly assumed anisotropic compactness statement makes
the quotient's canonical rational-point topology compact. Smooth affineness
and the local-field topology supply the topological-group and Hausdorff
instances. Applying the norm-kernel reduction proves compactness.

No rational-point surjectivity is assumed or inferred from scheme surjectivity.
Neither characteristic nor split rank is restricted. Applying this unit to the
actual centralizer-zero target still requires unconditional connected
reductivity of its actual quotient, a published proof of anisotropic compactness,
the source centralizer structure, and the supplied zero subgroup's openness
and containment. This unit does not prove that final target.
