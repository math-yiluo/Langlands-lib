# Section killing and quadrant propagation

This internal draft uses `SectionKillingStatement` as an explicit hypothesis.
It does not prove that statement or the final Serre vanishing theorem.

`Vanishes f N₁ N₂ G i a b` denotes zero actual relative cohomology in degree
`i` of `(G ⊗ N₁^a) ⊗ N₂^b`. The module constructs the tensor isomorphisms
needed to shift either exponent and proves the corresponding vanishing steps
from the kernel, source, and cokernel terms of multiplication by a section.

The conditional assembly takes positive powers `d₁,d₂`, sections of those
powers, a support dimension bound for `G`, and goodness of all four kernel
and cokernel modules. It chooses a common threshold `m` for these errors and
starts the grid at `B = m d₁`. For each positive degree up to the support
bound and residue pair `r₁ < d₁`, `r₂ < d₂`, section killing is applied with
the additional line bundle `P = N₁^r₁ ⊗ N₂^(B+r₂)`. The ray is regrouped
using the tensor-power multiplication and addition isomorphisms. Finite
residue propagation gives one quadrant threshold. Degrees above the support
bound vanish by the Library's support-dimension cohomology theorem.

This route avoids a separate passage from powers of ample bundles back to
the original pair. It is derived proof infrastructure implementing the
argument in the documentation of `ProperAmplePairSerreVanishingStatement`.
