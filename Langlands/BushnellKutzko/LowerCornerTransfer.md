# Transfer from the shifted lower-corner kernel

`LowerCornerTransferStatement` concerns a simple stratum `[𝔄,n,0,β]`
with a defining sequence over a nonarchimedean local field and a BK
additive character. Write `P` for the ambient filtration, `𝔥^m` for
the H lattice layer, and `D` for trace duality. Let `θ` be simple on
`H^m` at index `m−1`, where `m ≥ 1` is below the level and critical bounds.
Take complementary orthogonal projectors `e₁,e₂` in the integral
centralizer and `ζ′` in the depth `−1` centralizer lattice. Let `K` be
the subgroup of `H^m` whose lower corner lies in `P^(m+1)`. The
character `ϑ` on `K` is the restriction of `θ` multiplied by the trace
twist for `c ∈ P^(-m)` commuting with both projectors.

Suppose `𝔥^m ⊆ X ⊆ P^m`, `I ⊆ P^1`, and
`D(X) = a_β(I) + P^(1−m)`. The upper units
`u(y) = 1 + e₁ ζ′ y e₂` for `y ∈ I` must preserve `H^m` and fix `ϑ`
on the kernel defined by `e₂(k−1)e₁ ζ′ ∈ X`. For a complex
representation and a subgroup `M` of the upper block unipotent group,
the conclusion transfers isotypy from this kernel to `K` while
preserving existence of a vector outside the `M` Jacquet relations.

`exists_isotypic_of_lowerCornerKernel` uses the finite quotient of `K`
given by the shifted lower corner. The upper units preserve the lower
corner and hence induce conjugation ratios on this quotient. If a
ratio is trivial, the unit fixes `ϑ` on `K`. The unit preserves
`H^(m+1) = H^m ∩ U^(m+1)`, which lies in `K`. The twist is fixed
there, so the unit intertwines the forward restriction of `θ`.
The conjugation difference of `β` is exactly `a_β(e₁ ζ′ y e₂)`.
The intertwining formula puts the unit in the simple-character double
coset, and covariance places the difference in `D(𝔥^(m+1))`. The
corresponding reference trace character is trivial. The reference family
separates by double trace duality. Kernel comparison and finite abelian
duality then make the conjugation ratios surjective. The transfer follows
by character averaging, since the upper units commute with `M`.

This adapts the character comparison of Bushnell–Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993),
to the subgroup \(K\) with lower corner in \(P^{m+1}\). The comparison
in (8.2.26) uses all of \(H^m\) and takes the quotient by the product
of \(U^m(\mathfrak B)\) and the full shifted overlap. The Lean proof uses
the intertwining formula (3.3.2) and the covariance calculation (3.3.9)
for the kernel inclusion, followed by the averaging step of (8.2.14).
See printed pp. 105, 108, 281–282 and 288–289 (PDF pp. 117, 120,
293–294 and 300–301).
