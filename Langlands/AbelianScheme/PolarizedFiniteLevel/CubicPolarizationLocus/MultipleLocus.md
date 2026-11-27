# The divisibility locus of an abelian-scheme homomorphism

`exists_homMultiple_locus` represents the existence of a divisor by a positive natural number of an actual abelian-scheme homomorphism by a closed subscheme of the locally noetherian base. The statement tests all scheme maps into the base. `nsmul_hom_injective` proves uniqueness of the divisor.

The proof views multiplication on the source as a finite flat surjective isogeny. Its scheme-theoretic kernel is finite flat over the base by the kernel pullback square. `exists_finiteFlat_agreement_locus` represents equality of the restriction of the homomorphism to this kernel and the constant unit map. `kernelBaseChangeIso` identifies the changed kernel. `IsogenyFactorization.lift` then produces the divided homomorphism and cancellation along the isogeny gives uniqueness.

The construction generalizes the divisibility step in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), Proposition 6.11, printed pp. 122–123 (PDF pp. 135–136), source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`, SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
