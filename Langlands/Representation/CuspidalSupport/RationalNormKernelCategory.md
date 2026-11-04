# Actual norm-kernel factors for Renard VI.3.4

Worker 6 constructs the full factors and the category-decomposition assertion
in Renard's theorem VI.3.4. This is a definition unit. It does not prove that
these factors decompose the category, fixed-level finiteness (KF), or a
comparison with other descriptions of compact blocks.

The registered original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are IV.1.3, definition and coefficient criterion,
printed pp.89–90 / PDF pp.95–96; IV.1.6, notations, printed p.94 / PDF p.100;
IV.1.7, printed p.95 / PDF p.101; VI.3.4, printed pp.145–146 / PDF
pp.151–152; and Appendix A.IX, printed p.268 / PDF p.274.

The field `F : Type uF` is an arbitrary nonarchimedean local field.
`G` is an actual affine group scheme of locally finite type over `F`.
These hypotheses form the definitions; connected reductivity will be a
hypothesis of the separate universal theorem. The point group has the
published canonical `rationalPointTopology F G.X`. Its actual subgroup
`Plancherel.rationalCommonNormKernel G` is the intersection of the kernels of
the normalized absolute values of all actual rational algebraic characters.
The subgroup has the induced topology. The imported
`RationalNormKernelTopology` already proves its openness; no alternative
group or topology is supplied here.

For an existing
`CompactCoefficientClass.{uF, uV} (Plancherel.rationalCommonNormKernel G)`,
`rationalNormKernelClassSumProperty G c A` asks for an index type `I : Type uV`,
actual irreducible compact-coefficient smooth representations `D i`, and
actual equivariant maps `(D i).obj ⟶ A`. Every `D i` has class `c`, and the
cofan with these maps and vertex `A` must have the categorical coproduct
universal property. Thus `A` is a direct sum of representatives of `c`, as in
the source's definition of `M(0G)_τ`. The multiplicity index may be infinite
or empty. It is in the carrier universe; this convention places no bound of
the carrier universe by the field universe, and no resizing result is claimed.
`RationalNormKernelClassSumCategory` is the corresponding actual full
subcategory. No representative of `c` is selected. The existing quotient
identifies precisely isomorphic irreducible compact-coefficient objects.
The construction does not replace direct sums by a condition on irreducible
subquotients or assume a comparison between these conditions.

`rationalNormKernelNoCompactSubquotientProperty G A` says that, for every
actual smooth representation `D` in the same carrier universe, if `D` is
nonzero and an actual subquotient of `A`, then
`HasCompactSmoothDualCoefficients D.representation` is false.
`RationalNormKernelNoncompactCategory` is its full subcategory. The
subquotient is not required to be irreducible. Nonzeroness is explicit:
the zero representation has compact coefficients and is a subquotient of
every object, so excluding zero is necessary for the source's remaining
factor to have its intended meaning.

IV.1.3 first defines compactness by compact support of every averaged
vector-valued function
`g ↦ π(e_K) π(g⁻¹) v`, for every vector and compact open subgroup `K`,
and then states its equivalence with compact support of all smooth-dual
scalar coefficients. This construction uses that scalar formulation.
The proof comparing it with the original averaging definition, including
the inversion convention, remains a separate obligation. IV.1.3 assumes
unimodularity for its section; this unit asserts no averaging comparison
or theorem without that hypothesis.

The reused coefficient predicate tests every vector and every algebraic
functional smooth for the contragredient action. Its coefficient is
`g ↦ ℓ (ρ g v)`, with compactness expressed by `HasCompactSupport`.
This is compact support of matrix coefficients, not compactness of a
representation space or finite dimension. On a smooth representation these
coefficients are locally constant, so their nonzero loci are closed and
topological support agrees with the source support convention. No
admissibility, finite length, finite dimension, unitarity or central character
is imposed.

`rationalNormKernelProductProperties` uses `some c` for the class-sum factor
and `none` for the remaining factor. The two evaluation lemmas are
definitional equalities.
`IsRationalNormKernelCategoryDecomposition` applies the published
`Renard.IsCategoryDecomposition` of Appendix A.IX to this family. It asserts
that every actual object is the vertex of a coproduct with one object in each
factor, and that every morphism between distinct factors is zero. The possibly
large class index is retained; no assertion that every family with that index
admits a coproduct is added.

The intrinsic class-sum transport proof keeps the same representatives and
composes each coproduct injection with the ambient isomorphism. A cofan
isomorphism transports the universal property. Closure of the remaining
factor under subquotients composes the actual subquotient witnesses with the
published `smoothSubquotientTransitivity`. Its isomorphism transport uses the
published `IsSubquotient.of_iso_right`. These arguments prove no compactness,
semisimplicity, finiteness or decomposition theorem.

The universal connected-reductive norm-kernel KF and decomposition statements
remain to be submitted separately over published definitions. Their proofs
retain the VI.2.3 and VI.2.4 inputs, the compact norm-kernel restriction
arguments and the IV.1.7 assembly. In particular this unit does not discharge
the existing conditional projector hypotheses or identify their ranges with
the class-sum factors.
