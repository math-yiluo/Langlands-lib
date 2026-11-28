# Affine spaces for rational Bruhat factors

`Langlands.GroupScheme.rationalBruhatCellAffineSpace` proves
`RationalBruhatCellAffineSpaceStatement`. It uses the actual pullback
\(W_n=nVn^{-1}\times_G U\), where \(U=U(\chi)\) and \(V=U(-\chi)\)
over an arbitrary field \(k\). This is the intersection in Borel–Tits,
*Groupes réductifs* (1965), §§5.13 and 5.15, printed pp. 99–101
(PDF pp. 46–48). The registered source is `borel-tits-1965-groupes-reductifs`,
SHA-256 `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.

The normalizer action on cocharacters gives a cocharacter \(\xi\) of the
same torus with \(i\circ\xi=\operatorname{Int}(n)\circ(-\chi)\).
Transport of the identity-limit functor through the inner isomorphism
identifies the range of \(V\to G\) after conjugation with \(U(i\circ\xi)\).
The original torus acts on \(U\) because it commutes with \(\chi\).
Restricting this conjugation action along \(\xi\) gives an action of
\(\mathbb G_m\) on \(U\) for which the inclusion into \(G\) is equivariant.

The pullback gives a closed projection \(W_n\to U\) and identifies its
range with the preimage of \(U(i\circ\xi)\) in \(U\). For an equivariant
closed immersion, the identity-limit functor is the preimage of the
ambient identity-limit functor, by
`AutomorphicAction.IsEquivariant.unipotent_eq_comap_of_isClosedSubgroup`.
This identifies the range of the projection with the identity-limit
functor of the action on \(U\) on every test scheme.

Dynamic smoothness and the closed inclusion in \(G\) make \(U\) smooth
and affine. Apply `AutomorphicAction.splitContractingSubgroup` to the
action on \(U\). This construction supplies a representative of the
identity-limit functor with a finite split series. The isomorphism
between representatives transports connectedness and that series to
\(W_n\), which is affine by its closed inclusion in \(G\).
For the series of length \(d\),
`RelativeRoot.HasSplitSeries.smoothOfRelativeDimension` identifies the
smooth relative dimension. The theorem
`splitUnipotentAffineSpaceStatement` gives the isomorphism of underlying
schemes over \(k\) to \(\mathbb A^d_k\).

The contracting-subgroup construction uses the split-unipotence clause
of the split-torus action result in Milne, *Algebraic Groups* (2017),
Proposition 16.63, printed p. 347 (PDF p. 363). The affine-space step
implements §14.66, printed p. 299 (PDF p. 315), via the successive
one-dimensional additive quotients. The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
