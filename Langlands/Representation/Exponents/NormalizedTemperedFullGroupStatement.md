# Full-group exponents of normalized-exponent tempered representations

`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedFullGroupExponentStatement`
is a proposition stating the derived normalized-parameter formulation of the
first assertion in Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, VII.2.1, Remark 1, printed p.227/PDF p.233.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This pair states the assertion; it does not prove it.

## Actual meaning and scope

For every connected reductive group scheme `G` over a nonarchimedean local
field `k` in the existing `IsNonarchimedeanLocalField` interface, every smooth
complex representation `π` satisfying the published actual predicate
`IsNormalizedExponentTempered hG π`, and every specified split component
`a : A.toGrp ⟶ G`, the proposition tests the normalized Jacquet exponents for
the identity parabolic map `𝟙 G` and the identity Levi map `𝟙 G`. Witnesses
`hp`, `hl`, and `ha` assert those actual structural properties.

Every represented geometric unipotent radical `r : U ⟶ G` and every witness
that `subgroupMultiplication (𝟙 G) r` is an isomorphism are quantified.
For every character `χ` satisfying the published
`IsNormalizedJacquetExponent` for those maps and witnesses, the conclusion is
both

- `Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0`
  in the full real character space of `A`;
- `‖(χ x : ℂ)‖ = 1` for every actual point `x : rationalPoints A.toGrp`.

The second assertion is the pointwise meaning of unitarity of this character.
The exponent predicate uses the actual normalized Jacquet coinvariant
representation, literal point images and the specified split-component
point map. It includes openness of the character kernel and nonzero
generalized weight space. No additional character-smoothness hypothesis is
introduced by this statement. Neither zero real part nor any empty-root
presentation is assumed.

The canonical rational-point topology is installed explicitly.
The field topology is assumed Hausdorff, and the ambient point group locally
compact and nonarchimedean, as in the published actual exponent interface.
Connected reductivity supplies the affine structure needed by that topology;
the temperedness predicate supplies its finite-type instances internally.
There is no characteristic-zero or split-ambient-group restriction.
The field and group lie in universe `u`; the representation carrier lies in
independent universe `v`. No irreducibility, scalar central character or
finite-dimensional carrier hypothesis occurs.

## Provenance and retained obligations

The source's first assertion in Remark 1 says that normalized exponents
relative to the full group are unitary, equivalently have zero real part.
Here the real part is explicitly the normalized parameter of the published
`SplitTorusRealPart` module. The source's root-combination cone is described
in V.3.14–V.3.15, printed p.113/PDF p.119. Actual normalized Jacquet exponents
are from VII.1.1, printed p.220/PDF p.226, with the normalization of VI.1.2,
printed pp.135–136/PDF pp.141–142.

V.3.20, printed p.116/PDF p.122, first defines the real part through the
exponential based on `q^(-s)` and later writes the raw natural logarithm of
the modulus. In the existing positive-valuation convention the published
parameters satisfy
`rawLogRealPart hA χ = (-Real.log (LocalField.residueCardinality k : ℝ)) • normalizedRealPart hA χ`.
The scalar is negative because `q > 1`. This statement uses the explicitly
normalized temperedness predicate and does not identify the two parameters
or their membership in the same nonnegative root cone. A consistent
corrected-source comparison for V.3.20 and VII.2.1 remains separate.

The proof must establish the full-group root-cone degeneration and the
unitarity conclusion from the actual definitions. Those facts are conclusions
to prove, rather than premises of this proposition. The scalar-central-character
consequence on the full center in the second sentence of Remark 1, the
Casselman implication in Remark 2, standard reduction in Remark 3 and later
induction and classification results are separate obligations.
