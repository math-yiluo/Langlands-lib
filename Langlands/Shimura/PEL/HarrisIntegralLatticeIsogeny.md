# Carried Harris lattices under rational isogeny

Author: Worker 344.

This internal construction restricts the actual rational Tate isomorphism to
the submodules carried by an original Harris level and its original polarized
rational-isogeny transport. It proves that normalization of the transported
level is equivalent to exact realization of the starting submodule by the
inverse Tate map on the full integral Tate group.

## Inputs and conventions

The arithmetic carriers, scheme and point field have universe zero. The
inputs are the existing totally real number field `E`, totally complex
quadratic extension `F`, central simple unitary datum `D` on `A`, and Harris
signature charts `C` for any embedding section permitted by their type. The
displayed algebra and scalar towers are retained. No division or CM-section
hypothesis is added.

`P : Prerequisites` supplies the named tensor, Picard, duality and polarization
inputs of `PositivePolarizedAction`. The scheme `S` is quasi-separated, and
`s : Spec Ω ⟶ S` is a supplied point for an arbitrary field. The relative
finite Weil-transition statement, rational profinite-integer/finite-adele
comparison `h`, and `PositivePairAdditivity` are explicit inputs. The frames
and the positive polarized objects use the unchanged positive auxiliary
involution `auxiliaryStarRing D C` and the existing Harris Hodge PEL form.

Let `Af = Global.FiniteAdeles ℚ` and
`Rf = Global.integralFiniteAdeles ℚ`. The actual rational Tate carrier uses
the predicate `fun _ => True`, retaining every positive torsion index. Its
`Rf`-module is restriction of the actual `Af`-module along the subring
inclusion. The source span is the unchanged
`D.harrisHodgePELIntegralAdeleSpan C` in `Af ⊗[ℚ] A`.

The supplied `e : X.actionObj ≅ Y.actionObj` is an isomorphism in the
existing rational algebra-action category. Its underlying rational
abelian-scheme isomorphism intertwines the original algebra actions. A unit
`q : ℚˣ` and `he : PolarizedWeilLevel.Multiple ... X Y q e` supply the
original geometric rational dual-pullback multiplier condition. This is
the condition used by the existing Weil-frame and fixed-level transports.
Rational Weil functoriality is supplied by its published proof
`rationalWeilFunctoriality`.

## Frame images and original fixed levels

Write `r` for `Tate.rationalIso ... (RationalAlgebraAction.underlyingIso e)`.
Its function is exactly `Tate.rationalHomMap ... e.hom` on the underlying
rational abelian schemes; its inverse is the corresponding map of `e.inv`.
The existing `Tate.weilAdelicFrameIsogeny` sends a compatible frame `eta`
to the frame whose value at `v` is `r (eta v)`.

`harrisIntegralFrameLattice_isogeny` proves

```text
r w ∈ harrisIntegralFrameLattice Y (transported eta)
  ↔ w ∈ harrisIntegralFrameLattice X eta.
```

Both submodules are the literal images of the same original source span.
The proof expands their image-membership formulas. A witness for the
transported image gives a witness for the original image by injectivity of
`r`; the converse uses the same source vector. No integral preservation
property of the rational isogeny is assumed.

The fixed-level declarations additionally retain the finite-fibre hypothesis
`hs` for all finite-etale covers at `s`, the torsion finite-etale statement,
invertibility on `S` of every positive index, and the displayed finite and
etale roots-of-unity instances. They use the existing
`PolarizedWeilLevel.levelTower` and `PolarizedWeilLevel.levelIso`.
`x` is an element of the original monodromy-fixed right-orbit level. The
level subgroup must satisfy
`K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C`.

`harrisIntegralLevelLattice_isogeny` proves the same membership equivalence
for `harrisIntegralLevelLattice X K hK x` and the submodule of
`levelIso ... e he x`. The proof takes a representative `eta` of the
original orbit. The published frame transport commutes with the original
opposite-group right action, whose value is source precomposition. Thus
its image represents the transported orbit. The representative-evaluation
formula for the carried submodule reduces the result to the frame theorem.
The proof uses the fixed level's underlying orbit; it assumes no fixed
representative.

## Restricted isomorphism and normalization criterion

`harrisIntegralLevelLatticeIsogenyEquiv` restricts `r` to an
`Rf`-linear equivalence between those two carried submodules. The membership
equivalence supplies both restrictions. The inverse identities and
additivity follow from `r`, and `Rf`-linearity follows by restricting the
actual finite-adelic linearity of `Tate.finiteAdeleHomMap`.
`harrisIntegralLevelLatticeIsogenyEquiv_apply` records by reflexivity that
inclusion of its value into the rational target is the original rational
Tate homomorphism map.

`harrisIntegralLevelCondition_isogeny_iff` proves that the existing
`HarrisIntegralLevelCondition` on the transported original level is
equivalent to the following exact criterion, for every rational Tate vector
`w` of `X`:

```text
w ∈ harrisIntegralLevelLattice X K hK x
  ↔ ∃ b : FullIntegralTate(Y), r.symm (toRational b) = w.
```

Here `FullIntegralTate(Y)` denotes the actual
`GroupScheme.Tate.Full Y.actionObj.abelianScheme.toGrp (Over.mk s)`.
The conclusion uses the actual full rationalization map with all positive
indices; it neither substitutes an away Tate group nor picks an auxiliary
integral image.

The proof first uses the published criterion that normalization is equality
of the transported level's carried submodule and the full integral
rationalization image. The level membership equivalence transfers this
equality through `r`. Its inverse identities identify image witnesses with
the displayed inverse-image witnesses. Conversely, surjectivity of `r`
reduces equality of subsets of the target rational Tate space to those
same witness equivalences. No injectivity of integral rationalization is
needed.

## Provenance and remaining obligations

The provenance is internal. The construction derives restriction and image
identities from the published original frame transport, original fixed-level
transport, carried-submodule definitions and full integral-image
normalization criterion. It introduces no new external-source assertion and
does not modify those inputs.

All objects and the rational polarized isomorphism are supplied. This unit
does not construct an isogenous abelian scheme, integral algebra action,
polarization, determinant-condition model or normalized representative.
It gives a criterion to apply after exact lattice realization and compatible
geometric structures have been established. Those existence results, integral
reflection, the complete natural normalized moduli comparison, a representing
scheme, its admissibility, smoothness and division-case projectivity remain
separate obligations. The host's `DivisionCMRepresentabilityStatement`
remains open.
