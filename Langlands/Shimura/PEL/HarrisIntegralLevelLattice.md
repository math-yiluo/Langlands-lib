# The integral submodule carried by an original Harris level orbit

Author: Worker 344.

This internal construction attaches an integral finite-adele submodule of the
actual rational Tate space to an original Harris compatible-frame orbit at a
level that preserves the existing integral source span. For a geometrically
fixed orbit it proves invariance under actual rational Tate monodromy. It also
identifies the existing normalization predicate with equality of the carried
submodule and the full integral Tate rationalization image.

The declarations use `Lattice` in their names for this carried submodule. This
file does not prove finite generation, freeness, compactness, openness, or
realization by an abelian scheme.

## Inputs and conventions

The arithmetic carriers, base schemes and point fields have universe zero.
The inputs retain the existing totally real number field `E`, totally complex
quadratic extension `F`, central simple unitary data `D` on `A`, Harris
signature charts `C`, and displayed algebra and scalar-tower instances. The
charts may use any section `Φ` of complex embeddings allowed by their type;
this unit imposes no CM-section specialization or division hypothesis.

`P : Prerequisites` supplies the named tensor, Picard, duality and polarization
prerequisites used by `PositivePolarizedAction`. The base scheme `S` is
quasi-separated. A point `s : Spec Ω ⟶ S` is supplied for an arbitrary field
`Ω`; algebraic closedness, connectedness and local noetherianity are not
required here. The relative finite Weil-transition statement and the rational
profinite-integer/finite-adele comparison `h` are explicit inputs.

Every compatible frame uses the unchanged positive auxiliary involution
`auxiliaryStarRing D C`, the actual rational action of the positive polarized
object `X`, and the existing Harris Hodge PEL form. Write `Af` for the actual
ring `Global.FiniteAdeles ℚ`, `Rf` for its subring
`Global.integralFiniteAdeles ℚ`, and `Vf = Af ⊗[ℚ] A`. The source submodule
`Λf` is exactly `D.harrisHodgePELIntegralAdeleSpan C` from
`HarrisIntegralTateImages`: it is the `Rf`-span of the tensors `1 ⊗ x` for
members of the existing integer Harris pairing lattice. This construction
retains that source rather than selecting a different lattice.

## The transported submodule and its orbit descent

The private `source_scalar` and `target_scalar` lemmas identify the action of
`1 ⊗ a` in the tensor algebra `A ⊗[ℚ] Af` with the actual `Af` scalar action
on the source and rational Tate target. The source identity follows by tensor
induction and the existing tensor-algebra module formula. The target identity
uses the actual rational-endomorphism and finite-adele actions and the fact
that the algebra action sends one to the identity. Specializing a compatible
frame's tensor-algebra linearity to `1 ⊗ a` therefore gives its `Rf`-linear
underlying map. The target `Rf`-module is restriction of its existing actual
finite-adelic module along the subring inclusion.

`harrisIntegralFrameLattice X eta` is the `Submodule.map` image of `Λf`
under that map. `mem_harrisIntegralFrameLattice` states literally that a target
vector belongs exactly when it is `eta v` for some `v ∈ Λf`.
`harrisIntegralFrameLattice_apply_mem` uses frame injectivity to recover source
membership at `eta v`.

`harrisIntegralFrameLattice_right` proves that the original right action by a
member of `harrisIntegralAdeleStabilizer D C` leaves this image unchanged.
The right action is the existing opposite-group action and evaluates as
`eta (g v)`. The forward inclusion uses preservation of `Λf` by `g`; the
reverse inclusion uses `g`'s inverse linear equivalence and the stabilizer's
membership equivalence. No representative is assumed to be fixed.

`harrisIntegralFrameLattice_of_orbit_eq` applies the existing
`RightOrbit.mk_eq_mk` to equal original right orbits. If
`U ≤ harrisIntegralAdeleStabilizer D C`, the resulting right translate has the
same image. `harrisIntegralOrbitLattice X U hU` is consequently defined by
`Quotient.lift` on the original `RightOrbit` type. Its value on an original
representative is the frame submodule by reflexivity, as recorded in
`harrisIntegralOrbitLattice_mk`. This definition makes no new choice of frame.

## Original fixed levels and actual monodromy

The fixed-level declarations additionally take the existing finite-fibre
hypothesis `hs` for every finite-etale cover at `s`, the torsion finite-etale
statement, invertibility of every positive index on `S`, and the displayed
finiteness and etaleness instances for every corresponding roots-of-unity
scheme. They use the existing `PolarizedWeilLevel.levelTower` on finite-adelic
scalar-extension levels, with its unchanged actual Weil-compatible frames and
geometrically fixed right orbits. The actual monodromy action uses the
published `rationalWeilGeometricTransport` proof.

For a level `K` whose subgroup is contained in the source integral stabilizer,
`harrisIntegralLevelLattice X K hK x` evaluates the descended submodule at the
underlying orbit of the existing fixed level `x`.
`harrisIntegralLevelLattice_eq_frame` identifies it with the image under any
representative of that same orbit.

`harrisIntegralLevelLattice_monodromy` proves, for every
`gamma : FundamentalGroup s hs` and every vector `w` in the actual rational
Tate space, the equivalence

`rationalMonodromy gamma w ∈ harrisIntegralLevelLattice X K hK x ↔
w ∈ harrisIntegralLevelLattice X K hK x`.

The proof takes a representative `eta` of the given quotient and uses
`RightOrbit.mk_mem_fixedPoints` to obtain a member `g ∈ K` with
`gamma • eta = right eta g`. Evaluation at a source vector gives the actual
rational Tate monodromy value `eta (g v)`. Frame surjectivity reduces arbitrary
`w` to `eta v`; the carried-submodule membership formula and the integral
stabilizer equivalence then give both implications. Orbit fixedness is used
exactly here; fixedness of the frame itself is neither assumed nor concluded.

## Full integral image and remaining obligations

`harrisIntegralFrameCondition_iff_lattice` identifies the existing frame
normalization predicate with equality, as subsets of the rational Tate
carrier, between the carried submodule and
`Set.range (GroupScheme.Tate.toRational ... (fun _ => True))`. This is the full
actual integral Tate group, with every positive torsion index retained. Frame
surjectivity turns the original predicate on source vectors into equality on
all target vectors; the reverse direction evaluates the equality at `eta v`.

`harrisIntegralLevelCondition_iff_lattice` gives the same equality criterion
for the existing existential normalization predicate on an original fixed
level. Its forward direction uses the supplied normalized representative and
its orbit equation. Its reverse direction takes any representative of the
orbit and uses representative independence plus the frame equality criterion.
It assumes neither injectivity of rationalization nor existence of a
normalized model.

The provenance is internal: the unit derives image constructions and their
laws from the published source span, compatible frames, opposite right
action, original quotient and actual monodromy formulas. It imports these
mathematical objects by Lean name and invokes no external existence result.
No new literature assertion is introduced. The construction is an input for
the normalization route in the division representability task. Lattice
realization, normalized-model existence, integral reflection of rational
isogenies, the complete natural moduli comparison, representing schemes,
admissibility, smoothness and projectivity remain separate obligations. The
exact `DivisionCMRepresentabilityStatement` is not proved by this unit.
