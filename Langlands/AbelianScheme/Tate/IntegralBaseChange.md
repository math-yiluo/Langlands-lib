# Base change of actual integral Tate modules

For a scheme morphism `b : S' ⟶ S`, a commutative group scheme `G` over
`S`, and a test scheme `T` over `S'`, this module constructs the canonical
comparison

```text
Integral (b*G) T P ≃ Integral G (T → S' → S) P.
```

Here `P` selects positive torsion orders. The equivalence uses the actual
pullback group scheme and actual torsion points. It is a continuous linear
equivalence over the existing full profinite-integer ring. For the orders
coprime to any natural modulus `m`, it is also a continuous linear equivalence
over the existing prime-to-`m` profinite-integer ring. The module includes the
bundled abelian-scheme specialization and its pointed full and away versions.

## Provenance

This is a derived construction from the published `TorsionBaseChange`,
`Tate.Integral`, `Tate.Scalars`, and `Tate.TestScheme` modules.
`baseChangeTorsionPointsEquiv` restricts the actual pullback-adjunction
equivalence on sections to the kernel of integer multiplication. Applying
this fixed comparison coordinatewise produces the present limit comparison;
no comparison isomorphism is supplied by the caller.

The motivating Tate conventions are Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), printed p.18 / PDF p.26:
the full limit uses all positive orders, and the away limit uses coprime
orders. Section III.1, printed p.91 / PDF p.99, formulates the PEL problem
on pointed schemes. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary build
2012-02-08, Chapter X (10.30), printed p.151 / PDF p.155, describes pullback
of finite étale covers and the induced pointed fundamental-group map.
Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
That paragraph motivates the eventual monodromy compatibility; this module
only constructs the underlying Tate-module comparison. Its elementary
pullback proof works under the weaker hypotheses stated below and does not
invoke the source's Galois-category theorem.

## Finite coordinates and the limit

In namespace `Langlands.GroupScheme.Tate`, `levelBaseChange b G T n` is
`baseChangeTorsionPointsEquiv b G (n : ℤ) T` in additive notation. Thus its
forward map sends an actual section of `b*G` to its composite with the first
pullback projection. `toSection_levelBaseChange` exposes this point formula
through `baseChangePointsEquiv`. The torsion kernel used by `Level` is
definitionally the same kernel used by this published equivalence.

`levelBaseChange_transition` proves that this comparison commutes with
multiplication by `m / n` when `n ∣ m`. After forgetting the torsion subtype,
this is preservation of powers by the multiplicative point equivalence.
`levelBaseChange_symm_transition` follows by applying the forward equivalence
and cancelling its inverse.

`integralBaseChange` applies the finite equivalence to each selected
coordinate. The two transition lemmas prove coherence of the forward and
inverse families. Coordinatewise inverse identities and additivity give the
additive equivalence. `evaluation_integralBaseChange` and
`evaluation_integralBaseChange_symm` state its coordinate formulas.

Each finite level has the existing discrete topology, and the integral
limit has the existing product-subspace topology. Both continuity lemmas
compose a continuous evaluation with a map between discrete levels, then
use continuity into the product and subtype. They prove continuity without
claiming compactness or finite cardinality of those levels.

`integralBaseChange_smul` proves full residue scalar compatibility
coordinatewise: an additive map between groups killed by `n` respects their
canonical `ZMod n` actions. `integralBaseChangeLinearEquiv` bundles the
result with continuity in both directions. The same argument with
`awayReduction` proves `integralBaseChange_away_smul`, and
`awayBaseChangeLinearEquiv` bundles the prime-to-modulus version.
`integralBaseChange_restrictAway` says that retaining only the coprime
coordinates commutes with base change; both sides are definitionally the
same coherent family.

## Naturality and abelian schemes

`levelBaseChange_testRestrict` and `integralBaseChange_testRestrict`
compare restriction along a map `a : T' ⟶ T` over `S'` with restriction along
`(Over.map b).map a` over `S`. Their proofs use the naturality of the actual
pullback point equivalence, then coordinatewise extensionality.

`levelBaseChange_map` and `integralBaseChange_map` compare the pullback of
an actual group-scheme homomorphism `f : G ⟶ H` with `f` over the original
base. The finite square is `baseChangePointsEquiv_comp`; coordinatewise
extensionality gives the integral square.

In namespace `Langlands.AbelianScheme.Tate`, `integralBaseChange` and
`awayBaseChange` specialize these continuous linear equivalences to the
actual abelian scheme `(AbelianScheme.baseChange b).obj A`.
`integralBaseChange_map` specializes the naturality square to actual
abelian-scheme homomorphisms.

For a field-valued point `t : Spec Ω ⟶ S'`, `fullBaseChangeAt` gives

```text
T(b*A)_t ≃L[ProfiniteIntegerRing] TA_(t ≫ b),
```

and `awayBaseChangeAt` gives the corresponding away equivalence. These are
specializations at `T = Over.mk t`; the composite point is the actual
scheme composite. Taking an algebraically closed `Ω` gives the geometric
point application. No change of coefficient field is asserted.

## Scope

All schemes and coefficient fields in the pointed specialization use the
same universe. No connectedness, local noetherianity, finiteness, étaleness,
order invertibility, or algebraic closure is needed for these comparisons.
The generic construction requires a commutative group object; the final
specialization uses the published bundled abelian-scheme pullback.

This unit does not prove identity or composition coherence as the base
morphism varies, compatibility with fundamental-group maps, rational or
adelic scalar extension, or any Weil-pairing restriction. Those are separate
steps toward the pointed PEL functor. In particular, this module does not
claim a complete base-change operation on invariant level orbits.
