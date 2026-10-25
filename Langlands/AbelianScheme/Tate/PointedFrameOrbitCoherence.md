# Coherence for pointed pullback of fixed Tate-frame orbits

This internal unit proves identity and binary composition coherence for the
actual pointed pullback maps on monodromy-fixed full and prime-to-modulus
Tate-frame orbit classes. It combines `PointedFrameOrbitPullback`,
`FixedFrameOrbitComparisons` and the unrestricted right-orbit coherence already
proved in `AdelicFrameOrbitCoherence`. No external theorem is being transcribed.

## Equality of point maps

`adelicFrameOrbitPointEq` transports fixed orbit classes along an equality
`s = t` of field-valued points of a fixed base. Its two finite-fibre witnesses
remain explicit; after substitution the equivalence is the identity. It uses
the same abelian scheme, rational algebra action, scalar comparison, source
module, representation, torsion finite-etaleness hypothesis and unit hypotheses
at both endpoints.

The lemma `adelicFrameOrbitPointEq_val` identifies this equivalence's underlying
map with the existing `adelicFrameRightOrbitTestIso` for any supplied
`e : Over.mk s ≅ Over.mk t` whose underlying forward morphism of point schemes
is the identity. To prove this, substitute the point equality, identify `e`
with the identity isomorphism by extensionality in the over category, and use
the published identity law for unrestricted orbit transport. The
`_symm_val` lemma gives the inverse identification by injectivity. Thus these
lemmas relate equality transport to actual test-scheme restriction maps.

## Identity pullback

`adelicFrameOrbitPullback_id` starts with a fixed class at `s ≫ 𝟙 S`. It states
that pointed pullback along `𝟙 S`, followed by the actual identity
abelian-scheme comparison `adelicFrameOrbitBaseChangeId`, equals
`adelicFrameOrbitPointEq` along `Category.comp_id s`.

The identity comparison runs from frames for the pulled-back abelian scheme
at `s` to frames for the original scheme at `s`. The equality transport uses
`(Over.mapId S).app (Over.mk s)`, whose underlying point-scheme morphism is the
identity. The proof passes to the underlying right-orbit classes by subtype
extensionality, uses the projection formulas, and applies the existing
`adelicFrameRightOrbitBaseChange_id` to the inverse base-change image of the
original class.

## Binary composition

For `b : S' ⟶ S`, `c : S'' ⟶ S'` and a point `s` of `S''`,
`adelicFrameOrbitPullback_comp` starts with a fixed class of `A` at
`(s ≫ c) ≫ b`. Its two outputs lie in the fixed orbit set for the successive
pullback of `A`, evaluated at `s`:

- First transport the class to `s ≫ (c ≫ b)` by the inverse equality
  transport, pull back directly along `c ≫ b`, and apply the actual
  direct-to-successive comparison `adelicFrameOrbitBaseChangeComp`.
- First pull back along `b` at the point `s ≫ c`, then along `c` at `s`.

The equality transport in the first route is the inverse of transport along
`(Category.assoc s c b).symm`. Its forward underlying right-orbit equivalence
is precisely the test-isomorphism comparison
`(Over.mapComp c b).app (Over.mk s)`. The direct-to-successive comparison and
both successive rational algebra actions are those of the actual
abelian-scheme base-change constructions.

After subtype extensionality and the projection identities, the proof is an
inversion of the already established unrestricted coherence square. The private
`inverse_square` lemma expresses the elementary equivalence calculation:
if `f (g z) = t (d (c.symm z))`, then
`c (d.symm (t.symm x)) = g.symm (f.symm x)`. It is proved by applying the
injective equivalences and cancelling each inverse. Its specialization here
uses `adelicFrameRightOrbitBaseChange_base_comp`.

## Hypotheses and prime-to-modulus version

The named proposition `RationalMonodromyBaseChange` remains an explicit
hypothesis of both coherence laws because it is required to define pointed
pullback on fixed sets. Finite-fibre witnesses are explicit at every point,
including the two associations of the composite point. The named torsion
finite-etaleness hypothesis is retained. For composition, all retained positive
orders must be units on each of `S`, `S'` and `S''`; for identity only the common
base is involved.

The `primeToAdelic` declarations give the same constructions and laws for every
`m : ℕ`, with the actual prime-to-modulus Tate frames and
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m` coefficients. They retain one common full
comparison `h` and one coupled `hAway` throughout. Selected orders satisfy
`Nat.Coprime n m`, and unit hypotheses apply only to these orders. No primality
assumption on `m`, algebraic closedness, connectedness or local noetherianness is
added to this conditional API.

These results concern ambient tensor-linear frame orbits. They establish the
stated pointed identity and binary composition laws with actual comparisons;
they do not impose Weil-pairing compatibility, discharge the named monodromy
hypothesis, prove path existence, or construct an unpointed PEL moduli functor.
