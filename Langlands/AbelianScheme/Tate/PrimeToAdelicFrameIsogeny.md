# Rational-isogeny transport of actual prime-to-modulus adelic Tate-frame orbits

This module transports the published actual prime-to-modulus adelic Tate frames and their
geometrically fixed right-orbit classes along rational isogenies intertwining
rational endomorphism actions. It proves identity, composition, inverse, level
change, and geometric path compatibility. These are ambient linear frames;
no polarization or Weil-pairing condition is imposed.

## Source and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines an isogeny of abelian schemes as an
invertible element of `Hom(A,B) ⊗_Z Q`. Section III.1, printed p.91 / PDF p.99,
identifies PEL data using isogenies transporting the endomorphism actions and
level orbits. The same page specifies right translation by precomposition and
canonical independence of the geometric point for the moduli problem. Printed
p.92 / PDF p.100 introduces the prime-to-p invariant right-orbit level. The
arbitrary modulus used here generalizes that prime-to-p construction.
Registered source: `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This is a derived intermediate implementation of the level-transport part.
The source's additional polarization and pairing requirements remain separate.
The proofs reuse the constructed rational Tate functor, its actual monodromy
and path naturality, the tensor-algebra-linear isogeny maps, and the generic
fixed-orbit descent. Arbitrary rational algebra and source representation are
explicit generalizations used to isolate this reusable construction.

## Objects and assumptions

Let `A`, `B`, and `C` be abelian schemes over a scheme `S`. Let `D` be a
possibly noncommutative ring with a rational algebra structure, with rational
endomorphism actions `iA`, `iB`, and `iC`. Fix any natural modulus `m` and set
`R = D ⊗[Q] Global.PrimeToFiniteAdeles m`. The source `V` is any `R`-module with an
additive commutative group, and `rho : G →* (V ≃ₗ[R] V)` is any representation
of a group `G`. No nonemptiness of the frame space is asserted.

Fix a field-valued point `s : Spec Ω ⟶ S`. The target of a frame is the actual
`RationalAway A (Over.mk s) m`, the rational scalar extension of the compatible
families of actual torsion points at positive orders coprime to `m`.
`PrimeToAdelicFrame` uses the constructed action `primeToFiniteAdeleAlgebraModule`,
with the same coupled scalar-comparison hypotheses
`h : Global.RationalProfiniteIntegerAdeleComparison` and
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m` at every
object and point. Neither the truth of these comparisons nor independence from
their chosen witnesses is proved here. The field-valued points need not have the same coefficient
field, but both coefficient fields and schemes lie in universe `u`.

The isogeny is `e : Rationalization.of A ≅ Rationalization.of B`. Its
intertwining hypothesis `he` states, for every `d : D`,

\[
e\circ i_A(d)=i_B(d)\circ e.
\]

This is an equality of rational homomorphisms. In Lean,
`Rationalization.comp A B C f g` means first `f`, then `g`. There is no
assumption that `e.hom` is an integral homomorphism.

Frame transport alone needs no finite étaleness or invertibility of torsion
orders. Fixed orbits additionally retain a finite-fibre proof
`hs : ∀ Y : Cover S, Finite (Fiber s Y)`, the explicit proposition
`TorsionFiniteEtaleStatement`, and invertibility on `S` of the positive
torsion orders coprime to `m`. The full scalar-comparison input `h` imposes no
invertibility condition on omitted torsion orders. The acting group is the actual
`FundamentalGroup s hs`, the automorphism group of the finite geometric-fibre
functor, with its published Tate action. The intended application is to
geometric points of connected locally noetherian schemes where the selected orders are invertible;
the conditional API requires only the listed inputs.

## Construction and algebraic laws

`primeToAdelicFrameIsogeny m hAway iA iB V s e he` postcomposes a frame with
`primeToFiniteAdeleAlgebraIso (Over.mk s) hAway iA iB e he`. Thus

\[
\eta\longmapsto V(e)\circ\eta,
\qquad V(e)=\operatorname{rationalHomMap}_{(n,m)=1}(e.\mathrm{hom}).
\]

`primeToAdelicFrameIsogeny_apply` gives this formula. The equivalence's inverse
postcomposes with the map of `e.inv`.
`primeToAdelicFrameIsogeny_refl`, `primeToAdelicFrameIsogeny_trans`, and
`primeToAdelicFrameIsogeny_symm` prove identity, composition, and inversion. For
`e : A ≅ B` followed by `f : B ≅ C`, transport along `e.trans f` equals first
transport by `e` then by `f`. The proofs evaluate frames on vectors and apply
the existing rational Hom identity/composition laws; inversion is definitional.
The composed and inverse intertwining hypotheses are supplied by the published
`rationalIntertwines_comp` and `rationalIntertwines_inverse`.

`primeToAdelicFrameOrbitIsogeny` descends this equivalence to
`PrimeToAdelicFrameOrbit A ... U ≃ PrimeToAdelicFrameOrbit B ... U`. These are fixed classes
of the quotient by right precomposition with `U`, not classes represented by
fixed frames. The right-equivariance equation is associativity of evaluation.
Left equivariance follows from `rationalMonodromy_iso`: actual monodromy on
`B` commutes with the rational Tate map from `A`. Both sides use the same
fundamental group at `s`; the group equivalence supplied to
`InvariantOrbit.equiv` is its identity.

`primeToAdelicFrameOrbitIsogeny_refl`, `primeToAdelicFrameOrbitIsogeny_trans`, and
`primeToAdelicFrameOrbitIsogeny_symm` establish the corresponding laws on the full
orbit equivalences. Equivalence extensionality, subtype extensionality and
quotient induction reduce these equations to the frame laws above. No choice
of a representative of a fixed class is used.

## Level and path compatibility

For subgroups `U`, `U'` and `g : G` with
`∀ u ∈ U, g⁻¹ * u * g ∈ U'`, `primeToAdelicFrameOrbitIsogeny_translate` proves that
isogeny transport commutes with the existing right translation from level `U`
to level `U'`. Translation sends a representative `eta` to `eta ∘ rho(g)`.
The proof specializes `InvariantOrbit.map_translate` using the same right
and left equivariance equations. `primeToAdelicFrameOrbitIsogeny_forget` specializes
this square to `g = 1` and `U ≤ U'`.

Given a second point `t`, its finite-fibre proof `ht`, and a supplied natural
isomorphism `p : fiberFunctor s hs ≅ fiberFunctor t ht`,
`primeToAdelicFrameIsogeny_transport` proves

\[
V_B(p)\circ V_s(e)\circ\eta
  =V_t(e)\circ V_A(p)\circ\eta.
\]

It is frame extensionality applied to `rationalTransport_iso`.
`primeToAdelicFrameOrbitIsogeny_transport` descends the same square to fixed orbit
classes by subtype extensionality and quotient induction. Together with the
imported path-independence theorem, this gives compatibility of isogeny
transport with the path-independent fixed-orbit maps whenever such a path is
supplied. It does not establish existence of a path.

The unit makes no assertion about preservation of a Weil form or its
similitude multiplier, Tate-twist trivializations, topology of the frame
spaces, pointed base change of the base scheme, or a completed unpointed PEL
moduli functor. Those remain separate constructions. This API allows all invertible rational
homomorphisms on the away rational carrier. It does not define the narrower
prime-to-p-isogeny relation using `Hom ⊗ Z_(p)` on integral geometric data. For
a prime modulus `m = p`, it gives the rational level-transport construction
used by the prime-to-p variant; no primality is needed for the general laws.
