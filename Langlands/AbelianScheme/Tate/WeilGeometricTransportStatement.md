# Geometric transport of the actual rational Weil pairing

`Langlands.AbelianScheme.RationalWeilGeometricTransportStatement` is a
proposition specifying compatibility of the constructed relative rational
Weil pairing with the constructed geometric path maps. It is a statement,
not a proof of this compatibility.

The sources motivating this derived relative formulation are Kottwitz,
*Points on some Shimura varieties over finite fields* (1992), Section 5,
pp.390–391, and Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, XI (11.23), printed p.168 (PDF p.172).
The latter describes the inverse-limit pairing into the actual Tate twist
and its Galois equivariance. Kottwitz uses the monodromy action on the
polarized Tate module together with its Tate-twist value line in defining
invariant level orbits. These sources are registered as
`kottwitz-1992-points-shimura-finite-fields` and
`edixhoven-vandergeer-moonen-abelian-varieties-draft`.
The arbitrary-path, relative and arbitrary-selected-order formulation here
is a derived compatibility obligation for the Library's concrete
constructions; the cited field-level discussion alone does not prove it.

Fix a quasi-separated base `S`, an actual abelian scheme `A/S`, and its
dual-scheme geometry, Poincaré evaluation and pullback/Picard coherence
inputs. The finite Weil transition proposition is explicit. Let `s` and
`t` be field-valued points of `S`, with finite fibres for the actual finite
étale cover categories, and let `p` be an isomorphism of their fibre
functors. Geometric points are the intended application; the statement
only needs the displayed field and finite-fibre assumptions and a given
path.

For a predicate `P` on positive torsion orders, assume the published
torsion-finite-étaleness statement and invertibility on `S` of all selected
orders. Also retain finite étaleness of the selected root-of-unity schemes
as explicit hypotheses. No full-order invertibility is imposed when `P`
selects only orders coprime to a modulus.

Writing `τ_A` and `τ_DA` for the actual rational Tate path maps and `τ_1`
for the actual section-ring twist transport, the two conclusions are

`τ_1(e_s(x,y)) = e_t(τ_A(x), τ_DA(y))`

and, for every actual dual-valued homomorphism `lam : A → DA`,

`τ_1(e_s^lam(x,y)) = e_t^lam(τ_A(x), τ_A(y))`.

Here the first form is `rationalWeilBilinearMap`, constructed from the
actual finite Weil evaluation pairing. The second is
`rationalWeilAlongHomBilinearMap`, with `lam` applied in the second variable.
The second clause requires no polarization predicate; it also applies to
an actual polarization when one is supplied.

The value maps use `TateTwist.Geometry.sectionRationalTransport`. This map
compares the twist over `Γ(Spec Ω, ⊤)` with the twist over `Ω` through the
canonical `ΓSpecIso`, applies the existing geometric root transport, and
returns through the inverse comparison at the other endpoint.
Consequently the equality is in the actual section-ring twist at `t`;
there is no chosen basis of either twist and no scalar-valued replacement
of the pairing.

The statement retains `P` universally, so it specializes both to all
positive orders and to every coprime-order system. It concerns the rational
carriers; the existing full and away adelic pairings and twist transports
have these same values with their respective constructed scalar actions.
Taking a loop gives the monodromy compatibility needed to preserve the
Weil-compatible frame spaces. The proposition does not assert that a path
exists or is unique, that any frame exists, or that the pairing is
alternating or nondegenerate.

A proof must establish compatibility for the actual relative pairing, for
example by applying naturality of the geometric fibre functor to the
finite pairing morphism and its product inputs, then passing through the
inverse limit and rationalization. The pulled-back clause must also use
naturality of the actual homomorphism-induced Tate maps. It may not assume
pairing compatibility as additional input or replace the constructed form,
root action or path maps by arbitrary equivariant data.
