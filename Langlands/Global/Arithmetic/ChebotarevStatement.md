# Finite Galois Chebotarev and Frobenius-trace rigidity

Author: Worker 35. This pair states a concrete arithmetic prerequisite for
the global framework. The assertions are definitions returning `Prop`;
no proofs or theorem-valued assumptions are supplied.

The general rigidity theorem for continuous semisimple representations
of the global Weil group in Henniart 2000, Section 2.2, remains a separate
required statement. Such representations need not factor through a finite
Galois group. This pair does not identify that theorem with the finite
Galois case.

## Prime realization

`Langlands.Global.ChebotarevPrimeRealizationStatement` quantifies number
fields `K : Type u` and `L : Type v`, an algebra structure `K → L`, and
the Galois hypothesis. Every automorphism `σ : L ≃ₐ[K] L` is realized as
an arithmetic Frobenius above some prime of `K` outside an arbitrary
finite set `S`.

Both primes are actual height-one prime ideals of the rings of integers.
The extension of prime ideals is Mathlib's `Ideal.LiesOver`; unramifiedness
is `Algebra.IsUnramifiedAt` at the actual prime of the upper ring.
The Frobenius condition uses the existing
`AlgHom.IsArithFrobAt` applied to `RingOfIntegers.mapAlgHom σ`.
It asserts for every integral `x` that

\[
\sigma(x)-x^{\#(\mathcal O_K/\mathfrak p)}\in\mathfrak q.
\]

In the literal Mathlib definition the exponent uses the contraction of
the upper prime. `LiesOver` identifies it with the selected lower prime.
Thus the convention is the arithmetic, residue-power Frobenius. No
geometric inverse, chosen Frobenius section, abstract place label or
freely supplied residue cardinality is used.

The statement chooses an upper prime as well as the lower prime.
Consequently it can realize the specified automorphism itself, rather
than merely asserting the existence of an unspecified member of its
conjugacy class. This is exactly the choice allowed by the conjugacy-class
form of Chebotarev. The arbitrary finite exceptional set expresses the
infinitude consequence needed for rigidity; the full numerical density
formula is not part of this target.

The finite extension assumption follows from the two number-field
instances and the specified algebra map. There is no restriction on
degree, ramification away from the selected prime, or abelianness.

## Character rigidity

`Langlands.Global.FiniteGaloisFrobeniusRigidityStatement` quantifies two
actual complex representations of `L ≃ₐ[K] L` on independently universed
finite-dimensional vector spaces `V : Type w` and `W : Type z`.
It assumes equality of their characters on every Frobenius described
above every unramified lower prime outside `S`.
The conclusion is `Nonempty (ρ.Equiv τ)`, an actual invertible complex
linear intertwiner.

`Representation.character` is Mathlib's trace of the actual linear
action. There is no free character function, assumed correspondence, or
equality of dimensions supplied as a hypothesis. Equality at the identity
already forces equality of dimensions. For a finite Galois group,
finite-dimensional complex representations are semisimple by Maschke's
theorem; no separate semisimplicity assumption is necessary here.
This reasoning does not extend the assertion to arbitrary coefficient
characteristics or arbitrary infinite-group representations.

The proof obligation is the usual two-step argument: prime realization
gives equality of characters at each group element, and the complex
finite-group character theorem gives an intertwining equivalence.
That argument is documented as provenance, not implemented as a proof
in this statement contribution.

`Langlands.Global.ChebotarevRigidityStatement.{u,v,w,z}` is the conjunction
of the two propositions. All hypotheses are quantified inside its body.

## Exact sources and correspondence

1. Jürgen Neukirch, *Algebraic Number Theory*, English translation by
   Norbert Schappacher, Springer (1999), Chapter VII, Section 13,
   Theorem 13.4, printed pp.545–546 (PDF pp.556–557). The density
   definition and finite-exception observation are on pp.542–543
   (PDF pp.553–554). Worker35 read pp.542–547 in full.
   The theorem gives positive density for every conjugacy class;
   removing a finite set leaves a prime, and the upper prime can be
   chosen to realize the specified automorphism. This explains the
   derived weaker prime-realization target exactly.
   Source `neukirch-1999-algebraic-number-theory`, retained file
   `C:/Central-Library/Neukirch--Algebraic number theory (book)--1999.pdf`,
   SHA256 `4f4406e097cf7cc4bfcc3eb818153d8361c5b0d8f5fb9848053d68d6c6239210`.
   This is the source for the finite Galois prerequisite, not an
   attribution of Henniart's general global-Weil argument.
2. The same book, Chapter VI, Section 7, printed p.406 (PDF p.418),
   fixes arithmetic Frobenius by the residue-power congruence with
   exponent equal to the cardinality of the *lower* residue field.
   The surrounding pp.405–407 were read directly. Chapter I,
   Sections 8–9, pp.49 and 53–58, explain unramified primes,
   decomposition and conjugacy of primes, and the inertia quotient.
   The retained copy's Exercise 2 on p.58 has an apparent misprint,
   defining its congruence exponent as the relative residue degree.
   The Lean convention follows the explicit correct formula on p.406
   and Mathlib's residue-power definition, not that erroneous exponent.
   The p.58 formula and Theorem13.4 page were checked as images.
3. Jean-Pierre Serre, *Linear Representations of Finite Groups*,
   English translation by Leonard L. Scott, GTM42, Springer (1977),
   Part I, Section 2.3, Theorem4 and Corollary2, printed p.16
   (PDF p.25). The corollary says equality of complex characters
   determines a representation up to isomorphism. Sections1.3–1.4,
   Theorems1–2, pp.6–7, justify complete reducibility, and
   Section2.1 p.10 defines the character as trace.
   Worker35 read these passages and the preceding orthogonality
   theorem on p.15 directly.
   Source `serre-1977-linear-representations`, retained file
   `C:/Central-Library/Serre--Linear Representations of Finite Groups--1977.pdf`,
   SHA256 `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.
4. Guy Henniart, *Une preuve simple des conjectures de Langlands pour
   GL(n) sur un corps p-adique* (2000), Section2.2, printed p.444
   (PDF p.6), gives the broader global-Weil uniqueness assertion.
   Source `henniart-2000-simple-proof`,
   SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
   This is contextual provenance for the remaining general rigidity
   target. The current finite Galois pair neither asserts that all
   global Weil representations have finite image nor supplies the
   source's analytic argument.

## Mathlib dependencies and inspection

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version1:
Lean4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The only imports are from this pinned Mathlib, and no project
mathematical dependency is needed.

The existing `RingOfIntegers.mapAlgHom`, `AlgHom.IsArithFrobAt`,
`Representation.character` and `Representation.Equiv` are reused.
The inspected Frobenius file already proves conjugacy and basic
existence for a fixed finite residue extension; it does not supply
the asserted distribution of primes. Mathlib's character file
provides trace, conjugacy invariance and orthogonality; this pair
introduces no replacement representation or character object.
`Ideal.ramificationIdx_eq_one_iff` in the ramification API relates
the unramified predicate to ramification index one when the residue
extension is separable, as it is for the finite residue fields here.
No such general theory is reproved.

Native compilation of the statement module succeeded with no warnings
or errors. All three declarations were printed and their full bodies
inspected. Independent local type checks also confirm that the exact
number-field assumptions give finite relative dimension and a finite
automorphism group. No theorem truth is used in those checks.

Development diagnostic `a2612481-dd21-4137-9a9e-267afdd8dac5` performed
an incremental Lake build and exact entry-declaration inspection:
zero warnings/errors, a `Prop`-returning definition, and universe
parameters `u`, `v`, `w`, `z`. Its checked proposition fingerprint is
`9a4ae269835b85841e7cb4477df70bb7b64961fa7efce4ced94e00726edb26e8`.
The allowed-assumption inspection found only standard Lean assumptions.
This is development evidence, not independent semantic acceptance,
proof acceptance, or current Library publication.
