# Irreducible images up to sign under the actual Aubert operator

Author: Worker 320.

`Langlands.Aubert.IrreducibleImageStatement.{uF,uV} F T` is the proposition
that every actual irreducible smooth complex representation `π` of `GL_n(F)`
has an actual irreducible smooth representation `πD` of the same group with

```text
alternatingOperator F T n [π] = [πD]
  or
alternatingOperator F T n [π] = -[πD].
```

The brackets denote classes in the exact finite-length smooth Grothendieck
group. The proposition existentially quantifies the representation and its
irreducibility proof. It does not choose a duality functor, representation,
sign or isomorphism class. This module contains no proof of the proposition.

## Actual objects, signs and scope

Outer parameters are arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and supplied `T : F.TopologicalData`. The proposition
installs the supplied topology. Field universe `uF` and representation-carrier
parameter `uV` are independent, and both actual smooth representations have
carriers in `Type (max uF uV)`. No smaller universe is required for the output.

The input hypothesis is exactly `Representation.IsIrreducible π.representation`.
The existing generic theorem `SmoothRep.hasFiniteLength_of_isIrreducible`
supplies the finite group-algebra length of both objects. There is no
admissibility, central-character, finite vector-space dimension, cuspidality,
segment-support, positive-rank or extra theorem-valued premise.

The group is `GeneralLinear.FiniteLengthGrothendieckGroup.{uV,uF} n F.Carrier`.
It is the quotient using relations of all actual short exact sequences,
including nonsplit ones. The actual irreducible output is required before its
class is formed; a formal label, virtual element or arbitrary finite-length
output does not suffice.

The imported operator is unadjusted: it sums actual normalized induction after
Jacquet restriction over all ordered positive block shapes `B` with coefficient
`(-1 : ℤ)^(n - B.length)`. Its induction convention is upper block parabolic,
positive half-modulus covariance and right translation; Jacquet restriction
uses upper-unipotent coinvariants and inverse half-modulus action. No
cuspidal-support-dependent sign is added. The disjunction expresses precisely
preservation of irreducibility up to sign. The sign is not asserted to be
positive or independent of the support, and no segment socle-to-special-quotient
identity is included.

Every natural rank `n` is included. The source's positive-rank `GL_n` case is
extended to the trivial rank-zero group, where there is one empty shape with
coefficient `1`. Verifying that its actual induction-Jacquet term is the
identity is part of the future proof, rather than a result in this module.

## Original assertions and corrected proof boundary

The first original assertion is Anne-Marie Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie d'un
groupe réductif p-adique*, Transactions of the American Mathematical Society
347 (1995), 2179–2189, Corollary 3.9(a,b), printed p.2189 (one-based PDF p.11).
Registered ID: `aubert-1995-duality`; PDF SHA-256:
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
This page was reread as text and a rendered image for this module. Its class
formula is `D_G([E]) = (-1)^|I| [E#]`, and its second clause says that `E#` is
irreducible when `E` is. Every irreducible has a cuspidal-support component as
in Notation 1.6, printed p.2181. Forgetting that support index and allowing
either sign gives exactly the present assertion. The imported generic
finite-length theorem supplies the class witnesses internally.

Corollary 3.9 uses the complex theorem 3.6, whose original proof on printed
p.2188 repeatedly uses Proposition 3.2. The official 1996 erratum, printed
p.4687, withdraws that proof and states that Proposition 3.2 was not known to
be true. Registered erratum ID: `aubert-1996-duality-erratum`; PDF SHA-256:
`d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f`.
The original p.2188 and erratum pp.4687–4689 were reread as text for this module.
They are recorded to mark the proof boundary; neither defective argument is
assumed to prove this proposition.

The later direct original assertion is Dubravka Ban and Chris Jantzen,
*The Langlands quotient theorem for finite central extensions of p-adic groups
II: intertwining operators and duality*, Glasnik Matematički 51 (2016),
153–163, Theorem 4.3, printed p.159 (PDF p.7), which explicitly states
preservation of irreducibility up to sign. Registered ID:
`ban-jantzen-2016-duality`; PDF SHA-256:
`7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.
Section 4, printed pp.158–163 (PDF pp.6–11), was reread as text; the two-sided
support correction on p.161 was also checked in the rendered image. The
present group is the trivial-cover specialization `G = GL_n(F)`.

Their correction uses the largest subset of each Bruhat support set invariant
under both left `W_J` and right `W_I`. This establishes double-coset minimality
before applying the geometric lemma. The maps on successive graded pieces are
then identities up to the exterior-algebra signs (printed p.162). The full
complex on p.160 ending in zero must retain its terminal homology: exactness is
required before that homology, or for the appropriate truncation. The p.161
parenthetical comparison concerns consecutive modified support sets. These
source qualifications, and the finite-length extension used in the length
argument of Corollary 3.9, are recorded in the published source audit
[`notes/henniart/aubert-duality-route.md`](../../../notes/henniart/aubert-duality-route.md)
and its retained audit guide. They do not add hypotheses to the present
proposition or constitute an implemented Lean proof.

## Future proof and independence

A corrected complex proof must construct the actual transition maps and prove
exactness before the surviving terminal homology. To deduce irreducibility
by Aubert's length argument it must also justify the needed finite-length
extension, nonvanishing, additivity and length comparison. Involutivity and
formal functor identities are separate proof obligations; their proposition
definitions alone are insufficient. An alternative complete independent
proof route is permitted. This module does not select such a route.

Ban–Jantzen Proposition 4.1(3), printed p.158, explicitly invokes Langlands
classification to prove whole-Levi induction invariance. A proof upstream of
this project's analytic segment classification must replace that dependency
by an independently proved input; it cannot import the complete later proof
as an unexamined certificate. The existing source audit records the
classification-independent GL-specific route and the distinct
Schneider–Stuhler alternative with its further dependencies.

The only direct imports here are the published `Aubert.AlternatingOperator`
and `Smooth.IrreducibleRealization`, whose existing Lean and Markdown pairs
are unchanged. A future proof must avoid the parent analytic segment
classification, multisegment exhaustion, ordered strong-head existence,
quotient coverage, tempered block uniqueness, square-integrable Langlands
classification or exhaustion, regular exhaustion, and their proof successors
and transitive proof inputs. This statement asserts no analytic
square-integrability, irreducibility of segment products, or segment
classification result.
