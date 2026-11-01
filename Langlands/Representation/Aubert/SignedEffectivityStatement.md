# Signed effectivity on constituents of quasicuspidal induction

Author: Worker 76.

`Langlands.Aubert.SignedEffectivityStatement.{uF,uV} F T` states the following
nonnegativity assertion. Let `B` be an ordered positive block shape of rank
`n`, let `σ` be an actual irreducible smooth complex representation of its
product Levi, and assume that `σ` is quasicuspidal for all proper standard
refinements. If an actual irreducible smooth representation `π` of `GL_n(F)`
is an actual subquotient of the normalized induction of `σ`, then

```text
factorMap (((-1 : ℤ)^(n - B.length)) • alternatingOperator F T n [π])
  ∈ VirtualRepresentation.effective.
```

Here `factorMap` is the published integer-linear composition-factor map out
of the exact finite-length smooth Grothendieck group.
`VirtualRepresentation.effective` means that every integral coefficient on
every actual irreducible isomorphism class is nonnegative. The statement is
a proposition definition and has no proof in this module. It does not assert
that the displayed vector is nonzero, has length one, or has a chosen actual
realization.

## Scope and conventions

The parameters are arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and supplied `T : F.TopologicalData`. The statement
installs that topology. The field universe `uF` and carrier parameter `uV`
are independent, and both `σ` and `π` have carriers in
`Type (max uF uV)`. The induction functor has the same saturated carrier
universe. Every rank is included, including the empty Levi at rank zero.

Quasicuspidality is exactly `CuspidalSupport.IsLeviQuasicuspidal B`: the actual
unipotent coinvariants vanish on every proper standard refinement. No
admissibility hypothesis is imposed. Irreducibility of `π` supplies its
finite-length witness through the published
`SmoothRep.hasFiniteLength_of_isIrreducible`. No finite vector-space
dimension, central character or classification hypothesis is present.

`SmoothRep.IsSubquotient` retains an actual invariant submodule, a quotient
of that submodule by another actual invariant submodule, and an actual smooth
isomorphism to `π`. Thus the hypothesis concerns constituents of an actual
induction, rather than a chosen formal support set. The imported normalized
induction uses upper block parabolics, positive half-modulus covariance and
right translation. The unadjusted `alternatingOperator` uses the actual
normalized upper-unipotent Jacquet functor and all exact short exact
relations, including nonsplit ones. Its coefficients remain
`(-1)^(n - C.length)` for the shapes `C` in its defining sum.

The additional sign in the displayed assertion is the *single common sign*
`(-1)^(n - B.length)` attached to the inducing quasicuspidal support. It is
not an independently selected sign for each constituent.

## Provenance and proof obligation

This is a derived GL specialization of the effectivity consequence of
Aubert's duality complex. Anne-Marie Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie
d'un groupe réductif p-adique*, Transactions of the AMS 347 (1995),
2179–2189, Theorem 3.6, printed pp.2187–2188, identifies the support-adjusted
class with the class of its terminal homology. Corollary 3.9, printed p.2189,
uses this on constituents of an induction from irreducible cuspidal data.
The registered source is `aubert-1995-duality`, PDF SHA-256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
These three pages were read in preparing this statement. For the standard
GL Levi of shape `B`, the source's simple-root subset has cardinality
`n - B.length`. Passing to the published composition-factor lattice gives
the coordinate nonnegativity assertion above. Irreducible smooth
quasicuspidal data are used without adding admissibility to the interface;
any proof that needs admissibility must obtain it independently.

The original proof of Theorem 3.6 is not a proved input. It uses the
withdrawn proof of Proposition 3.2. The repaired route is Dubravka Ban and
Chris Jantzen, *The Langlands quotient theorem for finite central extensions
of p-adic groups II: intertwining operators and duality*, Glasnik Matematički
51 (2016), 153–163, section 4, especially printed pp.160–162. Registered
source: `ban-jantzen-2016-duality`, PDF SHA-256
`7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.
Section 4 was read in preparing the parent work, and pp.160–162 were reread
for this statement.

A proof through that complex must construct the actual transition maps,
use support invariant on both the left and right under the appropriate Weyl
subgroups before applying the geometric lemma, and check the induced maps
on graded pieces with their exterior-algebra signs. It must establish
exactness before the surviving terminal homology. The full complex ending
in zero cannot be treated as exact. A citation to the original proof, the
erratum alone, or the conclusion of irreducible preservation supplies none
of these steps.

This statement isolates only coordinate effectivity for irreducible
constituents. It does not require a finite-length extension of a homology
functor to arbitrary input representations. The parent irreducible-image
argument is intended to combine this input with independently proved
involutivity, induction commutation, the eigenvalue on quasicuspidal inducing
data and elementary counting in the composition-factor lattice.
The statement and its imports make no use of segment classification,
multisegment exhaustion, Langlands quotient coverage, tempered block
uniqueness or square-integrable classification. A future proof must preserve
the parent task's exclusions and independently justify all its inputs.
