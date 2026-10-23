# Character separation for irreducible admissible representations

`Langlands.CharacterSeparationStatement.{uG,uV,uW}` states Bernstein–Zelevinsky
(1976), Corollary 2.20, for the actual distribution character already defined in
`Langlands.Representation.Character.Basic`. It is a proposition definition;
this file proves no character-separation theorem.

The group is Hausdorff, locally compact and totally disconnected, with its
Borel measurable structure and continuous multiplication and inversion. These
are the locally profinite group hypotheses corresponding to the source's
l-groups (Section 1.1, printed/PDF p.6). The two representation carriers have
independent universes and only complex vector-space structures. In particular,
neither carrier has a topology or a finite-dimensionality assumption.

The measure is a regular left Haar measure. Mathlib's `IsHaarMeasure` requires
left invariance, finite mass on compact sets and positive mass on every nonempty
open set; `Regular` records the usual regularity convention separately. This
excludes the zero measure. This restriction matters because the more general
published character construction permits zero measure, for which every
character is zero and separation is false.

For actual representations `ρ` and `σ`, both admissible and irreducible, the
statement is

\[
  \Theta_{\rho,\mu}=\Theta_{\sigma,\mu}
  \quad\Longleftrightarrow\quad
  \exists E:V\mathrel{\simeq_{\mathbf C}}W,\quad
  E(\rho(g)v)=\sigma(g)E(v)\text{ for every }g,v.
\]

Equality on the left is equality in the complex algebraic dual of the actual
locally constant compactly supported test functions. Each value is the genuine
finite-rank trace of the integrated operator, as implemented by
`Character.distribution`, rather than ordinary trace on an infinite-dimensional
ambient carrier. The right side requests an actual linear equivalence with
pointwise equivariance; it does not assume that an equivalence exists.
Admissibility includes smoothness and finite-dimensional fixed vectors for all
open subgroups. No genericity, compact-coefficient condition or unitarity is
imposed. There is no assumption of right Haar invariance or unimodularity.

## Source correspondence and proof boundary

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Representations of the group GL(n,F) where F is a non-archimedean local field*,
Russian Mathematical Surveys 31:3 (1976), 1–68, source
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

Corollary 2.20 on printed/PDF p.21 is exactly equivalence of irreducible
admissible representations if and only if their characters are equal. Section
2.17 fixes the Haar measure used to define the character. Proposition 2.19
establishes the stronger linear-independence statement for pairwise inequivalent
irreducible admissibles, reducing via 2.10 to finite-dimensional representations
of compact-open Hecke corners. The present target asserts only the two-object
separation corollary. Independent carrier universes express ordinary
representation equivalence without placing both spaces in a common carrier.

The implication from an equivariant equivalence to equality of characters is
already available as `Character.distribution_eq_of_equivariant`. The converse
remains a separate proof obligation. Defining this target does not prove the
Gelfand–Kazhdan realization, distribution transpose invariance, or the generic
contragredient theorem.
