# Abelian local analysis over a finite p-adic field

Worker 33 authors this theorem-statement contribution. It uses the actual finite
extension `PadicField p`, its explicit `TopologicalData`, its valuation integer
ring, and its residue cardinality. The single proposition
`Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement` is a coherent
abelian theorem family. It supplies no theorem proof or chosen epsilon system.

The shared `Langlands.HarmonicAnalysis.Basic` definitions belong to Worker 20:
quasicharacters are continuous homomorphisms from field units to complex units;
additive characters are continuous nontrivial circle-valued additive
characters; test functions are locally constant functions with compact support;
additive Haar measures include regularity; and the Fourier kernel is `psi(x*y)`.
The companion `Langlands.LocalFactor.Abelian.Padic` exposes the same concrete
Euler, zeta and Gauss expressions as callable functions. Local aliases in this
proposition use those names. Its two canonical factor constructors additionally
use Worker 20's actual conductor constructions; this target retains its
explicit least/greatest-level hypotheses and every possible uniformizer.
It introduces no competing character or Haar structure.

## Quantification and conductor conventions

The coefficient field is complex. The local-field carrier has arbitrary
universe, the prime is arbitrary, and the extension is any finite p-adic
extension with the supplied topology. No unramified or Galois restriction is
introduced. Measurability always uses the Borel measurable space of that topology.

Write `ord` for the actual normalized additive valuation, `q` for the actual
residue cardinality, `O` for the actual integer ring in the field, and `U` for
its nonzero elements of order zero. The field-unit filtration is `U` at level
zero and `1 + maximalIdeal^a` at positive integer level `a`. The latter is
expressed by the actual multiplicative valuation inequality on `v-1`; this
automatically includes `v=1`, without misusing `ord(0)=0`.

The multiplicative conductor is the least nonnegative level on which the
character is trivial. Existence and uniqueness, openness of the kernel, local
constancy, finite image and modulus one on `U`, invariance under inversion,
and the usual product bounds are conclusions. The product has the maximum
conductor when the two conductors differ, and unramified twists preserve it.
Existence of a field unit of order one is also a conclusion; subsequent
formulas quantify every such uniformizer, rather than a fictitious unit.

The additive conductor `n` is the greatest integer for which the character
is trivial on `ord(x) >= -n`, including zero via the actual multiplicative
valuation. Its existence and scaling are covered by the separate harmonic
statement family. Here `n` is quantified with this explicit characterization.
It is not an assumed Fourier theorem or epsilon-system existence theorem.

## Integrals, continuation, and the separate L-factor

Extend a quasicharacter by zero at the origin. The local zeta integral is

`Z(f,chi,s) = integral f(x) chi(x) |x|^(s-1) dx`,

with integrand explicitly zero at zero. This uses the multiplicative measure
`dx/|x|` on the nonzero field elements. Both sides of each functional equation
use this same multiplicative measure. For any uniformizer `pi`, the convergence
domain is `norm(chi(pi)) * exp(-Re(s)*log(q)) < 1`. Absolute integrability and
holomorphy on that domain are asserted.

The local L-factor is separately and explicitly
`(1 - chi(pi)*exp(-s*log(q)))^-1` for conductor zero and `1` otherwise.
Its reciprocal is totalized at a pole only as a normal meromorphic
representative. Nonvanishing and pointwise evaluations are asserted only where
its denominator is nonzero.

Every zeta integral has a unique `MeromorphicNFOn` continuation. The quotient
by L is specified by a unique finitely supported Laurent polynomial in
`q^-s`; this is an actual `Int ->₀ Complex`, not an unspecified analytic object.
The meromorphic identity holds as punctured germs at every point; equality of
values is added on the regular domain. Thus cancellation of a pole does not
force an incorrect zero at a removable singularity.

The explicit test function is `1_O` in the unramified case and
`chi^-1 * 1_U` in the ramified case. It belongs to the actual test space and
its zeta integral is `vol(U)*L(chi,s)`. Also
`vol(U)=(1-q^-1)*vol(O)>0`. This records the normalization of L independently
of the epsilon functional equation.

## Epsilon, scaling, and duality

Put `d=n+a`. For conductor zero, the epsilon expression is

`chi(pi)^n * q^(n*(1-s)) * vol(O)`.

For positive conductor it is the actual Gauss integral

`integral_(ord(x)=-d) chi(x)^-1 |x|^-s psi(x) dx`.

The annulus excludes zero. Integrability, nonvanishing and entire dependence
on `s` are conclusions. The expression is independent of the uniformizer;
the equivalent formula using every element `c` of order `d` is also stated.
In the ramified case its domain is `c^-1 U`, not `c U`.

The target states positive Haar scaling, additive-character scaling
`chi(b)*|b|^(s-1)`, unramified-character twisting by `omega(pi)^d`,
and the simultaneous spectral translations of both L and epsilon.
At fixed Haar measure, epsilon is `epsilon(0)*q^(-d*s)`.
Centering at `s=1/2` gives
`epsilon(1/2)*q^(-d*(s-1/2))`. These are distinct parameterizations,
not a silent change from a fixed Haar measure to a self-dual one.
For a unitary multiplicative character and the self-dual volume
`vol(O)=q^(-n/2)`, the centered epsilon value has modulus one.

The dual equation uses the inverse additive character, inverse multiplicative
character, spectral variable `1-s`, and the dual Haar measure:
its integer-ring volumes satisfy `vol_mu(O)*vol_nu(O)=q^-n`.
The product of these two epsilon expressions is one. No arbitrary-degree
nonabelian induction is inferred from this rank-one statement.

Finally the actual Fourier transform is asserted to be a test function and
the local functional equation is stated through the normal meromorphic
continuations:

`Zhat(chi^-1,1-s)/L(chi^-1,1-s) = epsilon(chi,s)*Z(chi,s)/L(chi,s)`.

It is an identity of punctured germs at every complex point. Neither Fourier
closure nor the functional equation is supplied as a hypothesis.

## Sources and derivation

* John Tate, *Number theoretic background* (1979), sections 2.3 and 3.1–3.2,
  especially (3.1.3), (3.2.1)–(3.2.3), (3.2.6.1)–(3.2.6.3), printed
  pp.11–14 (retained Corvallis Part II PDF pp.20–23). Section 3.6,
  printed p.17/PDF26, distinguishes fixed Haar and self-dual measure.
  Registered ID `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  In particular, the annulus and twist exponents on printed pp.13–14
  were checked visually in the original.
* Tate's thesis in Cassels–Fröhlich, *Algebraic Number Theory* (1967),
  Chapter XV, sections 2.3–2.5: quasicharacters, local zeta convergence
  and continuation, the local functional equation, and the nonarchimedean
  shell/Gauss computations, printed pp.311–322, retained PDF spreads
  164–170. The shell computations on pp.320–322 were checked visually.
  Registered ID `tate-1967-thesis`, SHA256
  `01259375a6275b726e836ce209cee40ed6f98a5cefe1aa5ad40f2ad07a63169e`.
  The finite Laurent-polynomial formulation is derived from those shell
  integrals: compact support bounds the shells below; local constancy at
  zero makes the tail geometric when the character is unramified and
  zero when it is ramified. Dividing by the stated L-factor leaves finite
  Laurent support. Its uniqueness follows from the range of `q^-s`.
* Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions
  L* (1973), section 3.3, internal/PDF pp.26–27, and section 3.4.3,
  internal/PDF p.28 (journal pp.526–528). These give the plus convention,
  fixed-Haar scaling, ramified Gauss integral and unramified twist exponent.
  The rank-one case of the inverse-character dual relation in section 5,
  internal/PDF p.49, has the required dual Haar measure. Registered ID
  `deligne-1973-local-constants`, SHA256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  These original formula pages were inspected visually.

The unit-filtration conductor product bounds are elementary consequences of
the actual filtration and the least-level characterization. Openness and
finite unit-image use continuity on the profinite unit group and the absence
of arbitrarily small nontrivial subgroups in the complex units. The remaining
specializations and the normal-meromorphic representation are derived
formulations, with the source conventions preserved.

## Dependencies and status

The current Library at commit
`459d17160ca3aef5c5b4e8ba056125e56d9479a0` supplies
`Langlands.LocalField.Definitions`,
`Langlands.LocalField.Normalization.Definitions`, and
`Langlands.HarmonicAnalysis.Basic`. Their published pairs and current
availability were verified. Reuse is by these Lean module and declaration
names. The harmonic source hash is
`2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff`.

The conductor and callable abelian constructions are also independently
reviewed and published in this Library. Their complete final reviews and
published pairs were read, and the actual Library sources match the checked
development sources exactly. They retain the conductor predicates and all
local expressions used by this statement. Workers 20 and 33's construction
authorship is preserved; this contribution imports those published
constructions by Lean name.

The following table retains the historical source fingerprints from the original
statement check, with module labels updated to canonical paths. In
`Abelian/Padic.lean`, the only source change is its import of `Abelian/Definitions`.
The current complete source hash is recorded in the
[migration record](Abelian/Definitions.md#structural-migration-record).

| Canonical import | Historical Lean SHA-256 |
| --- | --- |
| `Langlands.HarmonicAnalysis.Conductor` | `1780ea3172b1c84654e647efa3208d12c669a8c51a0942a1b80f4a66f84b4a53` |
| `Langlands.LocalFactor.Abelian.Definitions` | `18215959be4fdf7359708f2250aa94e60a3a78f6e99919ea0c7ada61cf74ba22` |
| `Langlands.LocalFactor.Abelian.Padic` | `1689aa7750d78260e3657d039053e4d496a1c945a43585ecdecc1b7e4ae7bf05` |

The adopted companion additionally constructs `rationalLFactor` and its
nonzero, regular-domain evaluation. Its Gauss-integrability proof applies to
every spectral parameter: the character is continuous away from zero, the
valuation shell is compact and excludes zero, and the absolute-value power is
constant on that shell. The bridges identify this shell with the statement's
`gaussShell` and the canonical `deligneConstant` with the owner's abelian
expression. They give downstream constant systems actual functions and
proved comparison lemmas. They do not assume a functional equation or a
nonabelian system.

The unchanged statement passed check
`6d2e8dc1-20f6-4e97-afb9-296e8d3fd7a7` against the exact sources now
published under the names above and the published foundations. Incremental
Lake build and whole-declaration inspection both terminated with exit code
zero, no errors or warnings, and quiet process trees. Inspection confirms a
definition returning `Prop` at carrier universe `u`, using only
`propext`, `Classical.choice` and `Quot.sound`. The target fingerprint remains
`1b87b27a4f2f760c082b607704102bc51f8d2f681ea577fa7db6d5ad8823239c`.
The statement source remains
`a7302e448a0ebf4b4d0039565d5a1cc8b4f3b65a73c7bc5a9b04f694ea07aee1`.
The checked snapshot is
`980d5cf3e032274371cb56cddcffcea58d557d9f807cbf91851195e8b5c3449f`.

This is a statement submission for independent semantic review. Compilation
and target inspection do not prove the proposition or establish its independent
semantic acceptance. No theorem proof, chosen local-factor system, or
whole-task completion is claimed.

## Import-path migration

Worker 64 changed the single project import to
[`Langlands.LocalFactor.Abelian.Padic`](Abelian/Padic.md). The proposition,
its complete universe telescope, and every non-import source byte are unchanged.
The preceding source/check identifiers describe the original statement submission;
the [migration record](Abelian/Definitions.md#structural-migration-record) records the new checks.
