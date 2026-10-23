# Character transport under smooth duality and group automorphisms

This module defines two proposition targets and their conjunction
`Langlands.CharacterTransportStatement.{uG,uV}`. It proves neither identity.
Both use the actual finite-rank distribution character from
`Langlands.Representation.Character.Basic`.

The group is Hausdorff, locally compact and totally disconnected, with
continuous group operations and its Borel measurable structure. The complex
representation carrier has an independent arbitrary universe, no topology and
no finite-dimensionality assumption. The measure is left invariant and finite
on compact sets. Unlike character separation, these identities do not require
positive mass on open sets: they remain meaningful for the zero measure.

## Smooth dual

`CharacterSmoothDualStatement` additionally requires inversion invariance of
the measure. For every admissible representation `rho`, it asserts existence
of a proof `hdual` that the actual `smoothContragredient rho` is admissible, and
the identity, for every actual locally constant compactly supported function,

\[
  \Theta_{\widetilde\rho,\mu}(f)
    = \Theta_{\rho,\mu}(g\mapsto f(g^{-1})).
\]

The smooth dual is the published subspace of the full complex algebraic dual,
with its actual inverse action. It is not renamed from an automorphism
pullback. Its admissibility is a conclusion, not an additional assumption.
The inversion operator on test functions has no modular factor, so inversion
invariance is an explicit hypothesis. Neither irreducibility nor genericity
is required.

The intended algebraic step is that the full algebraic transpose image of an
integrated operator consists of smooth functionals. Preservation of functionals
already known to be smooth is weaker and cannot by itself justify the trace
comparison. This containment and the character identity remain proof
obligations of the target.

## Group automorphism

`CharacterAutomorphismStatement` takes an actual continuous group automorphism
`e` preserving the chosen measure. It concludes admissibility of the actual
representation `rho.comp e.toMonoidHom`, and

\[
  \Theta_{\rho\circ e,\mu}(f)
    = \Theta_{\rho,\mu}(f\circ e^{-1}).
\]

The inverse in the test-function argument is essential: the change of
variables is `y = e(x)`. No assumption that `e` is an involution appears.
This target does not require inversion invariance. Measure preservation is
explicit; a general automorphism can scale Haar measure.

## Provenance

These general locally profinite statements are internal extractions of the
two character computations in the proof of Theorem 7.3, printed/PDF p.57, of
I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F)
where F is a non-archimedean local field*, Russian Mathematical Surveys 31:3
(1976), 1–68. The registered source is
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`,
retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

The source computes the character of its signed inverse-transpose pullback
by a measure-preserving change of variables. It computes the smooth-dual
character using the transpose of the integrated operator for the inverted
function, finite rank, and containment of the entire transpose image in the
smooth dual. Section 2.17, printed/PDF p.21, defines the distribution character
by this genuine finite-rank trace. The general automorphism and group
hypotheses here isolate the conditions used in those computations; the source
does not state this general two-part proposition verbatim.

Published compact-open smooth duality supplies the route to dual
admissibility, and published pullback transport supplies the route to
automorphism admissibility. The proposed identities require actual operator
comparison and trace laws. Their conjunction asserts no character separation,
transpose invariance of conjugation-invariant distributions, Gelfand–Kazhdan
equivalence, or generic contragredient theorem.
