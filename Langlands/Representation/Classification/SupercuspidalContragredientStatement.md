# Supercuspidality and the smooth contragredient (statement)

Author: Worker 23.

`Langlands.GeneralLinear.SupercuspidalContragredientStatement` is a `Prop`
definition. It states a theorem and does not prove it. The proof is a separate
obligation.

## Setting

Fix a prime `p`, a finite extension `F : PadicField p`, a topological
realization `T : F.TopologicalData` and a rank `n`. The group is the actual
`GL_n(F) = GeneralLinear n F.Carrier`, with the matrix-unit topology installed
by `T.topology` and the topological-group structure
`T.generalLinearTopologicalGroup n`. The representation `ρ` is an arbitrary
complex representation on a carrier `V` in an arbitrary universe `uV`. No
topology or finite dimension is imposed on `V`.

The smooth contragredient `smoothContragredient ρ` is the published
construction of `Langlands.Representation.Smooth.Contragredient.Definitions`:
the smooth part of the algebraic dual `Module.Dual ℂ V`, with
`g ↦ ᵗρ(g⁻¹)`. Its carrier `SmoothDual ρ` lies in the same universe `uV`, so
the statement stays inside one carrier universe.

`IsSupercuspidal` is the published predicate of
`Langlands.Representation.Classification.Supercuspidal`: admissibility, and
vanishing of the actual Jacquet coinvariants for every proper ordered block
parabolic and every conjugate of its unipotent radical. Irreducibility is
Mathlib's `Representation.IsIrreducible`.

## Assertion

For every smooth `ρ`:

1. `IsSupercuspidal (smoothContragredient ρ) ↔ IsSupercuspidal ρ`;
2. if `ρ` is admissible, then
   `Representation.IsIrreducible (smoothContragredient ρ) ↔
   Representation.IsIrreducible ρ`.

Smoothness of `ρ` is needed for part 1. The smooth contragredient only sees the
smooth functionals, so without it `ρ` could fail to be admissible while its
smooth contragredient is admissible.

Together the two parts let an irreducible supercuspidal object be sent to its
smooth contragredient inside the published `SupercuspidalRep` and
`SupercuspidalClass`. They give the class-level contragredient map that the
lattice and assembly work of other tasks needs. That map is not defined here.

## Sources

Literature ID `casselman-1995-admissible-representations` (W. Casselman,
*Introduction to the theory of admissible representations of p-adic reductive
groups*, draft of 1 May 1995), SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`. Section 2
works over a coefficient field of characteristic 0 and a locally compact group
with a basis of compact open subgroups. Sections 4 and 5 work over the group of
rational points of a reductive group over a nonarchimedean local field `k`.
`GL_n(F)` with complex coefficients is a case of both.

- §2.1, printed p. 21-22 (PDF pp. 21-22): the contragredient is the
  restriction of the algebraic dual to the functionals fixed by some open
  subgroup. This is the published `smoothContragredient`.
- Proposition 2.1.10, p. 22: for smooth `π`, `π` admissible ⇔ `π̃`
  admissible ⇔ `π̃̃ ≅ π`. The forward implication and reflexivity are
  already the published proposition target
  `Langlands.SmoothAdmissibleDualityStatement`. This statement neither
  repeats nor assumes it.
- Corollary 2.1.13, p. 22: "The admissible representation π is irreducible
  if and only if π̃ is." This is part 2.
- §5.1, p. 46: an admissible representation is absolutely cuspidal
  (supercuspidal) if `V_N = 0` for every proper parabolic `P = MN`. Every
  parabolic of `GL_n(F)` is conjugate to an upper block parabolic, which is
  why the published predicate uses block parabolics and all conjugates of
  their radicals.
- Theorem 5.3.1, (a) ⇔ (b), pp. 48-49: an admissible `π` is absolutely
  cuspidal if and only if `π̃` is. Casselman derives this from the canonical
  pairing of §4.2. With Proposition 2.1.10 it gives part 1 for smooth `ρ`.
- Corollary 4.2.5, p. 42: the contragredient of `(π_N, V_N)` is isomorphic
  to `(π̃_{N⁻}, Ṽ_{N⁻})` for the opposite parabolic `P⁻`. For `GL_n` the
  opposite of an upper block parabolic is conjugate to the upper block
  parabolic of the reversed shape. So the published "all conjugates"
  condition is stable under passing to opposite radicals.

The formal statement adds nothing beyond these sources. It only places them
on the published objects: the actual block coinvariants, the published smooth
dual and the published admissibility (finite-dimensional fixed vectors for
every open subgroup, as in Casselman §2.1).
