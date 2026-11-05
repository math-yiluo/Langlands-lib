# Affine algebraic geometric irreducibility spreading

`Langlands.Algebra.FiniteTypeGeometricIrreducibilitySpreading.{u,v,w}` is a
Prop-valued statement of the algebraic affine case of Stacks Project
Lemma 37.27.5 (0559). It is an internal algebraic reformulation of that lemma,
rather than a quotation of a separately numbered algebraic result. This file
and its Lean pair state a proposition only; they provide no proof.

Let R be any commutative ring whose nilradical is prime, and let B be a finite
type commutative R-algebra. Write p = nilradical R. The hypothesis says that
the nilradical of `AlgebraicClosure p.ResidueField ⊗[R] B` is prime. The
conclusion supplies c in R with `¬ IsNilpotent c` such that, for every field
K and unital ring map φ from R to K with φ(c) nonzero, the nilradical of
`K ⊗[R] B` is prime. The map φ may have a nonzero kernel: all such field
maps are tested, not just embeddings or maps at maximal ideals.

The prime p is the generic point of Spec R. Mathlib's `Ideal.ResidueField`
is the residue field of the local ring `Localization.AtPrime p`; it also
has an `IsFractionRing (R ⧸ p) p.ResidueField` instance. Thus the field in
the generic hypothesis is the actual generic residue field κ(p), and its
algebraic closure is taken before extending scalars. The canonical map from
R to κ(p) has kernel p, as expressed by
`Ideal.ker_algebraMap_residueField`. No fraction field of the possibly
nonreduced ring R is assumed.

Both tensor products use the specified R-algebra structure on B. In the
hypothesis the R-algebra structure on `AlgebraicClosure p.ResidueField`
is the canonical composite through κ(p). In the conclusion the local
instance `letI : Algebra R K := φ.toAlgebra` makes the tensor product use
the particular quantified map φ. The universes u, v and w for R, B and K
are independent.

The source correspondence uses
`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`: a prime nilradical
expresses irreducibility of the spectrum, including nonemptiness because
a prime ideal is proper. Applied to the scalar extension to an algebraic
closure of κ(p), this is the affine geometric generic-fibre hypothesis.
The non-nilpotent c defines a nonempty principal open D(c), which contains
the generic point. The conclusion expresses irreducibility and nonemptiness
after every field-valued base change lying over D(c), hence tests the field
extensions that occur in geometric irreducibility. These identifications
explain the derived algebraic formulation; they are not proved in this pair.

Stacks Lemma 37.27.5 assumes an irreducible base, a geometrically irreducible
generic fibre, and a morphism of finite type, and supplies a nonempty open
over which all fibres are geometrically irreducible. The displayed
statement adds no reducedness, Noetherianity, finite presentation, flatness
or finite type over a field. Its proof is a subsequent obligation.
The arbitrary-scheme theorem still needs affine pullback and generic-fibre
comparisons, finite open covers and overlap assembly; those remain with
task `b84ed957-94d1-44b7-bd4a-ba61366eeabb`.

Source: [Stacks Project, Lemma 37.27.5 (0559)](https://stacks.math.columbia.edu/tag/0559),
statement and both proofs, including the corrected generic-fibre wording
and page comments, in registered source
`stacks-generic-geometric-irreducibility-2026-11-04`.
Retained file:
`literature/Stacks Project - Generic geometric irreducibility and finite etale splitting (HTML snapshot 2026-11-04)/0559.html`.
Collection SHA256:
`7779fd83e268ecb0b8a0b8783d039fea6de1ccf33ce652f9bf972c9697b02f8c`;
file SHA256:
`6dc5e34232f56f8111e2581afd2822d79276b962e4110f23eb411ab8b166ca1f`.

Worker 1606 authored the proposed Lean statement and paired explanation
supplied in this task's context. Worker 1620 reused that draft, checked its
source correspondence, and expanded the explanation of the generic field,
scalar structures and remaining proof obligations.
