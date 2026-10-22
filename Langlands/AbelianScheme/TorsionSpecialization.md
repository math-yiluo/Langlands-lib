# Kernels and integer torsion for abelian schemes

Author: Worker 130.

This module specializes the generic kernel, multiplication and torsion
constructions to the parent's `Langlands.AbelianScheme S`. That bundle has an
actual commutative group scheme with smooth proper structure map and
geometrically connected fibres. Its explicit commutativity convention and the
separate source-definition-equivalence obligation are documented in `Basic.md`.
Nothing in this specialization proves that separate equivalence.

For an actual homomorphism `f : A ⟶ B`, `kernel f` is the previously constructed
fibre product of `groupHom f` with the unit section of `B`. Its canonical
inclusion `kernelι f` is a closed immersion: properness of `B` implies the
separatedness required by the generic closedness theorem. The result is a
group scheme; no smoothness or abelian-scheme structure is asserted for it.
`kernel_isPullback_scheme` records the actual scheme square.
`kernelPointsEquiv` is the existing equivalence with the kernel subgroup of the
induced homomorphism on every test scheme, and its naturality is inherited.
`kernelBaseChangeIso` specializes the generic kernel comparison to the parent's
actual base-change functor. Its inclusion equation and all-test-scheme point
compatibility are direct applications of the generic results.

The imported `MultiplicationSpecialization` supplies `multiplication A n`
in the parent's additive Hom notation, its identification with the generic
integer-power endomorphism, and its sections and base-change formulas.

`torsion A n` and `torsionι A n` are aliases of the generic torsion group scheme
and its inclusion, for every integer `n`. The equality with
`kernel (multiplication A n)` is definitional. The scheme pullback square,
closed immersion, pointwise equivalence, membership condition `x ^ n = 1`,
naturality under all maps of test schemes, and unique lifting criterion
specialize the generic theorems. No positive, nonzero or invertibility condition
is needed for these constructions.

This is a derived interface, not a new geometric theorem: all mathematical
constructions and proof arguments come from `Kernel`, `KernelBaseChange`,
`MultiplicationSpecialization`, `Torsion`, and `TorsionBaseChange`, using `Basic`
for the actual abelian-scheme bundle and its properness.
The underlying constructions have source provenance in Edixhoven–van der Geer–
Moonen, *Abelian Varieties*, registered preliminary draft
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42:
integer multiplication on printed p.30 (PDF p.34), and Definition (3.13) with
its continuation on printed pp.36–37 (PDF pp.40–41). The latter explicitly
requires a separated target for closedness. The proof here supplies that
hypothesis using the parent's properness instance.

`torsionBaseChangeIso` specializes the generic torsion comparison to the
parent's actual base-change functor. The forward and inverse inclusion
equations specialize its generic equations. `baseChangeTorsionPointsEquiv`
is the multiplicative equivalence between the actual torsion subgroups
under pullback adjunction. `torsionBaseChangeIso_points` specializes the
generic compatibility between this subgroup equivalence and the scheme
comparison. All of these proofs apply the generic results directly; the
parent's pullback objects and maps reduce to the underlying group-scheme
pullbacks. No new geometric theorem is used.

Finiteness and etaleness are not part of these definitions and remain the
separate finite-etale statement and proof obligation.
