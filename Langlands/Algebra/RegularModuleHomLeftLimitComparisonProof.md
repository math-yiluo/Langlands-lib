# Reconstruction proof for the actual regular-Hom comparison

Worker 6 authored the reconstruction proof for the whole Renard book program.
Worker 185 checked the draft against the published statement and original source,
added the public per-ring theorem and its complete unapplied universe checks,
and prepared this proof unit for independent review.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implemented route is the reconstruction in the proof of the
I.1.4 proposition, printed p.10/PDF16. Actual compatible families
and their left-coherence equations come from printed p.9/PDF15.
Finite local units and the corner order are from I.1.1–I.1.2,
printed pp.6–7/PDF12–13.

The theorem `regularModuleHomLeftLimitComparisonTheorem_proof` proves
the closed target `RegularModuleHomLeftLimitComparisonTheorem`.
The public per-ring theorem `regularModuleHomLeftLimitComparison` proves
`RegularModuleHomLeftLimitComparison A M` from `IsIdempotented A` for
the specified original action. All reconstruction helpers remain private
to this proof.

For a family `x` and an original scalar `a`, choose an actual
idempotent `e` with `a*e=a` and set the reconstructed value to
`a • x(e)`. If `f` is another such right unit, the published
finite-upper-bound lemma supplies a common upper idempotent `g`.
Family coherence writes `x(e)=e • x(g)` and `x(f)=f • x(g)`.
Associativity of the original action and the two right-unit equations
then make both reconstructed values equal to `a • x(g)`.
Consequently every permitted right unit computes the same value.

The zero scalar law is the original zero action law. A common
right unit for `a` and `b` also fixes `a+b` on the right, so
distributivity proves additivity in the scalar. A right unit for
`b` also fixes `a*b` on the right, and associativity gives
`φ(a*b)=a • φ(b)`. This constructs an actual `RegularModuleHom`.
Using the same right unit for each family in a sum proves
additivity in `x`, and the zero-family law is `a • 0=0`.
The inverse reconstruction is therefore an actual additive map
from `NonUnitalModuleLeftLimit A M` to `RegularModuleHom A M`.

For an original Hom `φ`, reconstruction of its evaluation gives
`a • φ(e)=φ(a*e)=φ(a)` at every source scalar `a`.
In the other direction, evaluating reconstruction at an actual
idempotent `e` allows `e` itself as the right unit; the family's
fixed-coordinate equation gives `e • x(e)=x(e)`.
These identities supply both inverse laws of the actual additive
equivalence. Its forward additive homomorphism is definitionally
the specified evaluation. The proved reconstruction formula holds
at every permitted right unit, and the previously proved
`RegularModuleHom.toLeftLimit_comp_canonical` supplies exact
compatibility with the original-vector canonical maps.

The proof retains independent ring and vector universes and every
original target action. No nondegeneracy is used: local units are
chosen for source scalars, and the only target equations used are
the original action laws and the given family coherence. This is
the internal extension of the source's nondegenerate-module setting
described in the statement pair. Zero rings, zero actions, trivial
carriers and noncommutative nonunital rings remain included.
The closed-target checks and the complete unapplied per-ring interfaces
include arbitrary independent `uA, uM` and both unequal universe
assignments `(0,1)` and `(1,0)`. The closed theorem has no additional
section hypotheses.

This proof concerns only the algebraic additive comparison. It
does not install a scalar action on the family carrier or address
topology, analytic completion, the completion functor,
nondegenerate-part comparison or the adjunction.

The supplementary registered source
`renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`),
PDF page 1, corrects the older printed condition `ae=e` to `ae=a`.
The governing 2026 PDF16 already has `ae=a`, which is the condition
used throughout this proof. This older errata list does not replace
the 2026 original.
