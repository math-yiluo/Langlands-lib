# Top dual homology of a residue-field resolution

Author: Worker 1015.

`Langlands.CommutativeAlgebra.RegularLocalResidueResolutionDualityStatement.{u}`
defines a proposition and supplies no proof.

Let `R : Type u` be a commutative regular local ring of Krull dimension
`g : ℕ`, and write `k` for its residue field. Let `C` be a bounded
cochain complex of finite free `R`-modules with terms supported in
degrees `0` through `g`. Suppose its homology vanishes in all degrees
other than `g`, and its degree-`g` homology is isomorphic to `k` as an
`R`-module. The conclusion is that the degree-`g` homology of
`reversedDual g C` is also isomorphic to `k` as an `R`-module.

The reversed dual is the actual complex whose term in degree `i` is
`Hom_R(C^(g-i), R)` and whose differential is the transpose of the
corresponding differential of `C`. The declaration uses the existing
`reversedDual` construction, including its unsigned differential
convention. Both isomorphism hypotheses and conclusions use
`Nonempty` of the categorical isomorphism type in `ModuleCat R`.
Indices are integers; the natural number `g` is coerced to an integer
in these expressions. In the Krull dimension equality it is coerced
to `WithBot ℕ∞`. The case `g = 0` is included.

This is a derived supporting assertion from Edixhoven, van der Geer
and Moonen, *Abelian Varieties*, preliminary version of the first
chapters, (9.9), printed p.130 (PDF p.134), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. The retained PDF
has SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
There is no project errata note for this source.

The source compares its free resolution of `k` with a Koszul
resolution for a regular system of parameters. It states that the
resolutions are homotopy equivalent, then dualizes back. The last
dual differential has image the maximal ideal, so its cokernel is
`k`. The current proposition isolates that consequence for any
finite free resolution with the stated degree convention. It
asserts existence of an isomorphism, without choosing parameters,
a comparison map, or a canonical isomorphism.

With the usual resolution indexing, the conclusion expresses
`Ext_R^g(k,R) ≅ k`. No Ext construction or comparison is implemented
here. In particular, the proposition definition supplies neither a
Koszul resolution proof nor a proof of the punctual perfect-complex
statement. Lower-degree dual acyclicity is outside its conclusion.
