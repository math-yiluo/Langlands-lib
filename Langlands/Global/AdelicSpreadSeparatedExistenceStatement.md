# Existence of separated arithmetic spreads

`Langlands.Global.AdelicSpreadSeparatedExistenceStatement` is the
conjunction of the function-field and number-field assertions below.
It asserts existence and supplies no proof.

For every function field `F` over a perfect field `k`, with the displayed
compatible `k`- and `RatFunc k`-algebra structures and finite dimension
over `RatFunc k`, every separated finite-type scheme `Y` over the
original `F` has a separated finite-type model `M` over
`curvePlaceSIntegers k F T.val`, for some finite superlevel `T` containing
any prescribed finite initial place set `S`. The output includes an
isomorphism over `F` from `curvePlaceModelGenericFiber k F T.val M`
to `Y`.

For every original number field `K`, the second clause asserts the same
conclusion over the actual outside-`T` integer ring
`(T.val : Set (FinitePlace K)).integer K`, with its generic fiber over
the original `K`. All archimedean places can be included in Conrad's
place convention without changing this integer ring.

In both clauses finite type means `LocallyOfFiniteType` and
`QuasiCompact` of the structure map. Separatedness is relative
`IsSeparated` of the indicated structure map. The integer rings are the
literal subrings of the original fields. The existing generic-fiber
definitions use `Over.pullback` along the spectra of their inclusions.
Thus the conclusion includes an actual arithmetic scheme and an actual
isomorphism in the over-category of schemes over the given field.
`AdelicLevelIndexAbove S` consists of finite sets containing `S`.

No initial model is assumed. The field scheme and the output model need
not be affine. The function-field constants need not be finite, the
specified rational-function extension need not be separable, and `S`
may be empty. There is no extra quasi-separatedness premise.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed pp.5–6, Theorem 3.4(1), the separatedness case of Theorem
3.4(2), and Remark 3.5 with its arithmetic application.

This is a derived arithmetic consequence. First plain spread existence
gives a finite-type model at some finite superlevel. The given
generic-fiber isomorphism transports separatedness from `Y` to that
model's generic fiber. Eventual separatedness then gives a further
finite superlevel at which the actual model base change is separated.
Finite type is stable under base change. Composition of the literal
integer inclusions and the pullback-composition isomorphism identify
the new model's actual generic fiber with the earlier one over the
original field, and hence with `Y`. Transitivity retains containment
of the prescribed `S`.

The source discusses global fields and nonempty place sets. The
arbitrary perfect constants, possibly inseparable specified extension
and empty initial set are derived scope: the existing actual integer
exhaustion and Noetherianity results have this scope, as do the plain
existence and eventual-separatedness interfaces. The argument uses
only these algebraic facts and base change. It requires no finite
constants or local compactness. Restricting to finite constants and a
nonempty initial set recovers Conrad's function-field scope.

The proof and the proofs of plain spread existence and eventual
separatedness remain separate publication obligations. This statement
asserts no topology theorem and does not complete the five-section
program.
