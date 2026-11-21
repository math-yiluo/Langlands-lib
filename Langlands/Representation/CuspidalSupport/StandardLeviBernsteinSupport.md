# Fixed-vector support in a standard Levi

Author: Worker 4.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version of 9 July 2026. VI.7.1, printed pp. 180–181 / PDF pp. 186–187, defines inertial support. VI.10.6, printed pp. 213–214 / PDF pp. 219–220, introduces the fixed-vector locus and describes the fiber of cuspidal support by composition factors of normalized induction. The Corollary on printed p. 215 / PDF p. 221 applies the fixed-vector locus inside a standard Levi. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The support predicates

This is the inside-Levi counterpart of the induction-defined predicates in [`BernsteinBlock`](BernsteinBlock.md), on the nested data and quotient in [`StandardLeviInertialClass`](StandardLeviInertialClass.md). For a datum `a` of `M_J`, `standardLeviCuspidalInduction` converts `a.val.roots ⊆ J` into the internal root label `I : Finset J` with `leviIndex J I = a.val.roots`. It applies the actual `leviNormalizedInductionFunctor` inside `M_J(F)` using the corresponding standard Levi-in-Levi decomposition. The inducing action is on the literal subgroup of `G(F)` via `bernsteinLiteralLeviRep`, the comparison from the represented Levi scheme. `standardLeviCuspidalInduction_eq_of_leviIndex_eq` lets the caller use any internal label with the same image: after identifying the image with the datum's label, the inclusion and decomposition inputs are proofs, so the expression is definitionally unchanged.

`IsStandardLeviCuspidalSupport a τ` means that `τ` is irreducible and a subquotient of this normalized induction. `IsStandardLeviInertialSupport s τ` requires such an occurrence for some datum whose class in `M_J` is `s`. These use the induction presentation of the support predicates, as in the representative form of the Corollary; they do not assert uniqueness or identify these predicates with a support map defined independently using Jacquet modules.

## The fixed-vector locus

`standardLeviFixedVectorSupportSet i ν family J K_M` is the subset of `StandardLeviInertialClass i ν family J` consisting of classes with an irreducible smooth complex witness of that inertial support and a nonzero `K_M`-fixed vector. This is the nested standard-family model of `B(M_J)_{K_M}`. The definition is valid for any subgroup `K_M` of the actual `M_J(F)`. The Corollary uses the specific `K_M` obtained by pulling `K` back along the inclusion into `G(F)`; no compactness or Iwahori premise is needed to define the set itself.

The module uses the standard family's relative subgroups with the rational-point topologies and the local compactness and nonarchimedean hypotheses for normalized induction. The quotient also uses the local-field and local-finite-type inputs for rational unramified twists. The field universe `uF` and the inducing carrier universe `uV` are independent; normalized induction takes values in carrier universe `max uF uV`. This unit defines the subset, not its preimage equality, finiteness, or an intrinsic-family comparison for `M_J`.
