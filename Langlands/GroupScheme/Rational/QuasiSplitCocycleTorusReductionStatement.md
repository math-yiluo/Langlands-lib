# Torus reduction for cocycles of quasi-split semisimple groups

`QuasiSplitCocycleTorusReductionStatement.{u}` is an unproved proposition for
arbitrary universe `u`. For every field `K : Type u`, every actual semisimple
quasi-split group scheme `G` over `K`, every finite Galois extension `L/K` in
that same universe, and every natural cocycle of `G` on `Spec L → Spec K`, it
requires a `Cocycle.TorusReduction` of that cocycle.

The existing `IsSemisimple` includes connected reductivity and finiteness of
the full scheme-theoretic centre. `IsQuasiSplit` retains an actual
field-defined Borel that remains Borel over the algebraic closure. The
conclusion supplies an actual finite Galois field cover refining the original
one by an fpqc morphism, a cochain, a ground-field torus and a closed torus
inclusion, and factorization of the twisted cocycle on every relative scheme
valued test. The torus need not already split on the original cover. The
statement has no dimension, norm, perfectness or characteristic hypothesis.
It is a structural prerequisite for the separate dimension-one theorem.

The source is the cocycle-to-torus argument of Steinberg, *Regular elements
of semi-simple algebraic groups* (1965), Section 10, printed p.78/PDF p.31,
and the removal of the simply-connected restriction and Theorem 11.1 in
Section 11, printed p.79/PDF p.32. Source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
Steinberg states these results over a perfect field. Borel–Springer,
*Rationality Properties of Linear Algebraic Groups II* (1968), Section 8.6,
printed pp.483–484/PDF pp.41–42, extends the regular-semisimple conjugacy
argument to arbitrary ground fields and explains that the arguments of
Steinberg Sections 10 and 11 then apply in the reductive setting. Source
`borel-springer-1968-rationality-properties-ii`, SHA-256
`e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`.
No corresponding source-specific project errata note was found.

This is a derived concrete finite-cover formulation of the cited argument,
restricted to semisimple groups, which suffices for an adjoint acting group.
The sources describe a class in Galois cohomology coming from a torus. The
Lean target requires actual finite-cover representatives, their equivalence
cochain, and the scheme-valued factorization. Passing between those
formulations, including choosing a common finite Galois refinement in the
universe of the ground field, is part of the proof obligation. No such
comparison or structural existence is asserted as proved here.
