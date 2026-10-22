# Parameters for the actual local Weil group

Author: Worker 53. This definition contribution specializes Worker 17's
generic representation and Weil–Deligne framework to the actual group assembled
in `Assembly`. Its imports `Langlands.Weil.Local.Assembly` and
`Langlands.WeilDeligne.Parameters` are published at Library commit
`0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf`; the environment is Lean 4.34.0 with
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

For every prime `p` and algebraic `F : PadicField.{u} p`, the group, inertia,
geometric degree, and norm character are constructed from `F` itself.
`LocalWeilRepresentation.{u,v} F` uses actual finite-dimensional complex vector
spaces of independently chosen universe `v`. The field universe `u` is arbitrary.
The carrier is neither a dimension label nor a replacement for an isomorphism class.

`LocalWeilClasses` and `LocalWeilClassesOfRank` reuse the genuine quotient by
linear equivariant isomorphisms. `LocalContinuousWeilObjects` uses the usual
complex module topology; `LocalOpenInertiaWeilObjects` separately uses an open
kernel on actual inertia. The continuous irreducible and open-inertia semisimple
class sets are separate subtypes, and no equivalence of these predicates is
assumed. The generic predicates `HasFiniteInertiaImage`, `IsUnramified`,
`IsUnitary`, `HasFiniteImage`, `IsIrreducible`, and `IsSemisimple` apply directly
to these local representation objects. `IsLocalGaloisType` specializes extension
of the action along the actual projection to the absolute Galois group. It is
not identified with finite image by definition.

`LocalWeilDeligneRepresentation` uses the actual character whose value at
geometric Frobenius is the inverse actual residue cardinality. Its nilpotent
endomorphism satisfies the genuine conjugation covariance law. The
`LocalWeilDeligneClassesOfRank` alias imposes no additional predicate.
`LocalParameterObjects`, `LocalParameterClasses`, and
`LocalParameterClassesOfRank` impose open inertia kernel but allow nonzero
monodromy. `IsLocalFrobeniusSemisimpleParameter` and
`LocalFrobeniusSemisimpleParameterClassesOfRank` add semisimplicity of the
Weil action at every nonzero actual degree. They do not impose `N = 0`.
Every rank is supported, with rank zero retained for algebraic closure operations.

All category, linear isomorphism, quotient equivalence, and rank well-definedness
obligations are inherited from the generic constructors. The local
zero-monodromy functor and its explicit fully faithful certificate reuse that
construction; `localZeroMonodromyParameter` retains the existing open-inertia
proof on the same carrier. No classification, Frobenius semisimplification,
reciprocity, or local Langlands bijection is chosen.

Source correspondence: this is derived local specialization of Tate,
*Number theoretic background* (1979), sections 4.1.2–4.1.7, printed pages
20–21 / PDF pages 29–30 of the retained Corvallis Part II volume.
Those original pages were read directly. Literature ID:
`tate-1979-number-theoretic-background`; PDF SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The geometric sign and actual field data are documented in `Assembly.md`.
The definitions and proof provenance of the
generic layer remain Worker 17's, as documented in
`Weil/Representation/Basic.md`, `Predicates.md`, and
`WeilDeligne/Basic.md`, `Parameters.md`. The local aliases and functor
specializations introduce no new mathematical equivalence claim. Tate's later
existence and equivalence assertions are not structure fields or assumed
constructors in this module.
