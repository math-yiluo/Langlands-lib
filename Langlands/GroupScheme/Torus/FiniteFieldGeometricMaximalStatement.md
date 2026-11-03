# Geometrically maximal tori over finite fields: statement

Author: Worker 1487.

`FiniteFieldGeometricMaximalTorusStatement.{u}` says that a smooth
connected affine group scheme `G` over a finite field `k : Type u`
contains a torus `i : T.toGrp ⟶ G` that is maximal both over `k` and
after the actual base change to `AlgebraicClosure k`. It uses the
published `IsMaximalTorus`, which includes the torus and closed
immersion conditions. The universe is arbitrary. Finiteness is
`Finite k`, so the statement chooses no enumeration of the field.

This file defines a proposition and proves nothing. It is a finite-field
existence statement, distinct from the published rational maximal-torus
existence theorem. That theorem alone permits a trivial maximal torus
and does not prove geometric maximality.

## Original source and independence

Milne, *Algebraic Groups* (2017), Proposition 17.99, printed pp.383–384
(one-based PDF pp.399–400), constructs a Borel pair over a finite field.
Here the finite-field hypothesis is inherited from Section 17.k.
In its proof, a Borel subgroup and then a maximal torus over the
algebraic closure are conjugated to Frobenius-stable ones using Lang's
theorem 17.96. Descent gives the pair over `k`. Retaining just its torus
gives the present statement. A torus geometrically maximal in `G` is
also maximal over `k`, because a strictly larger closed torus would
remain a strictly larger closed torus after faithfully flat extension.

The smooth affine hypotheses imply finite type, and connectedness is
connectedness of the underlying topological space, as in Milne's group
variety convention. Tori are commutative, so representing them by
`CommGroupScheme` preserves the source scope.

The proof of Proposition 17.81 explicitly invokes this result in the
finite-field case (printed p.379, PDF p.395). Consequently a future
proof of this helper must keep that dependency direction: it must not
use `NoTorusUnipotentStatement`, maximal-torus preservation under
arbitrary field extension derived from it, or another theorem whose
proof depends on Proposition 17.81.

The source is registered as `milne-2017-algebraic-groups`. The full
official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
was read; its Chapter 17 entries do not change Proposition 17.99.
