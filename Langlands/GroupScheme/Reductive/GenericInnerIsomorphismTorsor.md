# An integral torsor of inner isomorphisms containing a generic isomorphism

Worker 684.

This is a derived interface for the torsor step in Conrad, *Reductive group
schemes* (2014), Theorem 7.1.9(1), p.245, and the proof of Theorem 7.2.16,
pp.261–262. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
It packages actual schemes and maps rather than postulating an automorphism
scheme or a nonabelian cohomology calculation.

For commutative `R`, a field `K` with an `R`-algebra structure, integral group
schemes `G, H`, and a specified generic isomorphism `f`, the structure
`GenericInnerIsomorphismTorsor R K G H f` retains:

- a reductive integral group `adjoint`, a quotient of `G` by its full centre,
  and its automorphic action restricting to conjugation;
- an actual field-level adjoint quotient on base change, and agreement of
  the pulled-back integral action with that quotient's published inner action;
- an actual fpqc torsor `parameter` under `adjoint`, using the existing
  categorical action `ModObj` and its invertible shear;
- a natural family `localIso` of actual group isomorphisms parametrized by
  this torsor, on every relative test scheme;
- compatibility `e(d • a)(g) = e(a)(inner(d⁻¹)(g))`, and an actual `K`-point
  whose recovered base-change isomorphism is exactly `f`.

The inverse in the compatibility equation is required because the action is
a left action on isomorphisms by precomposition. It is tested on all schemes,
including schemes that are not reduced. The structure asserts neither
existence of these data nor representability of the whole isomorphism functor.
No domain, discrete valuation, completeness or residue hypothesis is built
into the definition.

`LocalGroupIso.atSection` evaluates any natural local isomorphism family at
an actual section of its parameter scheme. The pointwise group equivalences
are natural by the family's existing naturality; `isoOfPoints` recovers an
actual group-scheme isomorphism. `comp_atSection_hom` is its evaluation
equation on every test.

`GenericInnerIsomorphismTorsor.nonempty_section` is conditional on the supplied
torsor data. If `R` is complete for a maximal ideal `I` with finite quotient,
the reductivity of `adjoint` gives a smooth affine group with connected special
fibre. The published `IntegralTorsorPoint.nonempty_ringPoint` supplies a point
of the actual torsor, and its base equation identifies it with a section.
Thus the finite-residue lifting step is proved once the geometric torsor has
been constructed. This theorem does not construct that torsor and does not
prove `ReductiveLocalIntegerIsomorphismStatement`.
