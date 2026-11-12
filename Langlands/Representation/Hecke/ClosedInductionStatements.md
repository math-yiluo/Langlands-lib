# The explicit Hecke Hom model of smooth induction: statement

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.5 Remark and equations
(III.2.5.1)–(III.2.5.5), printed pp.74–75 / PDF pp.80–81.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`ClosedInductionHomStatement` is a closed `Prop`-valued definition, not a
proof. It concerns an arbitrary closed subgroup `H` of a Hausdorff locally
compact nonarchimedean group `G`, with left Haar measures. Local
compactness of `H` is derived from its closedness; its nonarchimedean
structure is the published subgroup instance. No extra subgroup-topology
hypotheses or equivalence certificates are supplied.

The functors being compared are only composites of existing objects:
`inducedHeckeFunctor` is the published smooth function induction followed
by `heckeNondegenerateModuleFunctor`, and `homInductionHeckeFunctor` is the
published Hecke functor for `H` followed by the actual Chapter I
`Homomorphism.I`. Its carrier is precisely the nondegenerate part of
`NonUnitalModuleHom (HeckeAlgebra μH) (HeckeAlgebra μG) W`, with the
left subgroup action already constructed in `HomomorphismLeft`.

The target asserts a natural isomorphism `α` between those functors and
the following concrete descriptions.

- In the direction from induced functions to module maps,
  `q_f(T) = (T · f)(1)`, where `T · f` is the published integrated Hecke
  action on the actual induced representation. This is (III.2.5.5).
- Every nondegenerate Hom vector `q` is fixed by some normalized
  compact-open indicator `e_K`, in the explicit form
  `q(T * e_K) = q(T)` for every `T`.
- For every such choice of `K`, the inverse sends `q` to the function
  `g ↦ q(l(g)e_K)`. Under Haar distributions, `l(g)e_K` is
  `δ_g * e_K`. This is (III.2.5.2), with the Dirac evaluation explained
  exactly as in the source. Quantification over every fixing `K` implies
  independence of that choice. Covariance (III.2.5.3) and uniform right
  smoothness are retained by the actual induced-function codomain.
- For an indicator `e_U` of `H` fixing `T`, the subgroup Hecke action
  satisfies `(l(h)e_U) · T = l(h)T`. This is the operative identity
  (III.2.5.4); both sides use the actual restricted left regular action.

Naturality and inverse identities belong to the asserted natural
isomorphism, not to assumed data. The group universe `uG` and input
carrier universe `v` are independent. Both functors have the common
output carrier universe `max uG v`, inherited from the actual function
and Hom constructions.

No III.1.4 equivalence proof is needed as an input or smuggled into the
statement: the comparison is made directly in the Hecke-module category
using its published functor. By III.1.4, this is the smooth-representation
identification (III.2.5.1). A proof is a separate task.
