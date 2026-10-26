# Compact-quotient bijectivity of the finite-product induction tensor map

Author: Worker 524.

`Langlands.Induction.FiniteProductTensorBijectiveTheorem` is a proposition
definition stating bijectivity of the published canonical map
`Langlands.Induction.finiteProductTensorMap P σ`. This module states the result;
it contains no proof of bijectivity.

The statement quantifies over a field `k : Type uK`, a finite index type
`ι : Type uI`, groups `G i : Type uG` with topologies and instances
`NonarchimedeanGroup (G i)` and `WeaklyLocallyCompactSpace (G i)`, subgroups
`P i : Subgroup (G i)` with `CompactSpace (Induction.LeftQuotient (P i))`,
and arbitrary vector spaces `V i : Type uV` with representations
`σ i : Representation k (P i) (V i)`. The nonarchimedean instances supply
the topological group instances. The quotient is the actual quotient by
`QuotientGroup.rightRel (P i)`, with classes `P i * g` and its quotient
topology. Neither closedness of `P i` nor a Hausdorff hypothesis is imposed.

There is no topology on the coefficient spaces and no smoothness assumption
on the inducing actions. There are no assumptions of finite dimensionality,
admissibility, irreducibility, or finite length. No comparison, inverse,
evaluation splitting, or theorem-valued replacement is an input.

The asserted bijection has source and target

\[
\bigotimes_{i\in\iota}
  \operatorname{Ind}_{P_i}^{G_i}(\sigma_i)
\ \longrightarrow\
\operatorname{Ind}_{\prod_iP_i}^{\prod_iG_i}
  \left(\boxtimes_i\sigma_i\right).
\]

Here both induced representations are the Library's actual `smoothInduced`,
whose functions have covariance `f (p * g) = σ p (f g)` and a single open
right stabilizer for the entire function. The map is the published
intertwining map, with its existing coercion to a function. Its target
subgroup is literally `Subgroup.pi Set.univ P`, and its inducing action is
literally `Induction.productInducing P σ`. The latter pulls the external
tensor action back through the actual subgroup coordinate homomorphisms.
On pure tensors, the existing `finiteProductTensorMap_tprod_eval` gives

\[
\left(\operatorname{finiteProductTensorMap}
  \left(\bigotimes_i f_i\right)\right)(g)
   = \bigotimes_i f_i(g_i).
\]

Thus bijectivity concerns this prescribed map, including its established
equivariance, rather than the existence of some unspecified linear
isomorphism. It does not assert a tensor isomorphism for unrestricted
function spaces: an arbitrary function on a product need not be a finite
sum of separated functions.

All four universes `uK`, `uI`, `uG`, and `uV` remain independent. The product
group has carrier in `Type (max uI uG)`, the inducing tensor in
`Type (max uK uI uV)`, and both sides of the map in
`Type (max uK uI uG uV)`. The only index hypothesis is `[Finite ι]`.
In particular, the target includes `ι = Fin r` for every `r`, including
`r = 0`. The empty tensor and product use their existing canonical
constructions; no coordinate or nonempty index is required. It also
specializes to arbitrary complex vector spaces and any compatible actual
p-adic topologies satisfying the stated group hypotheses.

The hypotheses support a planned compact open section argument. A uniform
open right stabilizer in the finite product can be restricted along
coordinate inclusions to obtain a product of open subgroups inside it.
`Langlands.compactOpenSubgroupBasis` can shrink each factor to a compact
open subgroup. Compactness of each actual left quotient supplies a finite
double-coset cover through
`Induction.exists_finset_doubleCoset_cover`. After choosing distinct
double-coset classes, representative values determine a function at this
level, as in `Induction.fixedEvaluation_injective`.

For arbitrary inducing actions, `Induction.eval_mem_fixedVectors` puts
representative values in the required conjugate-intersection fixed spaces.
Over a field, `FiniteTensor.fixedVectors_external_le` expresses a product
invariant tensor using the factor fixed spaces without requiring those
spaces to be finite dimensional. The published
`Induction.compactDoubleCosetSection`, which does not assume a globally
smooth inducing action, constructs factor sections from such fixed
values. Finite sums of tensor products of these sections are the planned
surjectivity argument. For injectivity, a finite tensor expression can be
put at a common compact open level and expanded in sections; evaluation
of its image supplies its coefficients. These are proof obligations for
a successor, including their empty-family case, not proofs implemented
in this statement module. The supporting modules are cited by Lean name
and are not added as proof dependencies of the statement.

The provenance is derived. The registered original is I. N. Bernstein and
A. V. Zelevinsky, *Induced representations of reductive p-adic groups I*,
Ann. Sci. ENS (4) **10** (1977), 441–472, source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 1.8(a), printed p.444 / PDF p.5, defines induction with covariance
and uniform right invariance. Proposition 1.9(g), printed p.445 / PDF p.6,
states that compact induction commutes with an external tensor factor.
Proposition 1.9(e), on the same page, identifies compact and smooth
induction for compact quotients; section 2.3, printed p.446 / PDF p.7,
uses compactness of parabolic quotients. These passages were read directly,
and the retained p.445 formula was checked visually. No source-specific
errata file is present at `notes/errata/bernstein-zelevinsky-1977-induced-i.md`
in the current Library.

The original uses smooth complex representations in its stated group
setting. The finite-family formula here, its empty-family scope, its
arbitrary fields, and its arbitrary inducing actions are an internal
compact-quotient extension motivated by that compatibility, not a
verbatim finite-family statement of Bernstein–Zelevinsky. Its planned
justification is the section argument above using the published actual
map and fixed-vector constructions. The normalized refined-induction
adapter and its parent equivalence remain separate work.
