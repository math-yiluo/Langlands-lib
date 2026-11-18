# Smooth torus-subgroup moduli for groups with affine fibres

Authors: Worker 606 (draft) and Worker 175.

`Langlands.GroupScheme.TorusSubgroupModuli.SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u}`
is a proposition about every scheme `S : Scheme.{u}` and every actual group
scheme `G : GroupScheme S`. There is no restriction on the base: it need not be
affine, Noetherian, reduced or a field, and no dimension is fixed. Lean schemes
are not assumed separated, so they are SGA's préschémas.

## Hypotheses

- `Smooth G.X.hom`: the structure morphism is smooth in Mathlib's sense, so it is
  locally of finite presentation.
- `IsSeparated G.X.hom` and `QuasiCompact G.X.hom`. A separated morphism is
  quasi-separated, so together with smoothness these make `G → S` smooth and of
  finite presentation.
- For every point `s : S`, the actual residue fibre
  `RelativeIdentityComponent.residueFiber G s` is affine. This fibre is the base
  change of `G` along `Spec κ(s) → S`, so the condition says exactly that the fibre
  `G_s = G ×_S Spec κ(s)` is an affine `κ(s)`-scheme. The fibre at any other field
  point `Spec K → S` with image `s` is the base change of `G_s` along
  `Spec K → Spec κ(s)`, so it is affine as well.

No affineness, quasi-projectivity or connectedness of `G → S` itself is assumed.

## Conclusion

The proposition asks for a scheme `M` over `S`, an actual group scheme `K` over
`M` and an actual homomorphism `j : K ⟶ G_M`, where
`G_M = (GroupScheme.baseChange M.hom).obj G`, such that:

- `IsClosedSubgroup j`: the underlying morphism of schemes of `j` is a closed
  immersion;
- `RelativeTorus.IsTorus K`: on some jointly surjective étale cover of `M`, `K`
  becomes a split torus. The rank may differ between members of the cover, and
  rank zero is allowed;
- `TorusSubgroupModuli.IsUniversal j`: for every scheme `T` over `S` and every
  subgroup functor `F` of `G_T` that is represented by an actual closed
  relative-torus subgroup (`TorusSubgroupModuli.IsAdmissible F`), there is a
  unique morphism `a : T ⟶ M` over `S` with `TorusSubgroupModuli.evaluate j a = F`;
- `Smooth M.hom`: `M` is smooth over `S`.

`evaluate j a` is the literal range of `familyHom j a`. That homomorphism is the
pullback of `j` along `a.left`, followed by the specified comparison
`Descent.pullbackComparison` between the iterated pullback of `G` and its direct
pullback `G_T`. The equality `evaluate j a = F` is an equality of subgroup
functors, so it holds on every scheme over `T`, including nonaffine and nonreduced
tests. Because `j` is a closed relative-torus subgroup, every evaluation is
itself admissible (`TorusSubgroupModuli.isAdmissible_evaluate`). The conclusion
therefore says that `M`, with universal subgroup `j`, represents the functor
taking a scheme `T` over `S` to the set of closed subtori of `G_T`. Test schemes
are taken in the same universe `u` as `S`.

The proposition does not claim that `M → S` is separated, quasi-compact or
affine.

## Original source

M. Raynaud, SGA 3, Exposé XV, *Compléments sur les sous-tores d’un préschéma en
groupes. Application aux groupes lisses*, Gille–Polo recomposition dated
1 December 2008, Corollary 8.11, one-based PDF page 63 of `Expo15.pdf`
(recomposed page 295, original page 474). Registered source
`sga3-expose-xv-raynaud-2008`, SHA-256
`03647e0232067a7508bb1350e7aace3e88d58872956f068ced808a4f9cc3273f`.

Corollary 8.11 takes an arbitrary préschéma `S` and an `S`-group `G` that is
smooth and of finite presentation over `S`. If the abelian rank of the fibres of
`G` is a locally constant function on `S`, "in particular if the fibres of `G`
are affine", then the functor of subtori of `G` is representable by an
`S`-scheme that is smooth and separated over `S`. The same holds for
`Hom_{S-gr}(T, G)` for every `S`-torus `T`.

## Comparison with the source

Hypotheses. The Lean hypotheses give smoothness and finite presentation, as
explained above. Affineness of every fibre is the special case that the
corollary names explicitly. Separatedness of `G → S` is an added hypothesis
that the corollary does not require. It is used in the identification of
subtori below.

Subtori. A subtorus of `G_T` in SGA 3 is a subgroup scheme of `G_T` that is a
torus. The Lean functor counts only closed subgroup schemes. Since `G_T` is
separated and of finite presentation over `T`, the two notions agree.
SGA 3, Exposé VIII, Proposition 7.12 shows that a monomorphism of group schemes
`H → G_T` is a closed immersion when both are of finite presentation, `H` is
flat, and, locally at each point, `H` is commutative with smooth closed fibre,
its `n`-torsion subgroups are finite and those of `G_T` are separated, for all
`n > 0`. A torus satisfies the conditions on `H`. Separatedness of `G_T`
supplies the condition on `G_T`. The proof of Exposé XV, Theorem 3.1 B) uses
the same reference to conclude that a subtorus of a separated group is closed.
Without separatedness of `G`, a subtorus in the sense of the source need not be
closed.

Tori. SGA 3, Exposé IX, Definition 1.3 defines a torus as a group that is
locally isomorphic, for the fpqc topology, to `G_m^r` for an integer `r ≥ 0`. The
rank is a locally constant function of the point. Exposé X, Corollary 4.5 says
that a group of multiplicative type and of finite type is split by an étale
surjective morphism. Hence every torus in the sense of the source satisfies
`RelativeTorus.IsTorus`. Conversely, a jointly surjective étale family is an
fpqc covering, so a group satisfying `RelativeTorus.IsTorus` is a torus in the
sense of the source.

Conclusion. The corollary gives a representing scheme that is smooth and
separated over `S`. The proposition asks only for smoothness. It omits
separatedness of `M` and the assertion about `Hom_{S-gr}(T, G)`.

So the proposition is a specialization of Corollary 8.11. It adds separatedness
of `G`, restricts the abelian-rank hypothesis to affine fibres, and keeps only
the smoothness part of the representability conclusion.

Further citations:

- SGA 3, Exposé VIII, Proposition 7.12, Gille–Polo recomposition of
  8 November 2009, one-based PDF page 29 of `Exp8-8nov09.pdf`, registered source
  `sga3-expose-viii-gille-polo-2009` (SHA-256
  `06e43e0571d411cc5579975778fcc03c8ecaa67189248d1a053e61dc653af510`).
- SGA 3, Exposé XV, Theorem 3.1 B) and its proof, PDF pages 15–17 of the same
  `Expo15.pdf`; the reference to VIII 7.12 is on PDF page 17.
- SGA 3, Exposé IX, Definition 1.3, PDF page 2, recomposed page 32, registered
  source `sga3-expose-ix-gille-polo-2009`.
- SGA 3, Exposé X, Corollary 4.5, PDF page 17, registered source
  `sga3-expose-x-gille-polo-2009`.

No source-specific errata file for these sources was found in the consulted
Library.

## Scope of this module

This Lean module defines only the proposition. It proves neither
representability nor any of the comparisons above. A proof must construct the
universal family and establish smoothness and the all-test universal property
from the stated hypotheses. The existing proof of
`TorusSubgroupModuli.SmoothTorusSubgroupRepresentabilityStatement` does not
apply: that statement assumes `IsAffineHom G.X.hom`, and its proof uses affine
Hopf-algebra coordinates. The intended consumer is the proof of
`Langlands.GroupScheme.ReductiveFiberAffinenessStatement`, where affineness of
each fibre is available. This proposition does not assert that the ambient group
scheme is affine.
