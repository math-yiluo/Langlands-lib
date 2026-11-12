# Reductivity from an affine homogeneous quotient, conditional on geometric reductivity

Authors: Worker 1497, Worker 1502 and Worker 4246.

This module proves two results, a theorem and a proof-producing `def`. Both
take as a hypothesis the published proposition
`ReductiveGeometricReductivityStatement.{u}` (Haboush's theorem, module
`Langlands.GroupScheme.Reductive.GeometricReductivityStatement`). This module
does not prove that proposition. Applied to a proof of it, the `def` gives an
unconditional proof of the published target
`AffineHomogeneousQuotientReductiveStatement.{u}`
(module `Langlands.GroupScheme.Reductive.AffineHomogeneousQuotientStatement`),
which is unchanged.

`affineHomogeneousQuotientReductive_of_geometricReductivity` is an internal
proof-producing `def` whose type is the implication from Haboush's theorem to
the target (the `linter.defProp` linter is disabled for it), so that the module
can be published as a definition artifact before Haboush's theorem is proved;
it is used exactly like a theorem.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), proof of
Proposition A.8.12, printed pp.552–553 (PDF pp.578–579), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`. The proof first says “We may and do
assume that k = k̄.” It then states: “In general, the identity component of a
smooth closed k-subgroup G′ of G is reductive if G/G′ is affine.” For a proof it
cites [Bo1, Thm. 1.1(i)] or [Ri, Thm. A], and notes that Richardson's proof uses
Mumford's conjecture, which Haboush proved. The proof implemented here is the
project's own route, derived from Library results. It uses Haboush's theorem only
through the hypothesis `hHab`. It does not transcribe Borel's or Richardson's
argument.

## `hasTrivialUnipotentRadical_identityComponent_of_geometricReductivity`

```
theorem hasTrivialUnipotentRadical_identityComponent_of_geometricReductivity
    (hHab : ReductiveGeometricReductivityStatement.{u})
    {K : Type u} [Field K] [IsAlgClosed K] {G H : GroupScheme (Spec (CommRingCat.of K))}
    (hG : IsPseudoReductive G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i)
    (hQ : IsAffineHom Q.scheme.hom) :
    HasTrivialUnipotentRadical (identityComponent H)
```

This is the algebraically closed case. Here `K` is algebraically closed and `G` is
pseudo-reductive over `K` (smooth, affine, connected, with trivial `K`-unipotent
radical). `i : H ⟶ G` is a closed subgroup with `H` smooth and affine; `H` need
not be connected. `Q` is an actual homogeneous quotient of `G` by `H` with
`IsAffineHom Q.scheme.hom`. The conclusion is the trivial unipotent radical of
the published `identityComponent H`.

Proof. Unfold `HasTrivialUnipotentRadical`. Let `i' : N ⟶ identityComponent H` be
a closed subgroup with `N` smooth, connected and unipotent and with normal range.
We show that the range of `i'` is `⊥`. Suppose it is not.

1. `j = i' ≫ identityComponentι H ≫ i` is a composite of three closed immersions,
   using the published `IdentityComponent.isClosedSubgroup_identityComponentι`.
   So `N` is affine and `j` is a monomorphism. The published
   `smoothSubgroupQuotientExistence` gives an actual homogeneous quotient `QN` of
   `G` by `j`.
2. `HomogeneousQuotientTower.isAffineHom_of_normal_identityComponent` makes `QN`
   affine, since `N` is normal in `H⁰`, `H⁰` is normal in `H`, and `Q` is affine.
3. Since the range of `i'` is not `⊥`, some point `n` of `N` over some test scheme
   is not `1`. Otherwise every point of the range would be the image of `1`, and
   the range would be `⊥`.
4. Let `χ` be any natural additive function on the points of `N`.
   `HomogeneousQuotientAdditiveCocycle.exists_leftTranslate_of_isAffineHom`,
   applied to the affine quotient `QN`, gives a global function `f` on `G` with
   `f((n ≫ j) · x) = f(x) + χ(n)` for all points `n` of `N` and `x` of `G`.
5. `AdditiveShift.false_of_shift_functions` takes `hHab`, the pseudo-reductivity
   of `G`, the unipotence of `N`, the homomorphism `j`, the nontrivial point of
   step 3, and the functions of step 4. It gives `False`.

## `affineHomogeneousQuotientReductive_of_geometricReductivity`

```
def affineHomogeneousQuotientReductive_of_geometricReductivity
    (hHab : ReductiveGeometricReductivityStatement.{u}) :
    AffineHomogeneousQuotientReductiveStatement.{u}
```

This passes from an arbitrary field to an algebraic closure. Let `k` be a field,
`G` a connected reductive group over `Spec k` (`hG`), and `i : H ⟶ G` a closed
subgroup (`hi`) with `H` smooth (`hH`). The proof first introduces the local
instances of the target: `Smooth H.X.hom`, `IsAffineHom G.X.hom` (from
`hG.isAffineHom`), `IsClosedImmersion` for `i`, and `IsAffineHom H.X.hom` (the
composite of the closed immersion with the affine structure map of `G`,
rewritten by `Over.w`). Let `Q` be an actual homogeneous quotient of `G` by `H`
with `hQ : IsAffineHom Q.scheme.hom`.

Write `b = toAlgebraicClosure k`, and `G_k̄`, `H_k̄`, `i_k̄` for the base changes
along `b` of `G`, `H` and `i`.

1. `G_k̄` is pseudo-reductive, by the published
   `IsConnectedReductive.baseChange_toAlgebraicClosure` followed by
   `IsConnectedReductive.isPseudoReductive`.
2. `H_k̄` is smooth by the published `IdentityComponent.smooth_baseChange`.
   `i_k̄` is a closed subgroup by the published `IsClosedSubgroup.baseChange`.
   So `H_k̄` is affine: compose the closed immersion `i_k̄` with the affine
   structure map of `G_k̄` and rewrite by `Over.w`.
3. The published quotient transport `Q.baseChange b` is an actual homogeneous
   quotient of `G_k̄` by `H_k̄`. The published `Q.baseChange_isAffineHom b hQ`
   makes it affine.
4. The algebraically closed case above, applied to these data, gives
   `HasTrivialUnipotentRadical (identityComponent H_k̄)`.
5. The published `IdentityComponent.baseChangeIso H (algebraMap k k̄)` identifies
   the base change of `identityComponent H` along `b` with
   `identityComponent H_k̄`. The published `HasTrivialUnipotentRadical.of_iso`
   transports step 4 along it. This is the field
   `hasTrivialGeometricUnipotentRadical` of `IsConnectedReductive`.
6. The other fields of `IsConnectedReductive (identityComponent H)` are the
   published instances for smoothness, affineness and connectedness of the
   identity component.

## Scope

Both results are conditional on `ReductiveGeometricReductivityStatement.{u}`.
No other unproved proposition is assumed. In particular, neither the quotient
existence for `N` nor the affineness of `G/N` is assumed: both are proved from
Library results inside the first theorem.
