# Intertwining kernels of depth-zero compact inductions for supplied KP models

This module describes all maps between two depth-zero compact inductions
`c-Ind_{G^0(R)}^{G(K)} infl σ → c-Ind_{G^0(R)}^{G(K)} infl τ` of
`Langlands.BruhatTits.IntegralModels.DepthZeroInduction`. They correspond to
intertwining kernels on `G(K)`. When `G^0(R)` is compact and open, they also
correspond to families of local intertwiners indexed by the double cosets
`G^0(R) \ G(K) / G^0(R)`. When `σ` is finite-dimensional, each kernel is
supported on finitely many double cosets. Over a nonarchimedean local field,
all topological premises are discharged.

The module is a specialization of the published general proofs. It proves no
new representation-theoretic fact about compact induction. It supplies the
depth-zero "basic intertwining or double-coset decomposition theorem" that the
task objective asks for alongside compact induction to `G(F)`. The
Kaletha–Prasad source ledger (`notes/bruhat-tits/kp-source-ledger.md`) lists
it as open in its Section 13.2.6 consumer row.

## Provenance

The module is derived.

The general theorem is Vignéras, *Représentations ℓ-modulaires d'un groupe
réductif p-adique avec ℓ ≠ p* (Birkhäuser, 1996), Chapter I, 8.5 (printed
pp. 67–68 / PDF pp. 85–86). Its registered original has literature ID
`provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`
and SHA-256
`4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657`.
I.8.5 identifies `Hom_{RG}(ind_{G,K} σ, ind_{G,H} π)` with functions
`f : G → Hom_R(W, V)` that satisfy a) support in a finite union of double
cosets `HgK` and b) `f(hgk) = π(h) f(g) σ(k)`, through `f(g)w = (A i_w)(g)`.
The source names `K = H` as one of its two main cases. Its double-coset
decomposition appears in the proof of I.8.3 (printed p. 66 / PDF p. 84).

The Library formalizes this for one open subgroup `K = H` in three published
statements of `Langlands.Representation.Induction.OpenIntertwiningStatement`,
with the source's `(σ, W)` and `(π, V)` renamed `(σ, V)` and `(τ, W)`. Their
published proofs are:

- `Langlands.Induction.compactInductionKernel`
  (`Langlands.Representation.Induction.OpenIntertwiningKernelProof`): kernels
  for open `H`;
- `Langlands.Induction.compactInductionDoubleCoset`
  (`...OpenIntertwiningDoubleCosetProof`): the double-coset parametrization
  for compact open `H` and smooth `σ`;
- `Langlands.Induction.compactInductionFiniteTypeKernel`
  (`...OpenIntertwiningFiniteTypeProof`): the finite double-coset support
  criterion for compact open `H` and `σ` finitely generated over `R[H]`.

This module takes `H = G^0(R) = D.neutral.integralPoints`, with both
representations inflations along the published reduction map. The depth-zero
setting is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
13.2.6 (printed p. 470 / PDF p. 501), which identifies `P_{x,0}/P_{x,0+}` with
`\bar G_x(f)`. The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. KP do not
state the intertwining description of depth-zero compact inductions; this
module combines their setting with Vignéras I.8.5.

## Setting

As in `DepthZeroInduction`, `R` is a domain in universe `u` with fraction
field `K`, and `G` is a group scheme over `Spec K`. The data are
`D : RelativeComponentModelData R K G` and `Q : SpecialFibreQuotientData D`.
Write `H = D.neutral.integralPoints`. The coefficient ring `k` is any
commutative ring in any universe `uk`. The representations `σ` and `τ` of
`rationalPoints Q.quotient = \bar G(f)` act on `V` and `W` in universe `u`.

In the first part, `R` is local, and `rationalPoints G` carries an arbitrary
topology making it a topological group. The premises are:

- `hH : IsOpen (H : Set (rationalPoints G))`;
- `hK : IsCompact (H : Set (rationalPoints G))`, where it is used;
- `hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G))`, which
  the published `depthZeroInduction` needs.

`s : DoubleCoset.Quotient H H → rationalPoints G` is a choice of double-coset
representatives, with `hs : ∀ q, DoubleCoset.mk H H (s q) = q`.

The quotient hypotheses `hrad` and `hQ` of `Q.IsReductiveQuotient` are never
used, and neither is the Henselian property.

## Declarations

In namespace `Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData`:

- `depthZeroInductionKernelEquiv hH hC σ τ` (definition): an equivalence
  between morphisms `Q.depthZeroInduction hC σ ⟶ Q.depthZeroInduction hC τ`
  of smooth representations of `G(K)` and functions
  `Φ : rationalPoints G → (V →ₗ[k] W)` with
  `IsIntertwiningKernel H (Q.inflation σ) (Q.inflation τ) Φ`. That predicate
  is the covariance `Φ (h g h') = τ(h) ∘ Φ g ∘ σ(h')` for the inflations,
  together with per-vector finiteness of the right-coset support. The
  equivalence is built from `compactInductionKernel` applied to
  `Q.inflationSmoothRep hC σ` and `Q.inflationSmoothRep hC τ`. The forward
  map takes the kernel it provides. The inverse takes the unique morphism it
  provides. Both round trips follow from its uniqueness clause.
- `depthZeroInductionKernelEquiv_apply`: the kernel of `T` is
  `Φ g v = T (i_v) g`. Here `i_v` is the published
  `unitFunction H hH (Q.inflation σ) (Q.isSmooth_inflation hC σ) v`, and the
  value is read with `eval`.
- `depthZeroKernelDoubleCosetEquiv hH hK hC σ τ s hs` (definition): an
  equivalence between such intertwining kernels and families
  `φ : DoubleCoset.Quotient H H → (V →ₗ[k] W)` with
  `IsLocalIntertwinerFamily H (Q.inflation σ) (Q.inflation τ) s φ`. That
  predicate says that each `φ q` intertwines the inflation of `σ` with the
  `s q`-conjugate of the inflation of `τ` on `H ∩ (s q)⁻¹ H (s q)`, and that
  for each vector only finitely many `φ q` are nonzero on it. The forward map
  is restriction to the representatives, `Φ ↦ (q ↦ Φ (s q))`. The inverse is
  the unique extension. Both come from `compactInductionDoubleCoset`, applied
  with smoothness of the inflation (`Q.isSmooth_inflation hC σ`).
- `depthZeroInductionDoubleCosetEquiv hH hK hC σ τ s hs` (definition): the
  composite of the two equivalences. Morphisms
  `c-Ind infl σ ⟶ c-Ind infl τ` correspond to local intertwiner families on
  `G^0(R) \ G(K) / G^0(R)`.
- `depthZeroInductionDoubleCosetEquiv_apply`: the family of `T` takes the
  value `v ↦ T (i_v) (s q)` at `q`.
- `inflation_asModule_finite σ`: if `V` is a finite `k`-module, then
  `(Q.inflation σ).asModule` is a finite module over `MonoidAlgebra k H`. It
  is finite over `k`, and Mathlib's `Module.Finite.of_restrictScalars_finite`
  passes along the scalar tower `k → k[H] → asModule`. No topology is used.
- `depthZeroInductionKernel_finite_doubleCosetSupport hH hK hC σ τ T`: for
  `V` finite over `k`, the image under `DoubleCoset.mk H H` of the support of
  the kernel of `T` is finite. The kernel of every map is supported on
  finitely many double cosets `G^0(R) g G^0(R)`. This is the forward
  direction of `compactInductionFiniteTypeKernel`, applied with
  `inflation_asModule_finite`.

## Nonarchimedean local fields

Let `F` be a field with `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`. Take `R = 𝒪[F]`, `K = F`, `G` with
`IsAffine G.X.left`, and give `rationalPoints G` the canonical topology
`rationalPointTopology F G.X`. As in the sibling modules, that topology and
the group-topology instance are introduced with `letI` inside each statement,
so they are part of the statement.

- `RelativeComponentModelData.localField_isOpen_congruenceSubgroup D`: the
  level-one congruence subgroup of `D.neutral` is open. It is the published
  conditional `isOpen_congruenceSubgroup_of_congruenceBasis` applied to the
  published proof `LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof`.
  The sibling modules use the same term inline. This lemma names it so that it
  can be passed as `hC` to `depthZeroInduction` in statements.

With in addition `[LocallyOfFiniteType G.X.hom]`, so that the published
`rationalPoint_isTopologicalGroup F G` applies:

- `localFieldDepthZeroInductionDoubleCosetEquiv σ τ s hs` (definition): the
  double-coset equivalence for the canonical topology. Openness and
  compactness of `G^0(𝒪)` are the published
  `IntegralModel.isOpen_integralPoints_localField` and
  `isCompact_integralPoints_localField` for `D.neutral`. Openness of the
  congruence subgroup is the lemma above.
- `localField_depthZeroInductionKernel_finite_doubleCosetSupport σ τ`: for
  `V` finite over `k`, the kernel of every map between the two depth-zero
  compact inductions is supported on finitely many double cosets.

These local-field results are unconditional on supplied `D` and `Q`: every
premise above is a published theorem.

## Scope

`H` is `G^0(R)`, the integral points of the supplied neutral model. Nothing
here identifies it with the Bruhat–Tits parahoric subgroup `P_{x,0}`. Neither
is the kernel of the reduction identified with the Moy–Prasad subgroup
`P_{x,0+}` (KP Corollary 8.4.12). No representation is shown to be
irreducible, admissible or supercuspidal. The Hecke algebra
`End(c-Ind infl σ)` and its multiplication are not treated. The double-coset
representatives `s` are supplied; no Bruhat or Iwahori decomposition of
`G^0(R) \ G(K) / G^0(R)` is given.
