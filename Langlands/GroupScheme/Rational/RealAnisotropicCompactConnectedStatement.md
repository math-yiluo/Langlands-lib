# Real points of anisotropic reductive groups are compact and connected

`Langlands.GroupScheme.RealAnisotropicCompactConnectedStatement` is a Prop-valued
definition with no universe parameters. This module defines the proposition and
proves nothing.

## Statement

The proposition says: let `G : GroupScheme (Spec (CommRingCat.of ℝ))` be a group
scheme over `ℝ` with `[IsAffine G.X.left]`. If `IsConnectedReductive G` and
`IsAnisotropic G`, then

- `CompactSpace (RingPoint ℝ G.X ℝ)`, and
- `ConnectedSpace (RingPoint ℝ G.X ℝ)`.

In words: for a connected reductive group `G` over `ℝ` that contains no nontrivial
split torus, the group `G(ℝ)` of real points is compact and connected in the real
topology.

The ingredients are existing declarations, used without change.

- `GroupScheme S` (from `Langlands.AbelianScheme.GroupScheme`) is `Grp (Over S)`,
  a group object in schemes over `S`. `G.X.left` is the underlying scheme.
- `RingPoint ℝ G.X ℝ` (from
  [`PointTopology.ProductRingPoints`](../../AlgebraicGeometry/PointTopology/ProductRingPoints.md))
  is the set of morphisms `Spec ℝ ⟶ G.X` over `Spec ℝ`, the real points `G(ℝ)`.
- Its topology is the instance of
  [`PointTopology.AffineScheme`](../../AlgebraicGeometry/PointTopology/AffineScheme.md),
  which needs `[IsAffine G.X.left]`. It is the evaluation topology: the coarsest
  topology for which every evaluation `p ↦ p(a)` at a global function `a` is
  continuous into `ℝ`. For an affine scheme of finite type this is the subspace
  topology of `G(ℝ) ⊆ ℝⁿ` for any choice of generators. It is the same instance as
  in `Langlands.GroupScheme.RealPointComponentsStatement`.
- `IsConnectedReductive G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that `G` is smooth, affine (`IsAffineHom G.X.hom`) and connected over `ℝ`, and that
  the unipotent radical of its base change to an algebraic closure is trivial.
- `IsAnisotropic G` (from [`Rational.SplitTorus`](SplitTorus.md)) is
  `splitRank G = 0`: there is no closed-subgroup homomorphism `𝔾ₘ^I ⟶ G` with `I`
  finite and nonempty. This is the convention of Borel–Tits 4.23.
- `CompactSpace` and `ConnectedSpace` are from Mathlib. `ConnectedSpace` includes
  nonemptiness, which holds because `G(ℝ)` contains the identity.

The binder `[IsAffine G.X.left]` adds no hypothesis: `IsConnectedReductive G`
contains `IsAffineHom G.X.hom`, and `Spec ℝ` is affine, so `G.X.left` is affine
(Mathlib's `isAffine_of_isAffineHom`). The binder is needed only to form the
topology. Since `IsAffine` is a proposition, the topology does not depend on how
it is supplied.

## Provenance (derived)

Source: A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965),
registered as `borel-tits-1965-groupes-reductifs` (SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`). Printed page
= PDF page + 53.

- 9.3, printed p.126 (PDF p.73), fixes the setting of 9.3 and 9.4: « Supposons k
  localement compact de caractéristique zéro ». Here `k = ℝ` is allowed (9.1, printed
  p.126: « K est donc isomorphe à R, C ou à un corps p-adique »).
- Corollary 9.4, printed p.127 (PDF p.74): « Le groupe G_k est compact si et
  seulement si G est réductif et anisotrope sur k. » The compactness half of the Lean
  statement is the implication "reductive and anisotropic ⇒ compact" for `k = ℝ`.
- 14.3, printed p.146 (PDF p.93): « Cela implique en particulier que si G ⊂ GL(n, C)
  est connexe, défini sur R, et si G_R est compact, alors G_R est connexe. » The
  connectedness half applies this to the compact group of the first half.
- 4.23, printed p.93 (PDF p.40), defines anisotropy: « Le groupe G est anisotrope sur
  k si son k-rang est nul ». The Library's `IsAnisotropic` is this definition.
- 9.1, printed p.126, gives the topology: `V_K` carries the topology defined from
  that of `K`. For `K = ℝ` and an affine variety this is the evaluation topology
  described above.

The provenance is derived for these reasons.

- Two results are combined into one proposition. Corollary 9.4 gives compactness,
  and 14.3 deduces connectedness from compactness. The Lean statement claims nothing
  more than these two conclusions, for connected `G`.
- Borel–Tits work with linear algebraic groups over `k` (affine group varieties). A
  connected reductive group over `ℝ` in their sense is `IsConnectedReductive G` (see
  [`Reductive.Basic`](../Reductive/Basic.md)). The statement quantifies over every
  affine group scheme over `ℝ` satisfying the two hypotheses.
- The converse of 9.4 (compact ⇒ reductive and anisotropic) is not stated.
- Anisotropy follows Borel–Tits (`k`-rank zero), not Milne's Definition 25.3
  (no noncentral split torus). For example, the torus `𝔾ₘ` over `ℝ` is anisotropic
  in Milne's sense, because its split torus is central, but not in the Borel–Tits
  sense. Its real points `ℝ^×` are neither compact nor connected. So the
  Borel–Tits convention is necessary.

Errata. The only Borel–Tits 1965 erratum note in the Library,
`notes/errata/borel-tits-1965-closed-root-intersection.md`, concerns 3.22(b). It
does not affect 4.23, 9.1, 9.3, 9.4 or 14.3.

Sanity checks.

- `SO(n)` for the positive definite form over `ℝ` is connected reductive and
  anisotropic, and `SO(n)(ℝ)` is compact and connected.
- The norm-one torus `U(1) = ker(N : R_{ℂ/ℝ} 𝔾ₘ → 𝔾ₘ)` is anisotropic, and
  `U(1)(ℝ)` is the circle.
- The norm-one group `SL₁(ℍ)` of Hamilton's quaternions is anisotropic, and its real
  points form `SU(2)`, the 3-sphere.
- Connectedness of `G` is needed. The disconnected group `O(n)` of a positive
  definite form has compact but disconnected real points; it is not
  `IsConnectedReductive`.
- Anisotropy is needed for compactness: `SL₂(ℝ)` and `ℝ^×` are not compact.

Relation to the Library.

- `Langlands.GroupScheme.RealAnisotropicPointsCompactnessStatement` (module
  [`Rational.RealAnisotropicPointsCompactnessStatement`](RealAnisotropicPointsCompactnessStatement.md),
  sourced from Suzuki 1971, Remark 2) is a statement without proof in the Library. It asserts
  compactness only, only for semisimple `G` (`IsSemisimple G`), and it is phrased on
  `rationalPoints G` with the topology `rationalPointTopology ℝ G.X`. The present statement
  covers all connected reductive `G` and adds connectedness. Deducing that statement from this
  one would require identifying the two point spaces and their topologies; this module does not
  do it.
- `Langlands.GroupScheme.isAnisotropic_of_hasCompactRealPoints` (module
  [`Rational.RealCompactPoints`](RealCompactPoints.md)) proves the converse direction:
  compact real points imply anisotropy. The converse is not part of the present statement.
- `Langlands.GroupScheme.AnisotropicCompactnessStatement` (module
  `Langlands.GroupScheme.Rational.AnisotropicCompactnessStatement`) and
  `Langlands.GroupScheme.AnisotropicPointsCompactnessStatement` concern non-archimedean local
  fields only.

## Intended use

This proposition is the anisotropic step of Matsumoto's theorem (Borel–Tits 14.4,
printed pp.146–147). For a reductive group `G` over `ℝ` with maximal split torus `S`,
`Z_G(S)/S` is connected reductive and anisotropic, so its real points are connected.
That gives `Z_G(S)(ℝ) = Z_G(S)(ℝ)° · S(ℝ)`, which feeds the proof of
`Langlands.GroupScheme.RealPointComponentsStatement`.

## Proof

This module proves nothing. A proof is in the module
`Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedProof`
(declaration `Langlands.GroupScheme.realAnisotropicCompactConnected`).
