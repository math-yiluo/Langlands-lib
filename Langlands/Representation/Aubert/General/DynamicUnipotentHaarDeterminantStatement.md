# Haar scaling on a rational dynamic unipotent subgroup is the adjoint determinant

Author: Worker 1415.

`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentHaarDeterminantStatement`
is a proposition definition awaiting proof. Over a nonarchimedean local field,
it asserts that conjugation by a rational point `m` of the centralizer of a
cocharacter scales Haar measure on the rational points of the dynamic
unipotent subgroup by the normalized absolute value of
`det(Ad m | Lie U(χ))`. It supplies no proof or additional axiom.

## Scope and actual objects

- `k : Type u` is any nonarchimedean local field, given by
  `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]`.
  Positive characteristic is included.
- `G` is any group scheme over `Spec k` with `hG : IsConnectedReductive G`.
  The local instance `hG.isAffineHom` supplies affineness of `G`. This is the
  same binder form as in
  `Langlands.Aubert.General.RationalPointFamily.RationalOppositeHaarReciprocityStatement`.
- `RationalPoint k G.X` carries the canonical `pointTopology`. Local
  compactness, the nonarchimedean group property and Hausdorffness of this
  topology are displayed hypotheses, as in that statement.
- `χ : (Gm (Spec k)).toGrp ⟶ G` is any cocharacter of `G`. It need not factor
  through a split torus or be standard, and the trivial cocharacter is
  allowed.
- `Z` with `iZ` is any group scheme representing the subgroup functor
  `Dynamic.centralizer χ` (premise `hZ`). `U` with `iU` is any group scheme
  representing `Dynamic.unipotent χ` (premise `hU`). The instance premises
  `[IsAffine Z.X.left]` and `[IsAffineHom U.X.hom]` are those under which the
  Library forms determinant characters of actions on Lie algebras.
- `c : Lie.FiniteCoordinates U d` is any finite coordinate system on the Lie
  module of `U`. It is a family of `A`-linear isomorphisms
  `Lie(U)(A) ≃ A^d`, one for each `k`-algebra `A`, natural in `A`. Here
  `Lie(U)(A)` is the kernel of `U(A[ε]) → U(A)`.
- `hUc` is the displayed premise that the rational-point subgroup
  `(Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))`, written `U(χ)(k)`, is
  closed in `G(k)`. Closedness supplies local compactness inside the Haar
  character.
- `m : rationalPoints Z` is any `k`-point of `Z`, and `m ≫ iZ.hom.hom` is its
  image in `G(k)`. The premise `hm` states that this image normalizes
  `U(χ)(k)`. This is needed to form the character. The Library's
  `range_unipotent_isNormalizedBy_range_centralizer` records the
  scheme-level normalization.

The premises can be met for actual objects. `Dynamic.Affine.centralizerHom`
and `Dynamic.Affine.unipotentHom` represent the two subgroup functors. The
proved `dynamicAdjointDeterminantStructure` supplies the affineness
instances and the existence of finite coordinates over a field. The
remaining premises `hUc` and `hm` are properties of the actual subgroups and
the actual point. The proposition is therefore not vacuous.

## Conclusion and conventions

Let `g = m ≫ iZ.hom.hom`. The left side is the value at `g` of
`HaarModulus.closedNormalizerCharacter` of the closed subgroup `U(χ)(k)`,
coerced to `ℝ≥0`. It is `mulEquivHaarChar` of `u ↦ g u g⁻¹` on `U(χ)(k)`.
The Library's `normalizerCharacter_smul_map` states
`c(g) • map (u ↦ g u g⁻¹) μ = μ` for a Haar measure `μ` on `U(χ)(k)`. Hence
`c(g)` is the forward volume scaling factor:
`μ(g S g⁻¹) = c(g) μ(S)`.

On the right, `δ = (Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c`
is the rational character of `Z` given by the determinant of the Library's
actual action `m • u = m u m⁻¹` of `Z` on `U`, differentiated on `Lie(U)` and
read in the coordinates `c`. `rationalCharacterEval δ m : kˣ` is its value at
the rational point `m`, the determinant `det(Ad m | Lie U(χ))`.
`MeasureTheory.distribHaarChar k : kˣ →* ℝ≥0` is Mathlib's Haar scaling
character of `kˣ` acting on `k` by multiplication. By `distribHaarChar_mul`,
`distribHaarChar k a * μ_k(s) = μ_k(a • s)` for a Haar measure `μ_k` on `k`.
It is the forward scaling factor of multiplication by `a`, classically the
normalized absolute value `|a|_k`. No absolute value is chosen in the
statement. The conclusion is

`μ(g S g⁻¹) / μ(S) = |det(Ad m | Lie U(χ))|_k`,

stated as the equality of `closedNormalizerCharacter` and
`distribHaarChar k ∘ rationalCharacterEval δ` at `m`. Both sides have the
forward orientation. The Library's `adjointDeterminantModelIndependence`
shows that the right side does not depend on the chosen models and
coordinates.

## Original sources and provenance

Provenance: derived.

Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter III, revision of April 29, 2019, source
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Section 1, p. 1 (PDF p. 1), defines normalized induction by
`f(pg) = δ_P^{1/2}(p) σ(p) f(g)` and states:

"Here δ_P(p) = |det_n(p)| is the modulus character of P."

Here `n` is the Lie algebra of the unipotent radical `N` of the parabolic
subgroup `P = MN` of the rational points of a connected reductive group.
The present statement takes from this formula only the scaling of Haar
measure on `N` under conjugation by `M`. It says nothing about Mathlib's
modular character of `P`.

David Renard, *Représentations des groupes réductifs p-adiques*, 2026
version, source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
Section V.5.4, printed pp. 126–127 (PDF pp. 132–133). For `a` in the split
component `A` of `M`, the proof of the Lemme computes Renard's `δ_P(a)` as
an index ratio of compact open subgroups of `N`:

"δ_P(a) = [a⁻¹K_N a : K_{1,N}] / [K_N : K_{1,N}]" and
"δ_P(a) = ∏_{γ ∈ Σ(P)} |γ(a)^{-(m_γ+2m_{2γ})}|_F".

It also notes `δ_P(a) = δ_N(a)`. Renard's convention is
`∫ f(a p a⁻¹) dμ_P(p) = δ_P(a) ∫ f(p) dμ_P(p)`, so `δ_N(a)` is the inverse of
the forward factor `c(a)` above. The source therefore gives
`c(a) = ∏_{γ ∈ Σ(P)} |γ(a)|^{m_γ + 2m_{2γ}}`. This is the absolute value of
`det(Ad a | Lie N)`. Indeed `Lie N` is the sum of the root spaces of `A`, and
Renard's exponent `m_γ + 2m_{2γ}` collects the root spaces of `γ` and `2γ`
with their multiplicities.

The Lean statement is derived from these sources in the following ways.

- It is stated for every cocharacter `χ` of `G` and its dynamic subgroups
  `Z(χ)` and `U(χ)`, not only for standard parabolic subgroups. These
  subgroups are defined in Conrad, Gabber and Prasad, *Pseudo-reductive
  groups*, second edition, source `conrad-gabber-prasad-2015-pseudo-reductive`,
  SHA256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
  Lemma 2.1.5, printed p. 50 (PDF p. 76). Proposition 2.1.8(1), printed
  p. 53 (PDF p. 79), identifies `Lie(U_G(λ))` with the positive weight part
  `g_+` of `Lie(G)`.
- It is stated for every rational point of `Z(χ)`, not only for the split
  component.
- The determinant is the Library's algebraic determinant character of the
  adjoint action, evaluated at a rational point.
- The absolute value is Mathlib's `distribHaarChar k`, the Haar scaling of
  multiplication on `k`.

The rational-point and canonical-topology formulation is internal.

## Intended use

Together with the separate proposition
`Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement`,
this statement is intended as an input to a proof of
`Langlands.Aubert.General.RationalPointFamily.RationalOppositeHaarReciprocityStatement`.
That separate proposition says that the adjoint determinants on `Lie U(χ)`
and `Lie U(χ⁻¹)` are inverse characters of the common centralizer. That
derivation is not part of this statement.
