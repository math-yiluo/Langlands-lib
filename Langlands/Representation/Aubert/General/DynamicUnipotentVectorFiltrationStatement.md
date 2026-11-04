# A vector filtration of a rational dynamic unipotent subgroup with adjoint determinant

Author: Worker 1423.

`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`
is a proposition definition awaiting proof. Over a nonarchimedean local field
`k`, it asserts that the rational points `U(χ)(k)` of the dynamic unipotent
subgroup of a cocharacter `χ` have a finite filtration by subgroups normalized by
a given rational point `m` of the centralizer `Z(χ)`, whose successive quotients
are identified, topologically and `m`-equivariantly, with coordinate spaces
`k^(n r)` on which `m` acts linearly, and that the product of the determinants
of these linear actions is `det(Ad m | Lie U(χ))`. It supplies no proof and no
axiom. It imports `Langlands.Representation.Aubert.General.RationalPointFamily`,
`Langlands.GroupScheme.Dynamic.CentralizerAdjointAction`,
`Langlands.GroupScheme.Lie.ActionDeterminant`,
`Langlands.GroupScheme.Reductive.Basic` and
`Mathlib.NumberTheory.LocalField.Basic` unchanged.

## Binders

The binders are those of the Library statement
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentHaarDeterminantStatement`
without its two premises `hUc` (closedness of `U(χ)(k)`) and `hm`
(normalization of `U(χ)(k)` by the image of `m`).

- `k : Type u` is any nonarchimedean local field, given by
  `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]`.
  Positive characteristic is included.
- `G` is any group scheme over `Spec k` with `hG : IsConnectedReductive G`; the
  local instance `hG.isAffineHom` supplies affineness.
- `RationalPoint k G.X` carries the canonical `pointTopology`. Local
  compactness, the nonarchimedean group property and Hausdorffness of this
  topology are displayed instance hypotheses, as in the statement above.
- `χ : (Gm (Spec k)).toGrp ⟶ G` is any cocharacter of `G` (the trivial one is
  allowed).
- `Z` with `iZ` represents `Dynamic.centralizer χ` (premise `hZ`), and `U` with
  `iU` represents `Dynamic.unipotent χ` (premise `hU`). The instances
  `[IsAffine Z.X.left]` and `[IsAffineHom U.X.hom]` are those under which the
  Library forms determinant characters of actions on Lie modules.
- `c : Lie.FiniteCoordinates U d` is any finite coordinate system on the Lie
  module of `U`: `A`-linear isomorphisms `Lie(U)(A) ≃ A^d`, natural in the
  `k`-algebra `A`.
- `m : rationalPoints Z` is any `k`-point of `Z`. Write `g = m ≫ iZ.hom.hom`
  for its image in `G(k)`.

As in the statement above, the premises can be met for actual objects:
`Dynamic.Affine.centralizerHom` and `Dynamic.Affine.unipotentHom` represent the
two subgroup functors, and the proved `dynamicAdjointDeterminantStructure`
supplies the affineness instances and finite coordinates over a field.

## Conclusion

Write `U(χ)(k)` for the subgroup
`(Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))` of `RationalPoint k G.X`.
The conclusion asserts the existence of

- a length `N : ℕ` and subgroups `F : ℕ → Subgroup (RationalPoint k G.X)`,
- dimensions `n : ℕ → ℕ`,
- maps `q r : F r → (Fin (n r) → k)`, where `F r` has the subspace topology of
  `G(k)` and `k^(n r)` the product topology,
- `k`-linear automorphisms `L r` of `k^(n r)`,

such that

1. `F 0 = U(χ)(k)` and `F N = ⊥`;
2. `F (r + 1) ≤ F r` for `r < N`;
3. `g` normalizes `F r` for `r < N`;
4. for `r < N`, `q r` is a homomorphism from the group `F r` to the additive
   group of `k^(n r)` (`q r (x * y) = q r x + q r y`) whose kernel is exactly
   `F (r + 1)`, and `q r` is continuous, open and surjective;
5. for `r < N`, `L r` is induced by conjugation by `g`: if `x, y ∈ F r` and
   `y = g x g⁻¹` in `G(k)`, then `q r y = L r (q r x)`;
6. `∏_{r < N} det (L r) = rationalCharacterEval δ m` in `kˣ`, where
   `δ = (Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c`.

In item 6, `Dynamic.centralizerAdjointAction hZ hU` is the Library's action
`m • u = m u m⁻¹` of `Z` on `U`, and `determinantCharacter c` is the rational
character of `Z` given by the determinant of its differential on `Lie(U)`, read
in the coordinates `c`. Its value `rationalCharacterEval δ m : kˣ` at `m` is the
determinant `det(Ad m | Lie U(χ))`; by the Library's
`adjointDeterminantModelIndependence` it does not depend on the chosen models
and coordinates. The left side is a product in `kˣ` over `Finset.range N`.

Items 1–5 are exactly the hypotheses `_hF0`, `_hFN`, `_hFle`, `_hFg`,
`_hqmul`, `_hqker`, `_hqc`, `_hqo`, `_hqs` and `_hqL` of the separate
proposition `Langlands.HaarModulus.VectorFiltrationHaarModulusStatement` for the
subgroup `U(χ)(k)` and the element `g`. The map `L r` is determined by `q r`,
since `q r` is surjective; so item 6 is a genuine condition on the filtration.

## Original sources and provenance

Provenance: derived.

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*, second
edition, source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

- Lemma 3.3.8, printed pp. 111–112 (PDF pp. 137–138), for a split torus `S`
  acting on a smooth affine group and a nonzero character `a`, says: "For
  A = ⟨a⟩ with a ∈ X(S)−{0}, each U_{A^j}(G) is normal in U_A(G) and the
  quotient V_j = U_{A^j}(G)/U_{A^{j+1}}(G) is a vector group such that
  Ψ(V_j, S) = {ja} if V_j ≠ 0. In particular, V_j has a unique S-equivariant
  linear structure." Here `A^j` consists of the characters `na` with `n ≥ j`.
  Apply it to `S = GL_1` acting on `G` through conjugation by `χ` and to `a`
  the identity character. The existence proof of Proposition 3.3.6, printed
  pp. 109–110 (PDF pp. 135–136), constructs `H_⟨a⟩(G)` as `U_{G^{M_a}}(λ)` with
  `M_a = ker a` and `λ` inverse to `a`; here `M_a` is trivial, so
  `U_A(G) = U_G(χ)`. The `U_{A^j}(G)` then form a decreasing filtration of
  `U_G(χ)` by normal subgroups whose quotients are vector groups of pure
  weight `j`.
- Proposition 2.1.8(1), printed p. 53 (PDF p. 79), says
  "Lie(U_G(±λ)) = g_±", where `g_+` is the sum of the weight spaces `g_n`,
  `n > 0`, of `Lie(G)` under `t.v` induced by `λ(t) g λ(t)⁻¹`.

The statement is derived from these results in the following ways.

- The filtration is passed to `k`-points. Surjectivity of `q r` on `k`-points,
  its continuity and its openness for the canonical topology are consequences
  that the sources do not state; they hold because each step of the filtration
  splits as a scheme into the next step times a vector group.
- The action of the centralizer `Z(χ)` on each quotient `V_j` commutes with the
  `GL_1`-action, and an endomorphism of a vector group of pure nonzero weight
  that commutes with the weight action is linear. So `m` acts on `V_j(k)` by a
  linear map, the restriction of `Ad m` to the weight space `g_j` (Proposition
  2.1.8(1) and the identification `Lie(V_j) = g_j`). The determinant of `Ad m`
  on `g_+ = ⊕_j g_j` is the product of these determinants; this is item 6.
- The statement uses the Library's rational-point, canonical-topology and
  determinant-character formulations; these are internal.

## Intended use

Together with `Langlands.HaarModulus.VectorFiltrationHaarModulusStatement` and
the Library's `Langlands.BruhatTits.dynamicUnipotentCompactOpenContainment`
(every element of `U(χ)(k)` lies in a compact open subgroup), this statement is
intended to prove
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentHaarDeterminantStatement`:
the forward Haar scaling factor of conjugation by `g` on `U(χ)(k)` is
`distribHaarChar k` of `∏_{r < N} det (L r) = det(Ad m | Lie U(χ))`. That
derivation is not part of this statement.
