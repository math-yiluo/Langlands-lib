# Iwasawa bounds for the adjoint determinant of a dynamic parabolic

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicDeterminantLine`,
namespace `Langlands.GroupScheme.Dynamic`.

## Purpose and provenance

Provenance: internal. In the convergence proof of the standard intertwining integrals
(Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*
(2003), II.2, II.3.4 and IV.1.1, printed pp. 253–257 and 277–281), the Levi component of a
point of `Ū(F) ∩ U'(F)` is controlled through the modulus characters of parabolics, which act on
the top exterior power of the Lie algebra of their unipotent radicals. This module applies the
public eigenline bounds (`EigenlineIwasawaBounds`) to that determinant line, as constructed in the
public module `AdjointDeterminantLine`. The result is a uniform lower bound for
`|det(Ad(m) | Lie U(ψ))|` at Levi components `m`, for every parabolic `P(ψ)` that contains the
relevant Levi and a parabolic whose unipotent radical contains the point. The arguments are
derived from Library results and are not transcribed from the source.

## Setting and notation

- `k` is a field and `G`, `P`, `U` are group schemes over `Spec k`. `χ : 𝔾_m ⟶ G` is a
  cocharacter. `hP : (parabolic χ).IsRepresentedBy iP` and `hU : (unipotent χ).IsRepresentedBy iU`
  say that `iP : P ⟶ G` and `iU : U ⟶ G` represent the dynamic parabolic `P(χ)` and its dynamic
  unipotent subgroup `U(χ)`. `G` and `U` have affine structure maps and `P` is affine.
- `cG : Lie.FiniteCoordinates G N` and `cU : Lie.FiniteCoordinates U d` are natural finite
  coordinates on the Lie algebras. `adjointExteriorRepresentation cG` is the exterior power of
  degree `d` of the adjoint representation of `G`, and
  `adjointExteriorCoordinates cG cU iU A` is the coordinate vector of the wedge of the image of
  `Lie U` in it (both public, `AdjointDeterminantLine`).
- `adjointDeterminantCharacter hP hU cU : rationalCharacters P` is the algebraic character
  `det(Ad | Lie U(χ))` of `P` (public, `AdjointDeterminant`), and `rationalCharacterEval` is its
  value on rational points.
- In the local-field part `F` is a nonarchimedean local field, `ψ` replaces `χ` as the cocharacter
  defining `P` and `U`, `G` is affine and locally of finite type, `|·|` is
  `LocalField.residueNormalizedAbsoluteValue F` and `G(F)` carries `rationalPointTopology F G.X`.
  `Z(χ₀)`, `U(χ₀)`, `P(θ)` and `U(θ)` are the dynamic centralizer, unipotent subgroup and
  parabolic of further cocharacters `χ₀`, `θ` of `G`, and `(·).rationalPoints` is the subgroup of
  rational points.

## Declarations

- `rationalPointEquiv_map`: the affine point over `k` of the image of `x ∈ P(k)` in `G(k)` is the
  affine point of `x` composed with `iP`.
- `adjointExteriorCoordinates_rational_action`: for `x ∈ P(k)`, the exterior matrix of the image
  of `x` sends `v = adjointExteriorCoordinates cG cU iU k` to `det(Ad(x) | Lie U(χ)) • v`.
- `rationalPoints_map_injective`: the point map `P(k) → G(k)` of `iP` is injective.
- `adjointDeterminantPointValue iP c` (definition): for a rational character `c` of `P`, the
  function `G(k) → k` sending `g` to the value of `c` at the chosen preimage
  `Function.invFun (rationalPoints.map iP) g`. Only its values on the image of `P(k)` matter.
- `adjointDeterminantPointValue_map`: its value at the image of `q ∈ P(k)` is the value of `c`
  at `q`.
- `isEigenvectorOn_adjointExteriorCoordinates`: `v` is an eigenvector of the exterior
  representation on `P(χ)(k)` (`MatrixRepresentation.IsEigenvectorOn`), with eigenvalue function
  `adjointDeterminantPointValue iP (adjointDeterminantCharacter hP hU cU)`.
- `exists_le_abs_adjointDeterminant` (main result): assume
  `Z(χ₀)(F) ≤ P(ψ)(F)` and `P(θ)(F) ≤ P(ψ)(F)`, and let `K ⊆ G(F)` be compact. Then there is
  `C > 0` such that for all `x, m, u, κ ∈ G(F)` and `q ∈ P(F)` with `x ∈ U(θ)(F)`,
  `m ∈ Z(χ₀)(F)`, `u ∈ U(χ₀)(F)`, `κ ∈ K`, `x = m u κ` and image of `q` equal to `m`,
  `C ≤ |det(Ad(q) | Lie U(ψ))|`.

## Proofs as implemented

**Rational action.** The rational matrix of a point is its affine matrix at the base field
(public `rationalMatrix_eq_affineMatrix`). By `rationalPointEquiv_map` the affine point of the
image of `x` is the affine point of `x` followed by `iP`. The public
`adjointExteriorCoordinates_character_action` then gives the scalar action by the determinant
character on affine points, and `rationalCharacterEval_eq_affineUnitsEquiv` identifies that
scalar with the rational value.

**Injectivity and the eigenvalue function.** `iP` is a monomorphism (the first field of
`IsRepresentedBy`), so the point map is injective by cancellation, and `Function.invFun` is a
left inverse on its image. The rational points of `P(χ)` are exactly the image of `P(k)`
(public `SubgroupFunctor.rationalPoints_eq_range`), so the rational action gives the eigenvector
property.

**Lower bound.** Take `cG = Lie.finiteCoordinates G` (public, `ScalarExtensionCoordinates`). The
vector `v` is nonzero because `iU` is a monomorphism and `F` is a field (public
`adjointExteriorCoordinates_ne_zero`). Restricting the eigenvector property from `P(ψ)(F)` to
`Z(χ₀)(F)` by `hZ`, the public `exists_le_abs_eigenvalue` gives `C > 0` with `C ≤ |c m|` whenever
`x = m u κ` as above and `x` fixes `v`. To see that `x` fixes `v`: by `hθ` the eigenvector property
holds on a subgroup containing `P(θ)(F)`, so the public `eigenvalue_eq_one_of_mem_unipotent`
gives eigenvalue `1` at `x ∈ U(θ)(F)`; and `x ∈ P(ψ)(F)` because `U(θ) ≤ P(θ)` (public
`unipotent_le_parabolic`) and `hθ`. Finally `adjointDeterminantPointValue_map` rewrites `c m` as
the determinant at `q`.

## Scope

The module gives one lower bound for each parabolic `P(ψ)`; the structural inclusions
`Z(χ₀)(F) ≤ P(ψ)(F)` and `P(θ)(F) ≤ P(ψ)(F)` are hypotheses. It does not identify the restriction
of the determinant to the split component with a sum of relative roots, does not supply the cone
geometry of relative roots and does not complete the host intertwining theorem.
