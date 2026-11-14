# Piece factorizations with explicit coroot torus factors

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.PieceCorootFactorization`.

The published module `Geometry.Building.QuasiSplitMultipliableFactorization` factorizes points
of a multipliable relative root group piece by piece. Its torus factors are abstract
normalizer points. This module refines those factorizations over a split pinning: the torus
factors are coroot points, and the opposite-pair product of a product of piece triples is
computed explicitly.

## Setting

Let `k` be a field, `G` an affine group scheme over `Spec k`, and `p : SplitPinning G`. Write
`j = p.inclusion` and `U_χ = rootGroupPoints j χ`. For a root index `s`, write `s^∨` for the
coroot point map `LinkedRootParametrization.cocharacterPoint j (p.rootDatum.coroot s)`.

Sections `Piece` and `Pieces` also assume `[Smooth G.X.hom]` and
`[LocallyOfFiniteType G.X.hom]`, a commutative group scheme `S` with `f : S ⟶ p.torus`, a
character `a` of `S`, and `hline : RestrictsToMultipliableLine f p.rootDatum a`. The last
says every root restricting to a multiple of `a` restricts to `±a` or `±2a`. Pieces
(`IsMultipliablePiece`) and piece families (`PieceFamily`, with `tripleProd`) are the
published notions of module `Geometry.Building.QuasiSplitMultipliableOpposite`.

## Results

- `list_ofFn_prod_conj L l x hx hy`, a group lemma. Let `L : Fin r → M`. Suppose every
  factor `L m` with `m ≠ l` commutes with `x` and with `L l * x * (L l)⁻¹`. Then
  conjugating `x` by the ordered product `(List.ofFn L).prod` gives `L l * x * (L l)⁻¹`.
  The proof is by induction on `r`, splitting off the first factor (`List.ofFn_succ`).
- `gauss_decomposition_coroot p s hf hX`. This refines the published `gauss_decomposition`.
  Let `f ∈ U_{root s}` and `X ∈ U_{-root s}`. Then one of the following holds.
  1. `f X = X' τ f'` with `X' ∈ U_{-root s}`, `f' ∈ U_{root s}` and `τ` in the range of `s^∨`.
  2. `f X = B ν` with `B ∈ U_{-root s}` and `ν` normalizing `j` with
     `ν(-root s) = root s`.

  The proof is the published one, made explicit. If `f = 1`, take `τ = 1`. Otherwise
  `τ = (qr.1 W qr.2) (pr.1 f pr.2)`, where `pr` is an opposite pair of `f`, and `qr` one of
  the nontrivial conjugate `W ∈ U_{root s}`. This `τ` lies in the range of `s^∨` by
  `oppositeProduct_mul_mem_range` (module `Rational.LinkedRootOppositePairs`).
- `piece_factorization_coroot p hline hp hq hpq hm hXq hXm hXm1 hXp hpr`. Let `(lp, lq, lm)`
  be a piece, and `X_q ∈ U_q`, `X_m ∈ U_m \ {1}`, `X_p ∈ U_p`, with an opposite pair `pr` of
  `X_m`. The conclusion is the published `piece_factorization`, except that in the first
  case the torus factor `τ` is in the range of the coroot of `s = reflectionPerm lp lp`,
  whose root is `-root lp`. The second case is unchanged:
  `X_q X_m X_p = (pr.1⁻¹ d e) ν (c pr.2⁻¹)`, with `ν` normalizing `j` and `ν(p) = q`. The
  proof is the published one, with `gauss_decomposition_coroot` at `s` in place of
  `gauss_decomposition`. The Library lemma `root_reflectionPerm_self` converts between
  `root s` and `-root lp`.
- `oppositeProduct_eq_prod p hline hS F ha0 hX hZ hY hZ1 hg hg1 hg' hg'' hN hN' hpr`.
  Unlike `piece_factorization_coroot`, this result also takes the instance hypothesis
  `[Mono (CommGroupScheme.groupHom f ≫ p.inclusion).hom.hom.left]`: the composite
  `S ⟶ G` is a monomorphism of the underlying schemes. An arbitrary `f` need not be one; the
  hypothesis is needed for the restricted root groups and normalizer of `groupHom f ≫ j`
  used below (as in the published separation lemma `eq_of_mul_mul_mem_normalizer`). Assume:
  - `S` is split, `a ≠ 0`, and `F` is a piece family over `a`;
  - `g = F.tripleProd X Z Y` is a nontrivial point of the restricted root group of `a`,
    with every `Z l ≠ 1`;
  - `g', g''` lie in the restricted root group of `-a`;
  - `g' g g''` normalizes both `j` and `groupHom f ≫ j`;
  - `pr l` is an opposite pair of `Z l` for every `l`.

  Then there are `τ l`, each in the range of the coroot of `reflectionPerm (lp l) (lp l)`,
  with `g' g g'' = ∏ₗ (pr l).1 (Z l) (pr l).2 (τ l)`, an ordered `List.ofFn` product.

## Proof of `oppositeProduct_eq_prod`

1. For every piece, `piece_factorization_coroot` gives a factorization
   `X_l Z_l Y_l = L_l N'_l R_l`, with `N'_l` normalizing `j`. Either
   `N'_l = (pr l).1 Z_l (pr l).2 τ_l` (first case), or `N'_l` sends `p_l` to `q_l` (second
   case). Here `L_l = (pr l).1⁻¹ d_l e_l`, with `d_l = [(pr l).1, X_l] ∈ U_{-p_l}`, and
   `R_l = f'_l c_l (pr l).2⁻¹`.
2. As in the published proof of `opposite_coordinates`, all of `L_l`, `N'_l`, `R_l` lie in
   the piece group of `l`. Different piece groups commute (`pieces_commute`,
   `commute_of_mem_pieceGroup`). Hence `g = (∏ L)(∏ N')(∏ R)` (`list_ofFn_prod_mul_mul`).
   Moreover `∏ L` and `∏ R` lie in the restricted root group of `-a`
   (`rootGroupPoints_le_comp`).
3. The separation lemma `eq_of_mul_mul_mem_normalizer` gives `g' g g'' = ∏ₗ N'_l`.
4. Every piece is in the first case. Suppose piece `l` were in the second case. Take
   `x = x₊(1) ≠ 1` in `U_{p_l}`, from the chosen linked parametrization of `p_l`.
   - The other factors `N'_m` commute with `x` and with `N'_l x N'_l⁻¹`, both in the piece
     group of `l`. So by `list_ofFn_prod_conj`, conjugating `x` by `g' g g''` gives
     `N'_l x N'_l⁻¹`.
   - `N'_l x N'_l⁻¹` lies in `U_{q_l}` (`conj_mem_rootGroupPoints`), hence in the
     restricted root group of `a`.
   - `(g', g'')` is an opposite factor pair of `g` for `groupHom f ≫ j`. So `g' g g''` sends
     `a` to `-a` (`IsOppositeFactorPair.weylAction_eq_neg`). Since `x` lies in the
     restricted root group of `a`, the same conjugate lies in that of `-a`.
   - The published `RelativeRoot.eq_one_of_mem_subgroup_of_mem_opposite` makes the
     conjugate trivial, so `x = 1`, a contradiction.
5. Choosing the `τ_l` of the first cases gives the stated product.

## Provenance

This is an internal refinement of published Library proofs (`gauss_decomposition`,
`piece_factorization`, `opposite_coordinates`). It adds explicit coroot information about
the torus factors and makes no new mathematical assertion. It serves the `A₂`-orbit case of
Steinberg's theorem `Z(k) ⊆ G(k)^+` for quasi-split simply connected groups (Platonov–
Rapinchuk, *Algebraic Groups and Number Theory* (1994), §7.2, printed p. 406, registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`). There the torus part of the
rank-one Weyl element of a point of `U_a(k)` is read off over a splitting field.
