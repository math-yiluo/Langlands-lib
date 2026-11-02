# Rational points of `GL_N` and of its block subgroups

This module compares the algebraic group `GL_N` with the Library's concrete matrix group. The
algebraic group is the published `GeneralLinear.groupScheme (Fin N) R` over `Spec R`. The
matrix group is `Langlands.GeneralLinear N R`, the units of `Matrix (Fin N) (Fin N) R`, used by
the representation-theory parts of the Library.

The comparison takes place on rational points, the points over `Over.mk (𝟙 (Spec R))`. For
every block shape `B : Langlands.GeneralLinear.BlockShape N` it covers the dynamic subgroups
`P(λ_B)`, `Z(λ_B)` and `U(λ_B)` of the published block-shape cocharacter
`λ_B = blockShapeCocharacter B R`. It identifies them with the Library's block subgroups
`B.parabolic R`, `B.leviSubgroup R` and `B.unipotentSubgroup R`. It also identifies the limit
map with the Library's diagonal-block projection.

`R` is any commutative ring (`CommRingCat`), in particular any field, and `N` is any natural
number. For `N = 0` there is exactly one block shape, with no blocks, and every statement
applies to it.

## Sources and provenance

The identification of `P(λ)`, `Z(λ)` and `U(λ)` with block upper triangular, block diagonal and
block unipotent matrices is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015),
Example 2.1.1, printed pp. 45–47 (PDF pp. 71–73). There `P_G(λ)` consists of the `g = (a_rs)`
with `a_rs = 0` when the weight of `r` is smaller than that of `s`. The limit
`lim_{t→0} t.g` is the block diagonal part of `g`. The published module
`Langlands.GroupScheme.Dynamic.GeneralLinearOrbit` proves this on every test scheme
(`parabolic_blockShapeCocharacter`, `centralizer_blockShapeCocharacter`,
`unipotent_blockShapeCocharacter` and `hasLimit_blockShapeCocharacter_iff`).

This module is an interface bridge. It specializes those results to rational points and moves
the matrix entries from the global sections `Γ(Spec R, ⊤)` to `R` along
`Scheme.ΓSpecIso R`. It adds no new mathematics beyond this transport.

## Matrices along ring isomorphisms

Let `φ : A ≃+* A'` be a ring isomorphism.

- `glRingEquiv φ : GL n A ≃* GL n A'` applies `φ` to every entry (`Units.mapEquiv` of
  `RingEquiv.mapMatrix`). `glRingEquiv_apply` gives the entries. `glRingEquiv_eq_map` shows it
  agrees with Mathlib's `Matrix.GeneralLinearGroup.map`. `glRingEquiv_symm_apply_apply` shows
  that `φ.symm` undoes it.
- `glRingEquiv_mem_blockParabolicSubgroup_iff`, `glRingEquiv_mem_blockLeviSubgroup_iff` and
  `glRingEquiv_mem_blockUnipotentSubgroup_iff`: for weights `e : n → ℤ`, a matrix lies in the
  published weight-block parabolic, Levi or unipotent subgroup if and only if its image does.
  This uses the published stability lemmas `map_mem_blockParabolicSubgroup` and the related
  lemmas, for `φ` and `φ.symm`.
- `glRingEquiv_blockLeviProjection`: taking the block diagonal part (`blockLeviProjection`)
  commutes with `glRingEquiv φ`, because `φ 0 = 0`.
- For a block shape `B`, `glRingEquiv_mem_parabolic_iff`, `glRingEquiv_mem_leviSubgroup_iff`
  and `glRingEquiv_mem_unipotentSubgroup_iff` give the same statements for the Library's
  `B.parabolic`, `B.leviSubgroup` and `B.unipotentSubgroup`. The proofs go through the published
  equalities `blockParabolicSubgroup_blockShapeWeight` and the related ones.
- `glRingEquiv_leviEmbedding_leviProjection`: the Library's Levi part
  `B.leviEmbedding (B.leviProjection g)` of a block upper triangular matrix commutes with
  `glRingEquiv φ`. The proof goes through the published `leviEmbedding_leviProjection`, which
  writes it as `blockLeviProjection`.

## Rational points

- `globalSectionsEquiv R : Γ(Spec R, ⊤) ≃+* R` is the ring isomorphism of `Scheme.ΓSpecIso R`.
- `rationalPointsEquiv N R : (Over.mk (𝟙 (Spec R)) ⟶ (groupScheme (Fin N) R).X) ≃*
  Langlands.GeneralLinear N R`. It is the published `GeneralLinear.pointsEquiv` at the test
  scheme `Spec R`, followed by `glRingEquiv (globalSectionsEquiv R)`. It is a group isomorphism.
  So it is compatible with products, inverses and conjugation.
- `rationalPointsEquiv_apply_apply`: the `(i, j)` entry of the matrix of a rational point `x` is
  the image in `R` of the pullback along `x` of the coordinate function `entrySection i j`.

## Block subgroups

Fix a block shape `B` and write `λ_B = blockShapeCocharacter B R`.

- `mem_parabolic_blockShapeCocharacter_iff`, `mem_centralizer_blockShapeCocharacter_iff` and
  `mem_unipotent_blockShapeCocharacter_iff`: a rational point lies in `P(λ_B)`, `Z(λ_B)` or
  `U(λ_B)` if and only if its matrix lies in `B.parabolic R`, `B.leviSubgroup R` or
  `B.unipotentSubgroup R`.
- `map_parabolic_blockShapeCocharacter`, `map_centralizer_blockShapeCocharacter` and
  `map_unipotent_blockShapeCocharacter`: the images of the rational-point subgroups under
  `rationalPointsEquiv` are exactly these Library subgroups.
- `rationalParabolicEquiv B`, `rationalLeviEquiv B` and `rationalUnipotentEquiv B` are the
  resulting group isomorphisms. They are `P(λ_B)(R) ≃* B.parabolic R`,
  `Z(λ_B)(R) ≃* B.leviSubgroup R` and `U(λ_B)(R) ≃* B.unipotentSubgroup R`. Each is
  `rationalPointsEquiv` restricted to the subgroup (`rationalParabolicEquiv_coe` and the
  related lemmas).

## The limit map and its section

- `rationalPointsEquiv_limit`: for `g ∈ P(λ_B)(R)`, the matrix of the limit
  `Dynamic.limit λ_B g` is `B.leviEmbedding R (B.leviProjection R g')`, where `g'` is the matrix
  of `g` in `B.parabolic R`. Proof: the published `hasLimit_blockShapeCocharacter_iff` gives this
  over `Γ(Spec R, ⊤)`, and `glRingEquiv_leviEmbedding_leviProjection` transports it to `R`.
- `rationalLeviEquiv_limitHom`: the published limit homomorphism
  `Dynamic.limitHom λ_B : P(λ_B)(R) →* Z(λ_B)(R)` (`Dynamic.LimitMap`) corresponds to the
  Library's Levi projection. Precisely, `rationalLeviEquiv B (limitHom g)` is
  `B.leviEquiv R (B.leviProjection R (rationalParabolicEquiv B g))`. Its kernel is `U(λ_B)(R)`
  (published `Dynamic.ker_limitHom`).
- `rationalParabolicEquiv_inclusion`: the section `Z(λ_B)(R) ≤ P(λ_B)(R)` of the limit
  homomorphism corresponds to the Library's inclusion `B.leviAsParabolic`.

Together with the published `Dynamic.semidirectEquiv`, these give the Levi decomposition
`U(λ_B)(R) ⋊ Z(λ_B)(R) ≃* P(λ_B)(R)` in Library matrix terms. The module does not restate it.

## Scope

The module treats only the standard block-shape cocharacters, whose blocks are consecutive with
decreasing weights. Other diagonal cocharacters are covered over all test schemes by the
published weight-block subgroups (`blockParabolic n R e` and the related functors). The module
proves nothing about topologies on `GL_N(F)`; those are in the Library's
`Langlands.Group.GL` modules.
