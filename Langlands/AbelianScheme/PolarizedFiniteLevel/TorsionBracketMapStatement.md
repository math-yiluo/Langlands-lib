# Torsion bracket maps to projective space with finitely many configurations in each geometric fibre

`Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionBracketMapStatement` is a
proposition definition. It is a statement only. The module proves nothing.

## The statement

Fix `P : Prerequisites.{0}` and natural numbers `g d` with `0 < g` and `0 < d`.
The statement says that some natural number `N` has the following property. Let
`n ≥ N`, let `T : LevelBase n` be any level base (a locally noetherian scheme in
universe `0` on which `n` is a unit), and let `b : Datum P T.obj g d n` be any
datum over it. Then there are a natural number `m` and a morphism

`j : T.obj ⟶ ProjectiveSpace ℤ[1/n] m`

such that the following holds for every algebraically closed field `K : Type` and
every `K`-point `y : Spec K ⟶ ProjectiveSpace ℤ[1/n] m`. There is a finite set
`s` of `K`-points of `T.obj` such that for every `K`-point `t` of `T.obj` with
`t ≫ j = y`, some `t' ∈ s` satisfies

`(b.pullback t).TorsionConfigurationEquivalent (b.pullback t')`.

Here `ℤ[1/n]` is `Localization.Away (n : ℤ)`, `ProjectiveSpace` is the Library's
`Langlands.AlgebraicGeometry.ProjectiveSpace`, `Datum.pullback` is the published
pullback of data, and `Datum.TorsionConfigurationEquivalent` is the predicate of
module `TorsionConfiguration`.

In words: the `K`-points of `T` in one geometric fibre of `j` carry only finitely
many classes of torsion configurations. Both `m` and `j` may depend on `T` and
`b`, and `s` may depend on `K` and `y`. If `y` is not in the image of `j`, the
empty set works. The statement does not ask `j` to be a morphism over
`Spec ℤ[1/n]`. Since `n` is a unit on `T`, any morphism to `ProjectiveSpace ℤ[1/n] m`
is automatically one over `Spec ℤ[1/n]` (`LevelBase.eq_toLocalizationSpec`). The
statement does not ask `j` to be injective, quasi-compact or separated.

## Provenance

This is a derived intermediate statement. It is internal and not taken from a
source. Its brackets are the determinants of evaluation at labelled torsion
points that the accepted `LargeLevelQuasiFiniteProjectiveStatement` Markdown
describes. In that description, monomials in brackets are sections of a single
line bundle only when they are balanced, that is, have the same weight at every
label. The intended proof below avoids balancing. It uses the `n`-th power of
each single bracket, which is a section of `det(E)^{-n}` by step 3 below.

## Intended proof (not established)

Nothing in this section is proved or claimed. It records the route a proof is
expected to take.

1. **The direct image.** Let `π : A → T` be the abelian scheme of `b`, `L` its
   canonical bundle and `E = π_* L³ = b.rigidificationModule`. By the published
   `CubicDirectImageStatement` (proved in the Library), `E` is locally free of
   rank `M + 1 = 6^g · d` and commutes with base change. Its determinant
   `det(E)` is a line bundle; the Library's
   `Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant` constructs
   determinants of finite locally free modules. Write `Q_r = P_r^* L³` for the
   target of `b.torsionEvaluation r`.
2. **Brackets.** For a tuple `ρ = (r_0, …, r_M)` of labels, the determinant of
   the joint evaluation `E → Q_{r_0} ⊕ ⋯ ⊕ Q_{r_M}` is a section `[ρ]` of
   `det(E)^{-1} ⊗ Q_{r_0} ⊗ ⋯ ⊗ Q_{r_M}`. It is nonzero at a point exactly when
   the evaluations at `P_{r_0}, …, P_{r_M}` form a basis of the dual of the fibre
   of `E`.
3. **Trivializing `Q_r^{⊗n}`.** Let `𝒫` be the Poincaré bundle on `A ×_T Â`,
   rigidified along `0 × Â`. Then `L = (1, λ)^* 𝒫`, so
   `Q_r = (P_r, λ P_r)^* 𝒫^{⊗3}`. For an `n`-torsion section `x` and a section
   `ξ` of `Â`, the restriction of `𝒫` to `A × {ξ}` lies in `Pic⁰`. Hence
   `(x, ξ)^* 𝒫^{⊗n} ≅ (n x, ξ)^* 𝒫 = (0, ξ)^* 𝒫 ≅ 𝒪_T`, the last isomorphism by
   the rigidification. Fix these trivializations `τ_r : Q_r^{⊗n} ≅ 𝒪_T`. Then
   `[ρ]^{⊗n}` is a section of `det(E)^{-n}`.
4. **The map.** Let `ρ` run over all `(M + 1)`-tuples of labels. There are
   finitely many, `(n^{2g})^{M+1}`. When `n` is large, the sections `[ρ]^{⊗n}`
   generate `det(E)^{-n}`. Indeed, at every point some bracket is nonzero, by the
   published `FrameLocusCoverStatement` (every point lies in some frame locus).
   Alternatively, at every geometric point the torsion points span the projective
   space once `n² > 6^g · d · g!`, by `CubicTorsionHyperplaneBoundStatement`. The
   sections therefore define `j : T → ProjectiveSpace ℤ[1/n] m`, where `m + 1` is
   the number of tuples.
5. **Finitely many classes in a fibre.** Let `t : Spec K → T` with `t ≫ j = y`.
   Let `ρ_0` be the first tuple, in a fixed order, whose coordinate of `y` is
   nonzero. It depends only on `y`. At `t` the evaluations at the entries of
   `ρ_0` form a basis, so for every label `r` and every `k` there is a unique
   `c_{r,k} ∈ Hom(Q_{ρ_0(k)}, Q_r)` with `ev_r = Σ_k c_{r,k} ∘ ev_{ρ_0(k)}`. By
   Cramer's rule, `c_{r,k}` is the ratio `[ρ_0 with entry k replaced by r] / [ρ_0]`.
   Choose generators `e_r` of the lines `Q_r(t)` with `e_r^{⊗n} = τ_r`. In these
   generators each `c_{r,k}` is a scalar, and its `n`-th power is a ratio of two
   coordinates of `y`. So the tuple `(c_{r,k})` lies in a finite set that depends
   only on `y`. Two points `t, t'` over `y` with the same tuple are
   configuration-equivalent. Take `φ` to send the basis of `E_t` dual to
   `(ev_{ρ_0(k)})_k` to the corresponding basis of `E_{t'}`, and `ψ_r` to send
   `e_r(t)` to `e_r(t')`. Choosing one `t'` for each tuple that occurs gives `s`.

## Role

This statement is one of three inputs of the proved definition
`largeLevelQuasiFiniteProjective_of_torsionBrackets` (module
`LargeLevelQuasiFiniteProjectiveBracketReduction`). The other two are the
companion `TorsionConfigurationDeterminationStatement.{0}` and the accepted
`LargeLevelFiniteTypeStatement`. The definition proves
`LargeLevelQuasiFiniteProjectiveStatement`. It applies this statement to a level
base `X` that represents the moduli functor and to a datum representing the
universal class, and takes the resulting `j` as the locally quasi-finite map.
