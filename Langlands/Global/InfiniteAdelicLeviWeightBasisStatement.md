# A weight basis of the archimedean Lie algebra adapted to a parabolic: statement

Module `Langlands.Global.InfiniteAdelicLeviWeightBasisStatement`, namespace `Langlands.Global`.
It contains one `Prop`-valued definition, `LeviTangentWeightBasisStatement`, and proves nothing.

## Statement

The statement quantifies over a number field `F : Type u`, group schemes `G`, `Q`, `M'`, `V` over
`Spec F` such that the total spaces of `G`, `Q` and `M'` are affine, and morphisms `q : Q ⟶ G`,
`iV : V ⟶ Q`, `l' : M' ⟶ Q`. It assumes that `G` is connected reductive
(`IsConnectedReductive G`), that `q` is a parabolic subgroup (`IsParabolicSubgroup q`), that `iV`
is a geometric unipotent radical of `Q` (`LeviSubgroup.IsGeometricUnipotentRadical iV`) and that
`l'` is a rational Levi subgroup of `Q` (`IsRationalLeviSubgroup l'`). It then takes smooth
structures `hsmooth : SmoothOfRelativeDimension d G.X.hom` and
`hsmooth' : SmoothOfRelativeDimension d' M'.X.hom`.

The groups `G(F_∞)` and `M'(F_∞)` (`InfiniteAdelicGroupPoints`, the points with values in the
infinite adele ring `F_∞ = InfiniteAdeleRing F`) carry the Library's charted spaces
`smoothChartedSpace` modelled on `smoothModel F d`, resp. `smoothModel F d'`, with the real
structure of each archimedean completion given by `InfinitePlaceGroupPoints.completionRCLike`, and
`G(F_∞)` carries the Lie group structure `smoothLieGroup`. The real Lie algebra of `G(F_∞)` is its
tangent space at `1`, `GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)`.
The statement writes

- `ι : M'(F_∞) → G(F_∞)` for the point map `M'.affinePointsTarget (l' ≫ q)` of `l' ≫ q`, and
- `S_V ⊆ G(F_∞)` for the range of the point map `V.affinePointsTarget (iV ≫ q)` of `iV ≫ q`,
  the image of `V(F_∞)`.

The conclusion is that there are a point `t ∈ M'(F_∞)`, a natural number `n`, a real basis `b`
of the Lie algebra of `G(F_∞)` indexed by `Fin n` and integer weights `w : Fin n → ℤ` such that

1. every `b a` is an eigenvector of the tangent conjugation by `ι t` (the adjoint action
   `Ad(ι t)`, `groupTangentConjugation`) with eigenvalue `2 ^ (w a)`;
2. the tangent map `mfderiv ι 1` of `ι` at `1` is injective;
3. every `b a` with `w a = 0` lies in the range of `mfderiv ι 1`;
4. the range of `mfderiv ι 1` lies in the real span of the `b a` with `w a = 0`;
5. every `b a` with `w a > 0` is the velocity at `0` of a smooth curve `c : ℝ → G(F_∞)` with
   `c 0 = 1` and all values in `S_V`;
6. the velocity at `0` of every smooth curve `c : ℝ → G(F_∞)` with `c 0 = 1` and all values in
   `S_V` lies in the real span of the `b a` with `w a > 0`.

So the Lie algebra of `G(F_∞)` is the direct sum of the eigenspaces of `Ad(ι t)`, the image of
the Lie algebra of `M'(F_∞)` is the eigenspace for the eigenvalue `1`, and the real span of the
tangent directions of the image of `V(F_∞)` is the sum of the eigenspaces with eigenvalues
greater than `1`.

## Sources and provenance

The statement is derived. Over the base field `F`, a parabolic subgroup of a connected reductive
group is a dynamic parabolic `P_G(λ)` for a cocharacter `λ`: J. S. Milne, *Algebraic Groups*
(2017) (`milne-2017-algebraic-groups`), Theorem 25.1, printed p. 544 (PDF p. 560). The
cocharacter can be chosen in the centre of the given Levi subgroup `M'`, which is then its
centralizer, with `V` the dynamic unipotent subgroup `U_G(λ)`. The Lie algebras of `Z_G(λ)`,
`U_G(λ)` and `P_G(λ)` are then the weight-zero, positive-weight and nonnegative-weight parts of
the Lie algebra of `G` under `λ`: B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*,
second edition (2015) (`conrad-gabber-prasad-2015-pseudo-reductive`), Proposition 2.1.8 (1),
printed p. 53 (PDF p. 79).

The statement transports this decomposition to the real Lie algebra of `G(F_∞)` for the point
`t = λ(2)` of `M'(F_∞)`: `Ad(λ(2))` acts on the weight-`m` part by `2 ^ m`, and the Lie algebra of
the real Lie group `G(F_∞)` is the Lie algebra of `G` tensored up to `F_∞`. The value `2` is a
choice; any real number greater than `1` gives the same eigenspaces. Items 5 and 6 describe the
Lie algebra of `V(F_∞)` inside that of `G(F_∞)` through smooth curves in the image of
`V(F_∞)`, which needs no Lie group structure on `V(F_∞)` and no tangent map of its point map. The formulation with a basis indexed by `Fin n` and integer weights is
internal; it is made for the weight argument of A. W. Knapp and D. A. Vogan, *Cohomological
Induction and Unitary Representations* (1995) (`knapp-vogan-1995-cohomological-induction`),
Lemma 4.123, printed p. 301 (PDF p. 323), which decomposes a central element of the enveloping
algebra along such a basis.
