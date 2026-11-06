# Levi intersection with a parabolic sharing a maximal split torus

`Langlands.GroupScheme.RepresentedParabolicLeviIntersectionStatement` is a
proposition about two parabolic subgroups `P ⊃ M` and `Q = L U` of a
connected reductive group `G` over an arbitrary field `k`. If the Levi
subgroups `M` and `L` contain a common maximal split torus of `G`, then
`M ∩ Q` is a parabolic subgroup of `M`, with Levi subgroup `M ∩ L` and
unipotent radical `M ∩ U`.

## Hypotheses

- `G` is connected reductive (`IsConnectedReductive`).
- `p : P ⟶ G` is a parabolic subgroup (`IsParabolicSubgroup`) and
  `l : M ⟶ P` is a rational Levi subgroup (`IsRationalLeviSubgroup`).
- `q : Q ⟶ G` is a parabolic subgroup, `lQ : L ⟶ Q` is a rational Levi
  subgroup, `rQ : U ⟶ Q` is a geometric unipotent radical
  (`LeviSubgroup.IsGeometricUnipotentRadical`), and the multiplication
  `L ⋉ U ⟶ Q` is an isomorphism (`IsIso (subgroupMultiplication lQ rQ)`).
- `i : T.toGrp ⟶ G` is a maximal split torus (`IsMaximalSplitTorus`) that
  factors through `l ≫ p` and through `lQ ≫ q`, i.e. lies in `M` and in `L`.

The unipotent radical of `P` is not named; the conclusion does not involve it.

## Conclusion

There are group schemes `P'`, `M'`, `N'` and morphisms `p' : P' ⟶ M`,
`l' : M' ⟶ P'`, `r' : N' ⟶ P'` such that

- `p'` is a parabolic subgroup of `M`, `l'` is a rational Levi subgroup of
  `P'`, `r'` is a geometric unipotent radical of `P'`, and the multiplication
  `M' ⋉ N' ⟶ P'` is an isomorphism;
- as subgroup functors of `G`,
  `range (p' ≫ l ≫ p) = range (l ≫ p) ⊓ range q` (that is, `P' = M ∩ Q`),
  `range (l' ≫ p' ≫ l ≫ p) = range (l ≫ p) ⊓ range (lQ ≫ q)`
  (`M' = M ∩ L`), and
  `range (r' ≫ p' ≫ l ≫ p) = range (l ≫ p) ⊓ range (rQ ≫ q)`
  (`N' = M ∩ U`).

`SubgroupFunctor.range f` is the image of `f` on points with values in every
`k`-scheme, and `⊓` is the pointwise intersection. Equality of these functors
identifies the scheme-theoretic intersections, not only their rational points.

## Sources

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, 2026 version (`renard-2026-representations-groupes-reductifs-padiques`),
V.4.6 (ii) (printed p.120 / PDF p.126): for standard parabolics `P = MN`,
`Q = LU` and `w ∈ W_{L,M}`, `M ∩ w·Q` is a standard parabolic subgroup of `M`
with Levi factor `M ∩ w·L` and unipotent radical `M ∩ w·U`. V.4.7 (printed
pp.121–122 / PDF pp.127–128) transports this to arbitrary parabolics and the
representatives `z = g⁻¹ w h`: `M ∩ z·Q` is a parabolic subgroup of `M` with
Levi factor `M ∩ z·L` and unipotent radical `M ∩ z·U`.

## Provenance of the hypothesis form

This statement is derived. Renard's proof of V.4.6 (ii) only uses that `M` and
`w·L` both contain `A_∅` (the standard Levi subgroups contain it and `w`
normalizes it): through the bijection of V.4.2, `M ∩ w·Q` corresponds to the
parabolic subset `M ∩ w·Q` of the roots of `M` relative to `A_∅`. In V.4.7 the
same conclusion for `z = g⁻¹ w h` is the conjugate by `g⁻¹` of the standard
case, in which `M` and `z·L` contain `g⁻¹ A_∅ g`.

The statement isolates that common torus as its hypothesis, so it applies to
any pair of Levi subgroups containing a common maximal split torus. In this
generality it is the standard dynamic description. With `S` the common torus,
write `P = P_G(λ)`, `M = Z_G(λ)`, `Q = P_G(μ)`, `L = Z_G(μ)`, `U = U_G(μ)` for
cocharacters `λ`, `μ` of `S`. This uses Borel–Tits 4.15 b) (printed
pp.90–91 / PDF pp.37–38): a `k`-parabolic subgroup is `G_{Φ⁺}` for an order on
the roots relative to a maximal `k`-split torus of its radical, and its
`k`-Levi subgroups are the centralizers of such tori. Then
`M ∩ Q = P_M(μ)`, `M ∩ L = Z_M(μ)` and `M ∩ U = U_M(μ)`, which are a
parabolic subgroup of the connected reductive group `M`, a Levi subgroup of it
and its unipotent radical. This is what Renard's argument uses for `w·Q`. The
statement is the input that the published
`RepresentedGeometricLemmaGeometryStatement` needs for each representative
supplied by `RepresentedParabolicDoubleCosetStatement`.

## Scope

The statement is algebraic, over every field `k`, with no topology. It is
stated for `M` against `Q`. The companion assertion for `L` against a
conjugate of `P` is the same statement with the roles exchanged. The
decompositions of `P ∩ z·Q` and `N ∩ z·Q` in Renard V.4.6–V.4.7 are not
asserted.
