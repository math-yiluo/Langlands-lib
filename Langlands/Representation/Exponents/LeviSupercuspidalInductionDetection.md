# Detecting the irreducible subquotients of a supercuspidal induction

Author: Worker 4949. Internal deduction supporting the VI.5.4 target of task
`fc21c11d-1a31-468d-a90e-fdda36098677`, factored out for reuse (in particular by Task
5307, the represented maximal-Levi length bound). Source: David Renard, *Représentations
des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.5.4 Theorem, first
paragraph of the proof, printed p.174 / PDF p.180, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. It does not use any
part of the VI.5.4 association theorem.

## Group-scheme lemmas

- `range_comp_iso_hom_eq_comap`: the range of `j ≫ e.hom` for an ambient isomorphism `e`
  is the preimage of `range j` under `e.inv`.
- `range_eq_range_comp_innerIso_of_comap`: two subgroup maps whose ranges are the
  conjugates of one subgroup functor by `g` and `g'` are conjugate by `g'⁻¹ g`.

## Transport of nontrivial Jacquet modules

`nontrivial_leviJacquet_of_range_eq_comp_innerIso`: if an actual parabolic `Q'` has the
range of `Q ≫ Int(g)`, then a nonzero normalized Jacquet module along `Q` gives a nonzero
one along `Q'`, for any smooth representation of `G(k)`. The Levi and radical
presentations of `Q` and `Q'` are arbitrary. The radical images correspond by the
published `parabolicRadical_range_eq`; translation by `g` is a linear equivalence of the
coinvariant carriers (`coinvariantsTranslateEquiv`). These declarations were previously
in `LeviSupercuspidalInductionFiniteLengthReduction` and are unchanged.

## Detection

`exists_conjugateLevi_supercuspidal_jacquetQuotient hns hG p l r hp hl hr hmul ρ hρsc A hA
hsub`. Hypotheses: the represented VI.5.3 (ii) proposition
`LeviJacquetInductionNoSupercuspidalStatement.{u, v}` (`hns`), an actual parabolic
`P = MN` of a connected reductive `G` over a nonarchimedean local field, a smooth `ρ` of
`M(k)` whose normalized Jacquet modules along all proper actual parabolics of `M` vanish,
and an irreducible actual subquotient `A` of `i_P^G ρ` (carrier universe `max u v`).
Conclusion: there are an actual parabolic `Q' = L'U'`, a point `g` and an isomorphism
`φ : M ≅ L'` with `φ.hom ≫ l' ≫ q' = l ≫ p ≫ Int(g)`; the normalized Jacquet module
`r_{Q'} A` is nonzero; and some irreducible `σ` of `L'(k)`, with vanishing Jacquet modules
along all proper actual parabolics of `L'`, is an actual quotient of `r_{Q'} A` and an
actual subquotient of `r_{Q'} i_P^G ρ`.

Proof. The published `leviCuspidalEmbedding` (represented VI.2.1, at carrier universe
`max u v`) applied to `A` gives `Q'`, the nonzero `r_{Q'} A` and the surjection onto `σ`.
The represented Jacquet functor is exact (published `leviParabolicFunctorsExact`), so
`ExactSmoothTransport.map_isSubquotient` makes `r_{Q'} A` a subquotient of
`r_{Q'} i_P^G ρ`, and `smoothSubquotientTransitivity` puts `σ` there. If no conjugacy
`(g, φ)` existed, `hns` would forbid such a supercuspidal `σ`.

`exists_leviEmbedding_nontrivial_jacquet`: under the same hypotheses there is an actual
parabolic with Levi source `M` and Levi embedding exactly `l ≫ p` along which `A` has a
nonzero Jacquet module. It is the parabolic `q' ≫ Int(g⁻¹)` with Levi map `φ.hom ≫ l'`
and radical `r'` (published `IsParabolicSubgroup.comp_iso` and
`IsRationalLeviSubgroup.iso_comp`, `isIso_subgroupMultiplication_iso_comp`),
with nontriviality from the transport lemma at `g⁻¹`.

All field and carrier universes, topologies and instances are those of the published
represented statements; nothing is assumed beyond `hns`.
