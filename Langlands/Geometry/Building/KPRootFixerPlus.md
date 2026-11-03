# The positive-depth root groups `U_{a,x,r+}` and `U_{a,Ω,0+}`

This module belongs to the task on actual Kaletha–Prasad affine-root,
special-point, parahoric and compact-stabilizer objects. It continues the
modules `KPApartment` and `KPBuilding`. For valid apartment data
`D : KPApartmentData i ω` it defines the groups `U_{a,x,r+}` of the filtration
of `U_a(k)` indexed by `R~`, and their intersections `U_{a,Ω,0+}` over a set
`Ω` of points of the apartment. Groups of this shape appear in KP's product
decompositions of `G(k)^♯_C` (Corollary 7.4.9) and in the comparison of
facets (6.3.21).

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- Definition 6.1.2, last paragraph, printed p. 199, PDF p. 230: "we can also
  index the filtration `{U_{a,φ,r}}` by `R~`, with
  `U_{a,φ,r+} = ⋃_{s>r} U_{a,φ,s}`". The conventions for `R~` are those of
  §1.6.
- Lemma 6.1.6 (translation of the filtration), printed p. 200, PDF p. 231.
- §6.1.8 (the action of `N(k)`), printed p. 201, PDF p. 232; Definition 6.3.1
  and Fact 6.3.3, printed pp. 217–218, PDF pp. 248–249.
- Lemma 6.3.20 and 6.3.21, printed p. 222, PDF p. 253, where `U_{a,F,0}` and
  `U_{a,F,0+}` are written for a facet `F`.
- Definition 7.4.1(1), printed p. 255, PDF p. 286:
  `U_{a,Ω,0} = ⋂_{x ∈ Ω} U_{a,x,0}`.
- Corollary 7.4.9, printed p. 257, PDF p. 288, which uses `U_{a,x,0+}` and
  `U_{a,F,0+}`.

The registered corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`) were checked. The Chapter 6 corrections on
PDF p. 32 and the Chapter 7 corrections on PDF pp. 33–35 do not change the last
paragraph of Definition 6.1.2, Lemma 6.1.6, Lemma 6.3.20, 6.3.21,
Definition 7.4.1(1) or Corollary 7.4.9. The correction on PDF p. 35 to the
sentence before Remark 7.4.2 only changes notation: it writes `x` for the
subscript `{x}`.

## Setting

As in `KPApartment`, `i : S.toGrp ⟶ G` is a homomorphism of group schemes over
a field `k`, with `[Mono i.hom.hom.left]` and `[IsAffineHom G.X.hom]`, and
`D : KPApartmentData i ω` is valid apartment data with points `D.Apartment`.
A point `x` is a valuation of the root datum, and `x.val a u ∈ ℝ ∪ {∞}` is
KP's `x_a(u)`. `U_a(k)` is `rootGroupPoints i a`. The published
`D.filtration x a r` is `U_{a,x,r} = {u ∈ U_a(k) | x_a(u) ≥ r}`
(`mem_filtration`).

## The groups `U_{a,x,r+}`

- `D.filtrationPlus x a r` is `U_{a,x,r+}`, the supremum of the subgroups
  `U_{a,x,s}` over `s ∈ (r, ∞)`. The filtration is decreasing, so the family is
  directed and the supremum is the union `⋃_{s>r} U_{a,x,s}` of KP
  Definition 6.1.2. The index `a` is any character of `S`, as for
  `D.filtration`.
- `mem_filtrationPlus`: `U_{a,x,r+} = {u ∈ U_a(k) | x_a(u) > r}`. For
  `x_a(u) = ∞`, which happens for `u = 1`, the witness is `s = r + 1`.
- `filtrationPlus_le_rootGroupPoints`, `filtrationPlus_le_filtration`
  (`U_{a,x,r+} ⊆ U_{a,x,r}`), `filtration_le_filtrationPlus`
  (`U_{a,x,s} ⊆ U_{a,x,r+}` for `r < s`) and `filtrationPlus_antitone`.
- `filtrationPlus_eq_affineRootGroupPlus`: for a relative root `α`,
  `U_{α,x,r+}` is the published affine root group `U_{ψ+}` of KP
  Definition 6.3.1, where `ψ = D.affineFunctional α x r` is the affine
  functional with derivative `α` and value `r` at `x`. The proof uses the
  published `mem_affineRootGroupPlus_iff`.
- `filtrationPlus_vadd`: `U_{α,x+v,r+} = U_{α,x,(r−α(v))+}` for a translation
  `v`. This is the `r+` form of Lemma 6.1.6. It is derived from the published
  `filtration_vadd` for the groups `U_{α,x,s}`.
- `conj_mem_filtrationPlus`: `n U_{a,x,r+} n⁻¹ ⊆ U_{n·a,nx,r+}` for
  `n ∈ N(k)`, where `n·a` is the published `weylAction i n a`. The proof
  combines `conj_mem_rootGroupPoints` from `KPBuilding` with the published
  formula `(nφ)_b(g) = φ_{n⁻¹·b}(n⁻¹ g n)` of §6.1.8.

## The groups `U_{a,Ω,0+}`

Let `Ω : Set D.Apartment`.

- `D.rootFixerPlus a Ω` is `U_a(k) ∩ ⋂_{x ∈ Ω} U_{a,x,0+}`.
- `mem_rootFixerPlus_iff_forall_mem`: `u` lies in it iff `u ∈ U_a(k)` and
  `u ∈ U_{a,x,0+}` for every `x ∈ Ω`.
- `mem_rootFixerPlus`: `U_{a,Ω,0+} = {u ∈ U_a(k) | x_a(u) > 0 for all x ∈ Ω}`.
- `rootFixerPlus_empty`: for `Ω = ∅` it is `U_a(k)`.
- `rootFixerPlus_singleton`: `U_{a,{x},0+} = U_{a,x,0+}`;
  `rootFixerPlus_singleton_eq_iSup` writes this as `⨆_{s>0} U_{a,x,s}`, and
  `rootFixerPlus_singleton_eq_affineRootGroupPlus` as `U_{ψ+}` for the affine
  functional `ψ` with derivative `α` vanishing at `x`.
- `rootFixerPlus_le_rootFixer`: `U_{a,Ω,0+} ⊆ U_{a,Ω,0}`, where
  `D.rootFixer a Ω` is the published group of Definition 7.4.1(1).
- `rootFixerPlus_anti`: `Ω ⊆ Ω′` implies `U_{a,Ω′,0+} ⊆ U_{a,Ω,0+}`.
- `conj_mem_rootFixerPlus`: `n U_{a,Ω,0+} n⁻¹ ⊆ U_{n·a,nΩ,0+}` for
  `n ∈ N(k)`, where `nΩ` is the pointwise image.

Provenance. KP do not define `U_{a,Ω,0+}` for an arbitrary set `Ω`. The
definition here is derived: it is the `0+` analogue of
Definition 7.4.1(1), `U_{a,Ω,0} = ⋂_{x ∈ Ω} U_{a,x,0}`, with `0` replaced by
`0+`. As for the published `D.rootFixer`, the intersection with `U_a(k)` makes
the group `U_a(k)` for empty `Ω` rather than all of `G(k)`. For nonempty `Ω`
it changes nothing, since every `U_{a,x,0+}` lies in `U_a(k)`.

For a point, `U_{a,{x},0+}` is KP's `U_{a,x,0+}`, as used in Corollary 7.4.9.
For a facet `F`, KP write `U_{a,F,0+}` for `U_{a,x,0+}` with `x ∈ F`
(6.3.21, by analogy with Lemma 6.3.20 for `U_{a,F,0}`). So
`D.rootFixerPlus a F` equals KP's `U_{a,F,0+}` once `U_{a,x,0+}` is known to be
the same for all `x ∈ F`. That independence is not proved here.

## Not proved or defined here

- The independence of `U_{a,x,0+}` and `U_{a,x,0}` of the point `x` in a facet
  (Lemma 6.3.20 and its `0+` form), and the chain of inclusions of 6.3.21.
  Facets are not used in this module.
- The groups `U_{a,Ω,r}` and `U_{a,Ω,r+}` for `r ≠ 0`, and the concave
  function groups of §7.3.
- The product decompositions of Corollary 7.4.9 and of Proposition 7.3.12.
- Any relation of `U_{a,Ω,0+}` with the double root group `U_{2a}(k)`.
