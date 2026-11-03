# Levi decompositions in characteristic zero

`Langlands.GroupScheme.CharacteristicZeroLeviDecompositionStatement` is a Prop-valued
target for the existence of Levi decompositions in characteristic zero (theorem of Mostow).
The module states it and does not prove it.

## Statement

The proposition quantifies over every field `F : Type u` with `CharZero F` and every group
scheme `G` over `Spec F` with instances `IsAffine G.X.left` and
`LocallyOfFiniteType G.X.hom`. If `G.X.hom` is smooth and the underlying space of `G.X.left`
is connected, then there are

* a group scheme `L` over `Spec F`,
* homomorphisms of group schemes `p : G ⟶ L` and `j : L ⟶ G` with `j ≫ p = 𝟙 L`, so `j`
  is followed by `p` and `j` is a section of `p`,

with the following properties:

* `IsConnectedReductive L` holds (Library definition in `Langlands.GroupScheme.Reductive.Basic`:
  smooth, affine, connected, with trivial unipotent radical after base change to an algebraic
  closure);
* the scheme-theoretic kernel `GroupScheme.kernel p` (the pullback of the unit section of `L`
  along `p`, from `Langlands.AbelianScheme.Kernel`) is smooth over `F`, has connected
  underlying space and satisfies `IsUnipotent`. Here `IsUnipotent` is the Library definition:
  every nonzero finite-dimensional matrix representation has a nonzero fixed vector.

As in the target `NormOneRationalQuotientFiniteVolumeStatement`, `IsAffine` together with
`LocallyOfFiniteType` gives the affine algebraic-group scope, and connectedness refers to the
underlying scheme.

## Relation to the source

Milne, *Algebraic Groups* (2017), works with a connected group variety `G` over a field `k`.

* 6.45 defines unipotent algebraic groups: every nonzero representation has a nonzero fixed
  vector. 6.46 defines the unipotent radical `R_u(G)` as the largest connected normal
  unipotent subgroup variety, and defines `G` to be reductive when `R_u(G_{k^a})` is trivial.
* 19.9: the formation of `R_u(G)` commutes with separable algebraic field extensions. 19.11(b):
  over a perfect field the quotient `G / R_u(G)` is reductive.
* 25.48: if an algebraic subgroup `R` of `G` has `R_{k^a} = R_u(G_{k^a})`, then `R` is
  smooth, connected, unipotent and normal, and `G / R` is reductive. A Levi subgroup is then a
  connected subgroup variety `L` such that the quotient map `G → G / R` restricts to an
  isomorphism `L → G / R`, and `G = R ⋊ L`.
* 25.49: over a perfect field such an `R` always exists (19.9). In characteristic zero Levi
  subgroups always exist, and any two are conjugate by an element of the unipotent radical
  (theorem of Mostow; Hochschild 1981, VIII, Theorem 4.3).

The Lean statement is derived from these results by the following translation. Take `R` and a
Levi subgroup `L` as in 25.48–25.49. Let `j : L → G` be the inclusion and `p : G → L` the
quotient map `G → G / R` followed by the inverse of the isomorphism `L → G / R`. Then
`j ≫ p = 𝟙 L`. The kernel of `p` is the kernel `R` of the quotient map, which is smooth,
connected and unipotent. `L ≅ G / R` is connected reductive. The Lean formulation therefore
keeps only the split homomorphism `p`, its section `j` and the properties of `ker p`. It does
not mention quotient group schemes, it does not identify `L` with a subgroup of `G`, and it
asserts neither uniqueness nor conjugacy of Levi subgroups. It does not assert that `ker p` is
the unipotent radical. That follows because `G / ker p ≅ L` is reductive, but the statement
does not record it.

In the finite-volume project for `NormOneRationalQuotientFiniteVolumeStatement`, this
statement supplies the split map consumed by
`Langlands.Global.AdelicGroupPoints.LeviReductionFiniteVolumeStatement`, whose kernel is then
handled by the unipotent compactness statement.

Source records: `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`: 6.45–6.46 (printed
p.135, PDF p.151), Proposition 19.9 and Proposition 19.11 (printed pp.399–400, PDF
pp.415–416), Definition 25.46 and 25.48–25.49 (printed p.559, PDF p.575). The official author
errata page (`milne-2017-algebraic-groups-errata-2026-11-02`, snapshot of 2026-11-02) lists no
correction to these items.
