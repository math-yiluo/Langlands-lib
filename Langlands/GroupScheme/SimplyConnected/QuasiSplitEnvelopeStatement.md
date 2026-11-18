# A quasi-split simply connected subgroup containing a maximal split torus

`Langlands.GroupScheme.SimplyConnectedQuasiSplitEnvelopeStatement` is a
proposition over every field `k : Type u`.

Let `G` be a semisimple algebraically simply connected group over a field `k` and
let `i : S.toGrp ⟶ G` be a maximal split torus. There exist a group `H`, a closed
subgroup inclusion `j : H ⟶ G`, and a map `f : S.toGrp ⟶ H` such that `H` is
semisimple simply connected and quasi-split, `f` is a maximal split torus of
`H`, and `f ≫ j = i`.

`IsSimplyConnected` includes semisimplicity and requires that every incoming
central isogeny from a semisimple group be an isomorphism. `IsQuasiSplit` means
connected reductive with a field-defined Borel that remains Borel over an
algebraic closure. `IsClosedSubgroup j` requires a closed immersion of underlying
schemes. Both `i` and `f` use `IsMaximalSplitTorus`, and their source is the same
commutative group scheme `S`. The equality `f ≫ j = i` is in the category of
group schemes over `Spec k`.

## Derived provenance

* Armand Borel and Jacques Tits, *Groupes réductifs*, Publications Mathématiques
  de l'IHÉS 27 (1965), Theorem 7.2, printed pp.117–121 (one-based PDF pp.64–68).
  Registered source `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  For a maximal split torus `S`, choose a one-dimensional `k`-linear subgroup
  in each simple root group of the reduced system of nonmultipliable relative
  roots. The theorem supplies a split connected reductive subgroup `F` with
  maximal torus `S` and with that reduced root system.
  [Original article](https://www.numdam.org/item/PMIHES_1965__27__55_0/).
* Armand Borel and Jacques Tits, *Compléments à l'article « Groupes réductifs »*,
  Publications Mathématiques de l'IHÉS 41 (1972), Corollary 4.6, printed p.273
  (one-based PDF p.22). Registered source
  `borel-tits-1972-complements-groupes-reductifs`, SHA-256
  `7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`.
  The corollary, attributed to J. Humphreys, gives simple connectedness of
  the maximal split semisimple subgroup `F` from Theorem 7.2 when `G` is simply
  connected. [Original supplement](https://www.numdam.org/item/PMIHES_1972__41__253_0/).

Take `H = F` and let `j` be its closed subgroup inclusion. The embedding `i`
factors through `j` because `F` contains its image. The resulting `f` is a
maximal split torus in `F`, since `S` is a split maximal torus there. A split
semisimple group has a field-defined geometric Borel, giving the stated
quasi-splitness. In split rank zero `S` is trivial, so one can take
`H = S.toGrp`, `j = i`, and `f = 𝟙 S.toGrp`.

The reductivity argument on p.121 of the 1965 article cites 3.22 for a trivial
intersection of subgroups of opposite ambient unipotent radicals. The
opposite-cell factorization suffices for this special case. The project erratum
documents the obstruction to the general closed-root intersection assertion in
3.22(b). [Closed-root intersection erratum](../../../notes/errata/borel-tits-1965-closed-root-intersection.md).
