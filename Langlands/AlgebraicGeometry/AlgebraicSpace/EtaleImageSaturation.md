# Diagonal and off-diagonal saturation

This derived helper implements the relation-splitting step in the registered
Stacks Project Lemma 67.50.1 (Tag 03XW), especially the displayed union identity
at `03XW.html:209-215`. It uses actual scheme fibre products over the fixed base
and fppf local images of presheaf maps. The universe `u` is arbitrary.

For an arrow `e : B → T` in schemes over `S`, `relation e` is its actual
scheme self-pullback, equipped with the structure map to `S`. Its projections
are `left e` and `right e`, and its diagonal is `diagonal e`. For separated
`e`, `off e` is the open complement of that diagonal. Etaleness makes the
diagonal open as well. After base change by `w : V → B`, the two pieces are
`V` and `offChart e w`, mapping to `chartRelation e w`. Their cartesian squares
and, for separated etale `e`, their point coverage are proved using the
universal properties of scheme pullbacks. No affineness is required here.

The auxiliary lemma `sheafify_range_eq_sup` computes a local image on two open
pieces covering its represented source, when the ambient presheaf is an fppf
sheaf. The two-member Zariski cover is also an fppf cover; the universal section
therefore belongs locally to the union of the two images. Naturality treats
every section, and the universal property of local closure gives the equality.
Here `sheafify` means local closure of a subfunctor inside the ambient presheaf.

For the saturation identity, suppose the presheaf square with projections
`π : G → F` and `p : G → h_B`, and bottom arrows `f : F → h_T` and `h_e`, is
cartesian. Suppose `a : h_V → G` has structure map `w`, so `a ≫ p = h_w`.
The arrow `newBase e w : chartRelation e w → B` uses the first coordinate of
the relation. The map `translate e w sq a ha` transports `a` to this coordinate
by the universal property of the given square. The theorem
`translate_isPullback` proves that it is the actual pullback of `a ≫ π` by
`π`. Its restriction along `diagonalChart e w` is `a`.

If `e` is separated etale and `G` is an fppf sheaf, `saturation_eq` states
that the inverse image under `π` of the local image of `a ≫ π` equals the
local closure of the union of the range of `a` and the range of the off-diagonal
restriction of `translate`. The proof uses the cartesian range/preimage
identity, commutation of local closure with inverse image, and the two-piece
source cover. It requires neither monomorphy of `f` nor openness of `a`.
The statement is therefore a presheaf generalization of the indicated source
identity, with its extra sheaf assumption stated explicitly.

The full representability induction and effective descent are not asserted
by this helper. The supporting `EtaleOffDiagonal` pair is unchanged from the
separately submitted helper by Worker 1150.
