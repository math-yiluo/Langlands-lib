# Orbit maps onto reduced homogeneous schemes are faithfully flat

Authors: Worker 716 and Worker 1293. Worker 1293 proposed the interface (an
orbit map onto a supplied reduced scheme that is transitive on rational
points) for the closed-orbit step of the Borel route. Worker 716 wrote the
Lean statement and this text.

This pair states one proposition, `OrbitMapFaithfullyFlatStatement`, at
arbitrary universe `u`. It is not proved here; its proof is a separate
obligation.

## Statement

Fix an algebraically closed field `k : Type u`. The data are:

- a group scheme `G : GroupScheme (Spec (CommRingCat.of k))` whose structure
  morphism is locally of finite type and quasi-compact, so `G` is of finite type
  over `k`. No affineness, smoothness, reducedness or connectedness is assumed;
- a scheme `O` over `k` with `IsReduced O.left` and `LocallyOfFiniteType O.hom`;
- an action `a : SchemeAction G O`, the Library's categorical module-object
  action with its actual action morphism `G.X ⊗ O ⟶ O`;
- a rational point `x : 𝟙_ (Over (Spec k)) ⟶ O`.

The hypothesis is transitivity on rational points: every rational point
`y : 𝟙_ ⟶ O` equals `a.act g x` for some rational point `g : 𝟙_ ⟶ G.X`.

The orbit map is `a.act (𝟙 G.X) (toUnit G.X ≫ x) : G.X ⟶ O`. On `T`-points
it sends `g` to `g • x_T`, where `x_T` is the pullback of `x` to `T`. The
proposition asserts that its underlying scheme morphism is flat, surjective and
quasi-compact. `Flat`, `Surjective` and `QuasiCompact` are Mathlib's properties
of scheme morphisms. Surjectivity refers to all scheme points, not only rational
points.

By `SchemeAction.naturality`, `g ≫ (orbit map) = a.act g x` for a rational
point `g`. So the hypothesis says exactly that rational points of `O` lift along
the orbit map.

## Meaning of the hypotheses

- Reducedness of `O` cannot be dropped. For example `G = 1` acting on
  `O = Spec k[ε]/(ε²)` is transitive on rational points, but `Spec k ⟶ O` is
  not flat.
- No separatedness or quasi-separatedness of `O` is assumed. Since `O` is
  locally of finite type over a field, it is locally noetherian, hence its
  underlying space is quasi-separated. Together with quasi-compactness of `G`,
  this is what makes the orbit map quasi-compact.
- `O` is not assumed quasi-compact. The rational point `x` makes `O` nonempty.

## Provenance

The registered original is J. S. Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

- Proposition 7.4(a), printed p.139 (PDF p.155): let `G` be an algebraic group
  acting on an algebraic scheme `X`, and let `x ∈ X(k)`. If `X` is reduced and
  `G(k^a)` acts transitively on `X(k^a)`, then the orbit map `G → X` is
  faithfully flat and `O_x = X`.
- Proposition 1.65(a), printed pp.26–27 (PDF pp.42–43), is the general form
  for an equivariant map `X → Y` onto a reduced `Y`. Its proof is generic
  flatness (A.70) over a nonempty open `U` of `Y`, followed by covering `Y`
  with the translates `gU` for `g ∈ G(k)`.

This is a specialization, with the following differences in form:

- `k` is algebraically closed, so `k^a = k` and the transitivity hypothesis is
  about rational points of `O` over `k`.
- Milne's algebraic groups and algebraic schemes are of finite type over `k`.
  Here `G` is of finite type, but `O` is only locally of finite type. This
  makes the statement slightly more general.
- Milne's "faithfully flat" (A.68, printed p.582) means flat with `|φ|`
  surjective. Milne works with max spectra (A.1, A.11 and the dictionary
  A.22), so `|φ|` is the map on closed points. For schemes of finite
  type over a field this is equivalent to surjectivity on all scheme points,
  because the image is constructible and the schemes are Jacobson. The
  statement uses the scheme-point form.
- Quasi-compactness of the orbit map is automatic for Milne, since all his
  schemes are quasi-compact and locally noetherian. Here it is stated
  explicitly because consumers need it.
- Milne's statement also asserts `O_x = X`, meaning the orbit with its reduced
  structure is `X`. Since `X` is reduced, this is surjectivity.

The full registered author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`, was
read. Two entries are relevant. The p.26 entry says that in the proof of
1.65(a), `U` should be chosen before passing to the algebraic closure. Here
`k` is already algebraically closed, so no base change occurs. The p.582 entry
deletes "faithfully" from A.70, so generic flatness gives only a flat map over
`U`. The proof of 1.65(a) uses only that flatness, and surjectivity comes from
transitivity. Neither entry changes the statement. The p.570 entry (the proof
in footnote 3 needs correction) concerns the closedness claim in A.20, which
is not used here.

## Intended use

The consumer is the closed-orbit step of the Borel route for task
`6ec508b8-b9b5-401b-ab9f-c19fede905d0`. There, the flat surjective
quasi-compact orbit map onto a closed orbit feeds
`Langlands.GroupScheme.FiniteIndexQuotientProperTransferStatement` (a staged
statement unit of the same task), which requires such a map `π`. Constructing
the orbit with its action, proving its properness and the stabilizer fiber
relation remain separate obligations.
