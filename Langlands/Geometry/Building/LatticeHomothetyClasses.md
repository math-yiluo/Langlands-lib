# Lattices in \(F^n\) and their homothety classes

This module constructs the lattices of a vector space \(F^n\) over the valuation
ring \(\mathcal O_F\), their homothety classes, and the action of
\(\mathrm{GL}_n(F)\) on both. For a nonarchimedean local field \(F\) and
\(n=2\), the homothety classes are the vertices of the Bruhat–Tits tree of
\(\mathrm{GL}_2(F)\); the module
[`GeneralLinearTreeStatement`](GeneralLinearTreeStatement.md) states this
comparison for Kaletha–Prasad building data.

## Setting

`F` is a field with a valuative relation (`ValuativeRel F`), so that its
valuation ring `𝒪[F]` (Mathlib's `Valuation.integer` of `ValuativeRel.valuation F`)
is defined; `n` is a type, finite with decidable equality where matrices act.
Vectors are columns: \(F^n\) is `n → F` and a matrix \(g\) acts by
\(v\mapsto gv\) (`Matrix.mulVec`).

## Definitions

- **`ValuationRingLattice F n`**: a structure with an `𝒪[F]`-submodule
  `carrier` of `n → F` and a proof that it is a lattice in Mathlib's sense,
  `carrier.IsLattice F`: finitely generated over `𝒪[F]` and spanning `n → F`
  over `F`. Over a discrete valuation ring this is the usual notion: a finitely
  generated \(\mathcal O_F\)-submodule containing a basis of \(F^n\), which is then
  free of rank \(n\) (Mathlib's `Submodule.IsLattice.free` and
  `Submodule.IsLattice.rank_of_pi`).
- **`ValuationRingLattice.Homothetic L M`**: \(M=aL\) for some
  \(a\in F^\times\) (pointwise scalar multiple of the submodule).
- **`ValuationRingLattice.homothetySetoid F n`**: homothety as an equivalence
  relation (reflexive with \(a=1\), symmetric with \(a^{-1}\), transitive with
  \(ba\)).
- **`LatticeClass F n`**: the quotient of the lattices by homothety, the set of
  classes \([L]\); **`LatticeClass.mk L`** is the class of \(L\).
- **`glImage F n g L`**: for \(g\in\mathrm{GL}_n(F)\) and an
  `𝒪[F]`-submodule \(L\), the image \(gL=\{gv : v\in L\}\), the `Submodule.map` of
  \(L\) along the \(\mathcal O_F\)-linear map underlying \(v\mapsto gv\).
- **`MulAction (GL n F) (ValuationRingLattice F n)`**: \(g\cdot L=gL\).
- **`MulAction (GL n F) (LatticeClass F n)`**: \(g\cdot[L]=[gL]\).

## Proved properties

- `coe_glImage`: the underlying set of \(gL\) is the image of \(L\) under
  \(v\mapsto gv\).
- `mulVecLin_surjective`: \(v\mapsto gv\) is surjective for invertible \(g\)
  (with preimage \(g^{-1}w\)).
- `isLattice_glImage`: \(gL\) is a lattice when \(L\) is. Finite generation
  passes to images; the \(F\)-span of \(gL\) is the image under \(g\) of the
  \(F\)-span of \(L\) (`Submodule.span_image`), which is the image of all of
  \(F^n\), hence all of \(F^n\) by surjectivity.
- `glImage_one`, `glImage_mul`: \(1L=L\) and \((gh)L=g(hL)\), which give the
  action on lattices.
- `glImage_smul`: \(g(aL)=a(gL)\) for \(a\in F^\times\), because \(g\) is
  \(F\)-linear; so `ValuationRingLattice.Homothetic.smul`: homothetic lattices
  have homothetic images, and the action descends to classes.
- `LatticeClass.mk_surjective`, `LatticeClass.mk_eq_mk_iff` (two classes agree
  exactly when the lattices are homothetic), and `LatticeClass.smul_mk`
  (\(g\cdot[L]=[gL]\), by definition).

## Sources

The homothety classes of lattices as vertices are in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), 15.1.23, printed p. 521: the
vertices of the building of \(\mathrm{GL}(X)\) are the periodic lattice chains
whose segments are single lattices, that is, the chains \(\{\varpi^kL\}\) of one
homothety class. Proposition 15.1.31 (printed p. 523) and 15.1.33 (printed
p. 524) identify the stabilizer \(\mathrm{GL}(L)\) of a lattice \(L\) with the
stabilizer of the corresponding point of the extended building and with the
parahoric subgroup of the vertex of \([L]\). Mathlib's
`Mathlib.Algebra.Module.Lattice` defines `Submodule.IsLattice` and recalls the
same description of the tree; it does not define the homothety quotient, which
this module constructs.
