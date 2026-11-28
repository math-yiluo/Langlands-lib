# Effective descent of smooth group schemes along extensions of discrete valuation rings

The module `Langlands.GroupScheme.Descent.DvrSmoothEffectivityStatement` states the group
scheme case of Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §6.5 Theorem 1,
printed p. 157 (literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`). The module states a proposition and proves nothing.

## The proposition

`Langlands.GroupScheme.Descent.DvrSmoothGroupSchemeDescentStatement.{u}` quantifies over

- types `R R' : Type u` which are domains and discrete valuation rings
  (`IsDomain`, `IsDiscreteValuationRing`), with an algebra structure `Algebra R R'` making
  `R'` a faithfully flat `R`-module (`Module.FaithfullyFlat R R'`);
- a group scheme `G : GroupScheme (Spec R')` (the Library's `Grp (Over (Spec R'))`, with its
  actual multiplication, unit and inverse) whose structure morphism `G.X.hom` is smooth,
  separated, locally of finite type and quasi-compact, that is, `G` is smooth, separated and
  of finite type over `R'`;
- an actual Čech descent datum `D : Datum p G` along
  `p := Spec.map (CommRingCat.ofHom (algebraMap R R')) : Spec R' ⟶ Spec R`
  (module `Langlands.GroupScheme.Descent.Data`).

It asserts that there are a solution `s : Solution D` and the four properties `Smooth`,
`IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` of the structure morphism
`s.obj.X.hom` of the descended group scheme `s.obj : GroupScheme (Spec R)`.

By the definitions of `Langlands.GroupScheme.Descent.Data`:

- `D.overlap` is an isomorphism of group schemes over `Spec R' ×_{Spec R} Spec R'` from the
  pullback of `G` along the first projection to its pullback along the second projection,
  and `D.cocycle` is the cocycle condition on the triple overlap: the pullback along `p12`
  followed by the pullback along `p23` equals the pullback along `p13`.
- A solution `s` consists of a group scheme `s.obj` over `Spec R`, an isomorphism of group
  schemes `s.iso` from the base change of `s.obj` along `p` to `G`, and the compatibility of
  `s.iso` with the canonical datum of the base change and with `D`.

## Correspondence with the source

BLR 6.5/1: let `R → R'` be a faithfully flat extension of discrete valuation rings (resp. of
fields), let `G'` be an `R'`-group scheme which is smooth, separated and of finite type over
`R'`, and let `X'` be an `R'`-torsor under `G'`; assume there are descent data with respect
to `R → R'` on `G'` and `X'` compatible with the group structure of `G'` and with the action
of `G'` on `X'`. Then `G'` descends to an `R`-group scheme `G` and `X'` to an `R`-torsor `X`
under `G`; by the properties of descent, `G` and `X` are smooth, separated and of finite type
over `R`.

- Only the group scheme and the case of discrete valuation rings are stated: the torsor `X'`
  of the source is omitted, and the case of fields is not stated. BLR remark (printed
  pp. 159–160) that the group is handled as the trivial torsor under itself.
- A descent datum on a scheme is defined in BLR §6.1, printed pp. 131–132, as an isomorphism
  `φ : p₁*G' → p₂*G'` satisfying the cocycle condition `p₁₃*φ = p₂₃*φ ∘ p₁₂*φ`; BLR §6.5,
  printed p. 156, require of a descent datum on a group scheme that it be compatible with the
  group multiplication, that is, that `φ` be an isomorphism of group schemes over
  `S'' = S' ×_S S'`. The Library's `Datum` is exactly such an isomorphism of group schemes
  with this cocycle condition, written in diagrammatic order.
- The descent of `G'` to `G` (the effectivity of the datum, BLR §6.1, printed pp. 132 and 135) with its
  group structure is recorded by `Solution D`: an `R`-group scheme with an isomorphism of
  group schemes from its base change to `G'` which carries the canonical datum to `D`.
- "Of finite type" is expressed as locally of finite type and quasi-compact, for the given
  group scheme and for the descended one. The four properties of the descended group are
  part of BLR's assertion.
- Both rings, and hence both spectra, are in the same universe `u`. Mathlib's
  `IsDiscreteValuationRing` presupposes `IsDomain`, which is assumed for both rings.

BLR prove 6.5/1 on printed pp. 159–162: the descent is effective on generic fibres by a limit
argument and Galois descent; it is effective under the additional assumption that there is an
`R'`-dense open subscheme stable under the datum on which the descent is effective, using the
quasi-projectivity of torsors (BLR §6.4) and the descent of schemes with an ample invertible
sheaf (BLR §6.1 Theorem 7, printed p. 138); and the general case is reduced to that one.

## Use

BLR use 6.5/1 in the proof of §6.5 Corollary 2 (printed pp. 157–158), the descent of solutions
of strict birational group laws from a strict henselization, stated in the Library as
`Langlands.AlgebraicGeometry.StrictBirationalGroupLawSolutionDescentStatement`.
