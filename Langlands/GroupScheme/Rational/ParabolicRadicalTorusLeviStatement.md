# A rational Levi adapted to a maximal torus in a parabolic

Authors: Worker 1361 and Worker 1348.

`ParabolicRadicalTorusLeviStatement.{u}` is an unproved structural proposition
over every field in universe `u`. Let `G` be connected reductive, let
`j : P → G` be an actual rational parabolic, and let `t : T → G` be an actual
rational maximal torus, with a specified factorization `f : T → P`.
The torus `T` need not split over the ground field.

The proposition asserts the existence of a represented geometric solvable
radical `r : R → P` and a commutative group scheme `S`, with maps `sT : S → T`
and `sR : S → R`. The map `sT` is closed, `sR` is a maximal torus of `R`,
and `sT ≫ f = sR ≫ r`. On every test scheme, their common image in `P`
is exactly the intersection of the images of `f` and `r`.

It also asserts the existence of an actual rational Levi `l : L → P`.
The composite `l ≫ j` represents the centralizer of the whole torus
`sT ≫ t` on every test scheme. A specified map `sL : S → L` satisfies
`sL ≫ l = sT ≫ f` and is a largest closed central subtorus of `L`.
Here `IsRationalLeviSubgroup` retains an actual scheme isomorphism for
multiplication with a geometric unipotent radical. The largest-central-torus
condition compares all actual closed central tori, without identifying the
entire possibly nonsmooth center with a torus.

The original source is Borel and Tits, *Groupes réductifs* (1965),
registered as `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
Section 3.14, printed p.80/PDF p.27, identifies rational Levis of a
connected subgroup of maximal rank with centralizers of rational maximal
tori of its radical, and identifies their connected centers with these
radical tori. Sections 4.2–4.3, printed pp.85–86/PDF pp.32–33, give the
standard-parabolic structure and connectedness. The proof of 4.15(b),
printed p.91/PDF p.38, explicitly uses `S' = R(P) ∩ T` as a rational maximal
torus of the radical and identifies its ambient centralizer as a rational
Levi with connected center `S'`. The proof of 4.18, printed p.92/PDF p.39,
applies the same intersection construction to a given rational maximal
torus, using 4.2, 4.3 and 2.15(d).

This is a derived scheme formulation of those results, rather than a
literal transcription. Represented radicals, the intersection equality,
the centralizer and the largest-central-torus comparison are stated on all
test schemes. Proving the proposition therefore includes the scheme
structure and descent comparisons implicit in passing from the source's
smooth reduced algebraic groups to these interfaces. The proposition
assumes no splitness or perfectness of the field, and no Levi or radical
existence premise. It does not prove any of these geometric assertions or
the minimal-parabolic split-part theorem. Worker 1348 contributed the
structural decomposition; Worker 1361 authored the interface and source
comparison.
