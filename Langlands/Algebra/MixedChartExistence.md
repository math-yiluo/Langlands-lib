# Mixed-character window data through a field point

`Langlands.Algebra.MixedChartExistence.WindowDatum` extends the
mixed-character `Datum` with two additional conditions: the chosen
finite comodule window has all weights in the mixed box, and the
character reduction is injective on bounded sums of that box.
This is ring-level data; it is not a subgroup chart scheme.

`exists_window_extension` starts with a commutative finitely
presented Hopf algebra `A/R`, a finite `R`-submodule `V` with a
coassociative comodule map compatible with the comultiplication of
`A`, generators lying in `V`, and an explicit bounded presentation
of degree at most `N₀`, with `1 ≤ N₀`. It also assumes a
closed-immersion Hopf point over a field, a prescribed weight box,
injectivity of reduction on its bounded sums, and a point of the
finite-character Hom algebra giving that reduced Hopf point.
It extends the original mixed-character point over a principal open
of the Hom algebra, preserving the weight and support bounds,
scalar-extension surjectivity, the universal reduction equation,
and the exact specialization to the original field point.

The proof applies the published window-extension theorem at the
residue field of the given point. Uniqueness of the bounded
extension gives the required specialization. Weight control and
surjectivity each hold after a further principal localization.
Writing the product of their denominators over the original algebra
combines these localizations into one principal open.

`exists_windowDatum` drops the prescribed box and modulus but
retains the finite comodule-window and bounded-presentation inputs
above. It places the finitely many weights in a mixed box and chooses
a modulus sufficiently large for both rigidity and bounded-sum
injectivity. Multiplying by the cardinality of `F` makes the modulus
annihilate `F`; its positivity is proved explicitly. The window
extension then supplies `f` and the extended Hopf point. The
published invariant-open construction supplies `N`, invariant under
the finite automorphism group, whose nonvanishing locus is covered
by translates of `D(f)` and contains the given point. These objects
form the required `WindowDatum`.

The module also proves containment of bounded sums in larger mixed
boxes and that every finite mixed-character support lies in some
box. All these are internal derived constructions, adapted from
`TorusChartExistence` using mixed-character rigidity and the existing
generic weight-window and invariant-localization results. It proves
neither existence of the finite comodule-window inputs in general
nor the scheme-level multiplicative-type chart-cover statement.
