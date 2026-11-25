# Extensions over noetherian local rings and neighbourhoods

`noetherianLocal_of_splitSpecialFiber` proves relative multiplicative type for
an exact split-endpoint extension over a noetherian local ring whose special
middle fibre is relatively diagonalizable. The exact fibral criterion,
complete-local deformation statement, and local character surjectivity are
explicit premises of this intermediate theorem.

Take the actual maximal-ideal adic completion. It is noetherian, local,
complete and flat, and its canonical ring map is local and therefore
faithfully flat. The natural map of residue fields and its actual
compatibility with reduction identify the iterated special-fibre pullbacks.
Base change of the supplied special-fibre diagonalization then gives a
specified diagonalization of the completed special fibre. The included
complete-local extension construction diagonalizes the whole completed
group. Fpqc descent from the supplied criterion gives relative multiplicative
type over the original local ring.

`noetherian_exists_diagonalizing_neighbourhood` works over any noetherian
coefficient ring at a prime whose middle residue fibre is of field-level
multiplicative type. The actual etale special-splitting construction produces
an etale algebra and a point with split residue fibre. This algebra is
noetherian. Localize at that point and apply the preceding completion
argument, keeping the exact quotient and split endpoints by base change.
The actual ordinary-localization limit presentation and local detection
construction spread the resulting relative multiplicative type to an
affine fppf diagonalizing neighbourhood. Composition with the etale map gives
the desired neighbourhood over the original coefficient ring and retains a
point above the chosen prime.

All scalar maps and special-fibre comparisons are actual maps of the supplied
groups. No strict henselization, Artin approximation, smoothness of the groups,
or uniform connectedness alternative is used. These are internal combinations
of the included constructions and the Library's completion, localization and
base-change results. The explicit premises are not proved in this module; the
Library proves the fibral criterion and the complete-local deformation statement
as `multiplicativeTypeFibralCriterion` and
`multiplicativeTypeCompleteLocalDeformation`.
