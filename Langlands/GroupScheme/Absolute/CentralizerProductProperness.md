# Properness of the actual intersection quotient

Internal supporting construction by Worker 1438 for the centralizer–Borel
intersection argument. This specializes `HomogeneousClosedImmersion` to the
actual comparison constructed in `CentralizerProductQuotient`. The included
unchanged homogeneous helper credits Worker 716 for its adapted generic-flatness
covering argument.

For actual group-scheme maps `j : M → G` and `b : B → G`, the supplied quotient
maps are `q : G → Q` and `r : M → R`. Their exact fiber hypotheses hold on every
relative test scheme: the differences of two group points lie respectively in
the actual ranges of `b` and `subgroupIntersectionFst j b`. The construction
`intersectionQuotientAction` is the left action on `R` obtained from the
published categorical quotient action. `intersectionQuotientBasepoint` is the
actual identity section of `M` followed by `r`.

Over an arbitrary base, with both projections flat, surjective and
quasi-compact and with `j` monic, `intersectionQuotientMap_equivariant` proves
equivariance between this action and the action on `Q` restricted along `j`.
The proof tests equality after an fpqc local lift through `r`. Multiplication
computes the source and target actions on that lift, and the actual comparison
factorization gives equality.

Over an algebraically closed field in arbitrary universe, assume `M` and `R`
are locally of finite type. Scheme-surjectivity of `r` gives a rational lift of
each rational point of `R` by `HomogeneousClosedImmersion.exists_rational_lift`.
Acting on the identity coset by this lift gives the prescribed point. Thus
`intersectionQuotientAction_transitive` proves rational transitivity without
assuming surjectivity on the points of every test scheme.

The closed-immersion theorem assumes that both subgroup maps are monic, `M` is
smooth, the quotient projections are smooth, surjective and quasi-compact,
`R` is quasi-compact over the field, and `Q` is locally of finite type. It also
retains the actual closed-product hypothesis:
`range (productHom j b)` is closed in `G`. Smoothness of `R` follows by smooth
surjective source descent applied to `r`; smoothness over the field then makes
`R` reduced. The previously proved comparison monicity and closed-image
theorem, together with equivariance and rational transitivity, meet every
hypothesis of `HomogeneousClosedImmersion.isClosedImmersion_of_closed_range`.
The resulting closed immersion has no additional immersion premise.

Finally, `intersection_quotient_isProper_of_product_closed` assumes properness
of `Q` over the field. This supplies its local finite-type condition. The
structure map of `R` factors through the proved closed immersion and the
proper structure map of `Q`, so it is proper.

Both actual quotient models, their all-test exact fibers, and closedness of the
actual multiplication image remain inputs. This module supplies no proof of
product closedness, quotient existence, or the centralizer–Borel statement.
