# Localizing an integral closure by tensoring the base with a localization

`integralClosureTensorLocalizationMap` maps the integral closure
in a tower of algebras to the integral closure after localizing
the scalars in both algebras by tensor product. This map comes
from the ambient localization and the original integral equation.
Both tensor products localize at the images of the scalar
denominators. The localization property of integral closure
then identifies the new closure as a localization of the old one.

At a prime of the new closure, the local ring is the localization
of the original closure at the contracted prime. The comparison
is obtained by composing the two localizations. If the original
closure is integral over the original scalar ring, every prime
of the localized closure over the chosen base prime is maximal.
Indeed, a strict inclusion into a larger prime would give a
strict inclusion after contraction by incomparability, and the
inverted scalars prevent the contraction from growing past the
chosen prime.

These comparisons are derived steps for using local ramification
results at the generic points of the normalized fibres in
Conrad's appendix to Prasad–Yu, *On quasi-reductive group schemes*,
author preprint, Remark A.7 on printed and PDF p. 30. The registered
source is `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
