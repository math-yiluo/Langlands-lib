# Underlying points in pullbacks along étale analytic maps

`LocalizedEtalePullbackPointsStatement` says that any compatible pair of ordinary points lifts to a point of an analytic pullback when its first cospan leg is étale, with independent field and space universes. The theorem `localizedEtalePullbackPoints` proves the statement. The form `exists_point_of_isPullback_of_etale` can be applied directly to a pullback square and a compatible pair.

Write the cospan maps as right fractions. Their source denominators give homeomorphisms on ordinary points. Étaleness passes to the first numerator, and `exists_recognizedLocalizedPullback_point` lifts the transported point pair to a point of the recognized pullback of the numerators. The two projections composed with their denominators give a cone over the original arrows. Mapping this cone into the given pullback maps the lifted point to the required point.

This is derived infrastructure for the ordinary points of Berkovich's analytic fibre products, *Étale cohomology for non-Archimedean analytic spaces* (1993), Proposition 1.4.1, printed pp. 29–30 / PDF pp. 26–27. The registered source is `berkovich-1993-etale-cohomology`, SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
