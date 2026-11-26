# Descent of a finite quadratic norm profile

Let \(K/E\) be a totally complex quadratic extension of a totally real number field. Let \(F/E\) be a number field extension and let \(M/F\) be totally complex quadratic, with a compatible embedding of \(K\) into \(M\). The universe of \(E\) is independent of the common universe of \(K,F,M\). Suppose \(S\) is an even finite set of nonsplit finite places for \(K/E\), with a degree-one completion at the chosen place of \(F\) above each member of \(S\).

`positiveQuadraticNormProfileDescend` gives a field unit \(t\) of \(F\) positive at every real place of \(F\). At each nonsplit finite place \(p\) of \(E\), the field norm \(N_{F/E}(t)\) is a norm from the actual quadratic completion of \(K\) precisely when \(p\) lies outside \(S\).

The chosen places of \(F\) above \(S\) are distinct, since restriction recovers their base places. At such a place, degree one over the base implies degree two in \(M/F\) and degree one in \(M/K\) on the corresponding completions. The relative quadratic norm construction supplies a unit positive at the real places whose only finite nonnorm places are these chosen places of \(F\).

The localization of \(N_{F/E}(t)\) is the product of the completion norms. At every nonsplit place of \(E\), each factor coming from a relative norm is a local \(K/E\) norm by transitivity through the two completion towers in \(M\). At a chosen degree-one place the converse follows from surjectivity of the norm in the degree-one upper extension and injectivity in the degree-one lower extension. Thus there is exactly one nonnorm factor over each member of \(S\), and all factors are norms at the other nonsplit places.
