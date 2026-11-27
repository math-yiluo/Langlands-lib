# Smooth extension from a finite word-seminorm bound

`RealSmoothIntertwinerWordExtensionStatement` uses two jointly continuous
representations of the actual real general linear group on complex Banach
spaces. An algebraic carrier is identified with all the genuine
compact-finite smooth vectors of the first representation by an equivalence
that intertwines the compact action and Lie derivatives. A linear map from
the algebraic carrier into the second genuine smooth carrier also
intertwines those actions. Given a bound on its underlying norm by a finite
sum of genuine source word seminorms, there is a unique continuous
full-group intertwiner of the genuine smooth carriers extending it.
The three carrier universes are independent.

The proof applies the given norm estimate to the algebraic derived vector
for each fixed word. The intertwining identities identify its values with
the genuine derivatives in each model. This bounds each coordinate of the
map by a continuous function of the source that vanishes at zero, and the
word topology gives continuity on the compact-finite source. The dense
compact-finite inclusion and completeness of the target smooth carrier
give the extension. Equality on the dense source implies uniqueness and
extends the compact and Lie identities. The real group integration theorem
then gives equivariance under every group element.

This is the extension argument of `SmoothCasselmanWallachBound` applied to
a supplied estimate on one map. The hypotheses concern the actual source
realization, target smooth maps and norm estimate, and permit reducible
source modules. In particular, `realPrincipalSeriesSmoothExtension_of_wordBound`
applies the argument to the genuine compact Banach model of the scalar
minimal principal series under `RealPrincipalSeriesWordBoundStatement`.
