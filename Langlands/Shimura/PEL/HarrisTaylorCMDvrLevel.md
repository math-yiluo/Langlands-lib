# Extending the actual pointed Harris level over a DVR

`extendDvrHarrisLevel` extends a fixed orbit for the actual canonical
base change of a given positive polarized action on a good model over a
DVR. At each original Harris level it gives a fixed orbit on the model
and an equation identifying its existing level pullback with the
specified generic orbit.

The ambient generic frame supplies a frame on the model via the actual
adelic Tate comparison at the composite geometric point. This is the
frame existence used by the canonical polarized action base change.
The fraction-field map surjects on the pointed finite étale fundamental
groups. The Library's fixed-orbit pullback theorem therefore supplies
surjectivity at the actual level, from which the construction chooses a
preimage and obtains the pullback equation.

This is a derived specialization of the actual Harris level pullback
and the DVR monodromy surjectivity result. The given polarized action
and the chosen changed-dual data determine the level comparison.
