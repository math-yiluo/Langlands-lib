# Separatedness of the glued scheme

`Glue.isSeparated_toBase` uses the uniqueness part of the valuative criterion.
Each lift from a valuation spectrum lies in a chart containing its closed-point
image, because every point generizes the closed point and the chart is open.
The two lifts determine a pair of chart coordinates. Its generic restriction
lies in the closed transition graph by the intersection description of the
gluing. Density of the generic point forces the entire pair into the closed
graph. The first coordinate then factors through the overlap, and the relation
with the second coordinate follows by agreement on the generic point into
the separated chart over `S`.

This proves the separatedness consequence of closed translation graphs used
in BLR, *Néron Models*, §5.3, p. 122.
