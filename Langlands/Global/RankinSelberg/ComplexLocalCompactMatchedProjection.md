# Matched compact projections of inducing and Whittaker coefficients

This internal comparison implements the compatible compact projection in Jacquet §8.2 and §8.3. A continuous compact weight with finite span under left translation determines projected vectors in the actual complex standard module. Their compact restrictions are the indicated averages of the right-translated inducing functions.

The proof chooses the projections from the compact-picture existence theorem. It applies the Whittaker comparison using analytic regularity of smooth standard Lie intertwiners and preconnectedness of the invertible complex matrices. The standard Lie generator acts by the real right derivative used by the Library’s Whittaker intertwiner. This identifies the evaluated projection with the compact average of the Whittaker coefficient at all group elements, with the same weight and Haar measure as in the inducing-side average.
