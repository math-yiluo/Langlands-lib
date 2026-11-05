# Faithfulness of the original real archimedean differential

This internal helper uses the unchanged original `ArchimedeanGL.SmoothFunctions`
and its actual real directional differential. For every real continuous linear
functional on the original mixed-coordinate matrix algebra, `smoothRealLinearTest`
restricts its complex-valued real inclusion to the original general-linear group.
The existing units chart proves this is an original smooth function.

At the identity its derivative in a real Lie direction is the functional
evaluated on the original matrix representing that direction. This follows
from `smoothDifferential_eq_of_extension` using the continuous linear functional
as the ambient extension. Since continuous real linear functionals separate
points of the real normed matrix space, equality of differential operators
implies equality of real directions. The proof includes rank zero and uses no
assumed faithfulness or supplied replacement action.
