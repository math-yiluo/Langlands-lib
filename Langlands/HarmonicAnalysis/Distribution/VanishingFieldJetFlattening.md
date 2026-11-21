# Flattening finite jets by iterating a vanishing vector field

Suppose a smooth vector field and its scalar correction vanish on a set, and
the derivative of the field is nilpotent at every point of that set. For every
integer \(k\), one power of the corrected field derivative makes all jets of
orders below \(k\) vanish there, for every smooth compactly supported test.
`VanishingFieldJetFlatteningStatement` records this uniform power.

Once the lower jets of a test vanish at a point, the next jet of the corrected
derivative is the linearized field acting in each jet slot and summed over the
slots. The scalar correction contributes zero to that jet. The slot sum is
nilpotent with a bound determined by the jet order and the finite dimension of
the space. Iterating through successive orders therefore kills every required
jet, and the lower jets remain zero at each step.

This is an internal regularization input for extending Whittaker distributions
near lower real Bruhat cells. It uses the same linearized field computation as
the support vanishing argument.
