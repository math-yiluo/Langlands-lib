# Removing the Jacobian from a chart distribution

`jacobianNormalizedChartDistribution` evaluates a local test after dividing it by the positive chart Jacobian and transporting it to the ambient space. Multiplying a test by the Jacobian recovers ordinary chart restriction.

Suppose an ambient distribution annihilates derivatives along a finite family of trace-zero linear fields, and a constant coordinate direction pushes forward to a variable linear combination of these fields. In chart coordinates the Leibniz rule gives a correction from the derivatives of the combination weights. The Jacobian derivative is the Jacobian times this correction. Applying the original identity to the test divided by the Jacobian then shows that the normalized distribution annihilates the constant coordinate derivative.

The construction is an auxiliary step for local real matrix conjugation descent. Here the trace-zero fields are the ambient commutator fields.
