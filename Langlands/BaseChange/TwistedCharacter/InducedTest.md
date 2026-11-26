# A common inducing-group test for twisted induced traces

The ambient group and the inducing group are Hausdorff locally compact
totally disconnected groups with Borel measures. The ambient measure is left
invariant and finite on compacts, and the inducing measure is two-sided Haar.
The ambient automorphism is continuous in both directions and has finite order.
It preserves a closed subgroup with compact left quotient. A continuous open
homomorphism to the inducing group intertwines the two automorphisms.

For every ambient test, `twistedInducedTest` chooses a test on the inducing
group before choosing a representation or its twisting operator. It computes
the ambient trace of the actual unnormalized smooth induction for every
admissible inducing pair whose induced action is admissible.

The proof chooses an invariant compact open subgroup for which the ambient
test is bi-invariant. Evaluation on a finite double-coset transversal
identifies the induced fixed space with a product of coefficient fixed spaces.
The coefficient subgroups are the images of the compact open double-coset
stabilizers under the open homomorphism. Expressing the integrated action
by its finite action samples gives matrix entries on the product. At a
fixed output coordinate, projection by the normalized coefficient indicator
preserves the combined output and makes each individual sample an operator
to the coefficient fixed space.

Cyclicity of trace eliminates the entries connecting distinct summands.
For a diagonal sample the coefficient is the trace of the indicator projection
after the action of the automorphism's image of the inducing element and the
given twisting operator. Right translation of the indicator by the inverse
of that image gives the corresponding test. The sum of these tests with the
ambient sample coefficients works for every inducing pair.

Choosing the inducing tests on a basis of ambient tests and extending
linearly gives a map of test spaces. Its transpose sends each inducing
twisted distribution to its induced twisted distribution, so every linear
relation among the inducing distributions passes to the ambient group.

Rogawski (1988), §3, p. 218, and Henniart–Lemaire (2011), II.4.4,
p. 85, use the same twist on induced sections, applying the inducing
operator to the value of the section at the inverse automorphism.
Their normalized models include a half modulus in the covariance law.
When the half modulus descends to an invariant character of the inducing
group, one can absorb it into the inducing action in the unnormalized
model used here. The common-test identity is derived from the finite
double-coset calculation above.
