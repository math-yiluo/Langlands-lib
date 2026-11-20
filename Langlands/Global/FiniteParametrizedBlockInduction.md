# Finite adelic induction with standard compact parameters

A section in `FiniteParametrizedBlockInduction.Sections F B σ` is a
function of the standard compact argument at infinity and the finite
adelic matrix argument. It takes values in the algebraic tensor of the
finite adelic block representations `σ`. It transforms on the left
under the finite block parabolic by the block tensor action and the
positive half-modulus. The half-modulus is the restriction of the
actual adelic half-modulus through the inclusion of the finite factor.

Each entire section has one open right stabilizer in the finite
adelic group. `induced` is the resulting right-translation action on
the finite variable. `sectionOf` constructs an element from the covariance
and a uniform stabilizer. Evaluation at all pairs determines the section.

This is a derived section model for the finite-place reading of the
cuspidally induced realization in Langlands, *On the notion of an
automorphic representation*, Corvallis Part I (1979), printed pp. 204–205
(PDF pp. 199–200), source `langlands-1979-notion-automorphic-representation`.
The proof of Proposition 2 there uses cuspidal Levi slices of a constant term
and chooses a cuspidal coefficient summand. The model here retains the
standard compact argument at infinity for evaluation of those slices. The
action and all section covariance in this module concern the finite group.
