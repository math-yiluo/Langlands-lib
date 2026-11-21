# Rank-three skew Gram models with matching reduced norm

`QuaternionicRankThreeMatchedNormModelStatement` takes an invertible rank-three Gram matrix for standard conjugation on a central quaternion division algebra. Given any nonzero alternating element `c`, it produces an invertible antihermitian diagonal matrix with first entry `c` and the same reduced norm as the input matrix. The base field has invertible `2`.

The proof chooses an orthogonal division basis. If `p` is the reduced norm of its change-of-basis matrix and `b` is the ordered product of the three diagonal values, the reduced norm of the original Gram matrix multiplied by `p²` equals the quaternion norm of `b`. The quaternion `p⁻¹ • (b * c⁻¹)` consequently has norm equal to the original Gram norm divided by the quaternion norm of `c`. Factoring that quaternion into two pure elements supplies the second and third entries.

This is a derived construction for the prescribed diagonal in Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), §4.3, Lemma 4 and its sublemma, printed pp. 56–57 (PDF pp. 62–63). The ordered product of diagonal values already supplies the required quaternion norm representative over the ground field.
