# Upper triangular differentiation of the full infinite compact evaluation

`infiniteCoefficientLieAt` places the sum of the actual block Lie operators at one real or complex place in that place's slot of the full infinite coefficient tensor.

At the infinite compact identity, the evaluation after an upper triangular Lie operator on a standard factor is the sum of two terms. The first is the half-character derivative times the original evaluation. The second applies `infiniteCoefficientLieAt` with the diagonal block directions. The pointwise local derivative law holds at the chosen place, and the other place evaluations are unchanged. The proof tensors the local linear map identity using multilinearity in that single slot.

This is an internal comparison for Task 6553 in the normalized scalar compact model of Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283). Flath (1979), §2, pp. 180–181 (PDF 176–177), gives the tensor product context. The Lean proof uses the Library's actual infinite compact coordinates and the local derivative formulas into the cuspidal coefficient spaces.
