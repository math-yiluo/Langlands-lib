# Formal maps over affine global sections

The structure sheaf of an affine spectrum has global section algebra canonically isomorphic to the original coefficient algebra. `globalCoefficientEquiv` uses this isomorphism over the ring of formal-module scalars.

For coordinate formal modules over the affine base, an integral homomorphism over the full structure sections thus gives an integral homomorphism over the original ring. `Hom.ofGlobalCoefficients` applies the inverse coefficient isomorphism and identifies the resulting source and target laws with the original ones. Extending the result back to the structure sections recovers the initial homomorphism. Faithfulness of this extension follows from injectivity of the coefficient isomorphism on every series coefficient.

This is an affine coefficient comparison for the local-coordinate formal groups used in Drinfeld 1976, §1, printed pp. 108–109.
