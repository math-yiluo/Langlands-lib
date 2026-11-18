# Commutativity of the analytification tensor square

This internal derived helper proves that the tensor-product inclusion square
commutes for complete strong arrows, saturated atlas morphisms, and localized
morphisms. The appropriate published functoriality propositions are explicit
hypotheses at both required universe instantiations.

The implemented proof identifies each composite with the strong, saturated, or
localized arrow induced by the corresponding composite algebra map. The two
composite algebra maps agree by the balancing relation of the relative tensor
product, as proved in `TensorLiftComparison.include_comp`.

This supplies only square commutativity. Existence and uniqueness for arbitrary
localized test objects are separate parts of the fibre-product proof.
