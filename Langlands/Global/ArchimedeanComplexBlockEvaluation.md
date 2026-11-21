# Compact block tensor evaluation for complex standard modules

The ambient complex standard module has the concatenated list of characters in the original block order. At any included index its position character is the character of the corresponding block index. Padding a block torus element with identity entries gives the correct block diagonal matrix. For phases the extra modulus factors in the full principal-series character equal one, so the padded character is the principal-series character of the chosen block.

Restricting an ambient vector to the unitary subgroup of one block gives a continuous function. Its right translates lie in the image of the ambient vector's finite-dimensional compact orbit span. The phase identity gives the compact left transformation required by `complexPrincipalSeriesExtension`. This extension gives a block standard function, and uniqueness from the unitary restriction makes the slice linear. The algebraic compact evaluation then assembles these slices at each compact argument into the tensor of the original block standard modules.

`complexEvaluation_value` recovers the original function on the compact block product through any compact base point. `complexEvaluation_left` and `complexEvaluation_right` give the corresponding compact translation laws. The compact restrictions determine the original function, which proves `complexEvaluation_separates`.

This is an internal comparison for the compact model of normalized induction. It uses the function-level induction-in-stages comparison in Knapp and Vogan (1995), Chapter XI, (11.196), and the scalar compact model of Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283).
