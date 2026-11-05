# Affine coordinates for defining-ideal descent

Internal deductions from Mathlib's affine ideal-sheaf equivalence and the
ideal-sheaf pullback/pushforward adjunction. On affine schemes, pushforward
contracts the ideal on global sections. The adjunction consequently shows that
pullback extends that ideal. No flatness or reducedness is assumed.

`ofGlobalIdeal` converts equality between the extension of a global ideal and
the global ideal of a specified ideal sheaf into actual `DefiningIdealDescent`
data. This is a scheme adapter; the algebraic ideal equality is still a premise.
