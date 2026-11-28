# Haar measure on a product group modulo a product subgroup

Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), §I.2.9, printed p. 22 (PDF p. 30), uses
convolution with a chosen Haar measure on the central quotient of a factor in
a product of places. Section I.2.4, printed pp. 15–16 (PDF pp. 23–24), uses
the product of copies of the chosen group Haar measure in the corresponding
product of groups. The construction here applies that product normalization
to the factor quotients and allows one supplied measure for each factor.
Retained source `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.

`Langlands.QuotientIntegration.quotientGroupPiEquiv` identifies the actual
quotient group of `∏ᵢ Gᵢ` by `∏ᵢ Zᵢ` with `∏ᵢ (Gᵢ ⧸ Zᵢ)` for a family of
normal subgroups of topological groups. The homeomorphism uses the Library's
left-coset product homeomorphism and identifies each normal left-coset space
with its quotient group. Multiplication agrees componentwise on representatives.
The product subgroup is closed when each factor subgroup is closed and central
when each factor subgroup is central.

For a finite index type and the displayed Borel structures on the quotient
spaces, `quotientGroupPiMeasure` transports the product of the supplied
measures back to the actual quotient group. The factor quotients are second
countable so their product measurable space is Borel. With sigma-finite Haar
measures on the factors, Mathlib's finite product measure is Haar and the
continuous group isomorphism preserves this property on transport. The
rectangle formula gives the product of the supplied volumes for sigma-finite
factor measures. The Bochner integral formula evaluates a quotient integral
by composing with the inverse isomorphism and using the finite product measure.
