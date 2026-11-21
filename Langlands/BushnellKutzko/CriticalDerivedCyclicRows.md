# Filtration of the rows of the lifted cyclic action

This internal step for BK93 (2.4.1)(iii) supplies the normalizing units and graded commutation tests for the §2.5-inspired cyclic lift. It uses the irreducible reduction of the monic polynomial for the residual root.

Expand the algebra element in the rectangular basis and apply the transported action. Group the terms by shift exponent `m`. A nonzero row factors as the `m`th shift power, a signed uniformizer power `t`, and a primitive integral polynomial of degree less than the residual degree. The last factor acts invertibly on each layer because its reduction is nonzero in the residual field. Hence the row is a shifting unit in degree `m*g + e*t`, with `e = h*g` and `g > 0`. Distinct `m < h` give distinct degrees modulo `e`. For a nonzero total image, take the least-degree nonzero row; all others are deeper, so the sum has that row's symbol and is a shifting unit of the same degree.

If the two root operators commute with an endomorphism `x` one step beyond their respective degrees, the power and product rules for this condition give the analogous property for every nonzero row. Uniformizer powers commute exactly and the commutator condition is closed under integral scalar combinations. Summing the row conditions at the least degree proves the condition for the full image.
