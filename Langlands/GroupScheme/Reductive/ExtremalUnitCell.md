# The unit cell of the constructed negative-rho coefficient

This derived companion supplies the actual normalized diagonal coefficient
to the previously constructed negative-rho unit-cell lift. It retains the
representation, diagonal cocharacter equality, unique minimum coordinate
and prescribed restricted negative-rho weight from `ExtremalNegativeRho`.
It also retains the connected reductive group, split maximal torus, actual
root datum, full integral coroot span, represented dynamic parabolic and
centralizer, closed parabolic inclusion, normalizing point with the
prescribed action and represented conjugate opposite parabolic.

The diagonal coefficient is a nonzerodivisor on any connected reductive
group over a field. This uses its already proved value one at the identity
and the existing theorem that the coordinate algebra is a domain. It
requires no weight hypothesis on the supplied representation.

On any relative scheme test, a product of points of the two opposite
parabolics has unit value under the coefficient. Its two covariance laws
and identity normalization express that value as the product of the two
negative-rho character values, each a global unit. This implication needs
neither algebraic closedness nor a Bruhat covering.

Over an algebraically closed field, retain the supplied Borel-torus Bruhat
covering. The definition `extremalNegativeRhoUnitCellLift` applies the
existing actual global lift to the constructed coefficient and its proved
covariance laws. Multiplication of the lift recovers the original point.
The existing all-test factorization theorem then supplies global points of
the two opposite parabolics. Combining both implications identifies the
unit-valued points of the coefficient exactly with these products, on
every original relative test scheme, including nonaffine and nonreduced
schemes.

These are internal constructions using the established normalization,
covariance and geometric lift results; no new external source is invoked.
The structural subgroups, root datum, Bruhat covering and representation
with the prescribed weight remain inputs. This file proves no existence
of these data and no irreducibility or cofinality statement for the entire
covariant function spaces, and does not prove `SteinbergBigCellStatement`.
