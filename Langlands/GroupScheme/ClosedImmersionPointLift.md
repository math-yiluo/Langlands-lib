# Points that factor through a closed immersion

Module `Langlands.GroupScheme.ClosedImmersionPointLift`, namespace `Langlands.GroupScheme`.

## Contents

- `exists_comp_eq_of_evaluation_eq_zero`: let `H` and `G` be group schemes over `Spec k` for a
  field `k`, with affine total spaces, and let `j : H ⟶ G` be a morphism whose underlying morphism
  of schemes is a closed immersion. Let `B` be a commutative `k`-algebra in the universe of `k`
  and `x` a `B`-point of `G` (`G.affinePoints`). If every global regular function `a` of `G`
  whose pullback along `j` vanishes also vanishes at `x` (`G.affinePointEvaluation x a = 0`),
  then `x = y ≫ j` for a `B`-point `y` of `H`.

## Proof

Write `π` for the pullback of global regular functions along `j`. It is surjective because `j`
is a closed immersion of affine schemes
(`IsClosedImmersion.isAffine_surjective_of_isAffine`). The point `x` is a `k`-algebra map `φ`
from the coordinate ring of `G` to `B` (`affineSchemePointEquiv`). By hypothesis `φ` vanishes on
the kernel of `π`, so it factors through the coordinate ring of `H`, which is the quotient by
that kernel (`Ideal.Quotient.liftₐ`, `Ideal.quotientKerAlgEquivOfSurjective`). The factor `ψ`
is a `B`-point `y` of `H`. The points `y ≫ j` and `x` have the same evaluation on every regular
function (`affinePointEvaluation_postcomp`), so they agree
(`affinePointEvaluation_injective`).

This is the description of the points of a closed subscheme of an affine scheme as the points
killed by its ideal.
