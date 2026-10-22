# The cyclic Herbrand quotient of the idele class group

`Langlands.ClassField.Global.CyclicIdeleClassHerbrandQuotient` states the
number-field case of the first fundamental inequality in its stronger form:

For every cyclic Galois extension `E/F` of number fields, the groups
`H¹(Gal(E/F), C_E)` and `H²(Gal(E/F), C_E)` are finite, and

`|H²(Gal(E/F), C_E)| = [E : F] * |H¹(Gal(E/F), C_E)|`.

The declaration is a `Prop`-valued definition. This module contains no proof
of the proposition.

## Fields and actual cohomology

The fields `F : Type u` and `E : Type v` have independent arbitrary universes,
with `Field`, `NumberField`, and `Algebra F E` instances. Mathlib supplies
`FiniteDimensional F E` from these number-field assumptions. The additional
hypotheses are `IsGalois F E` and `IsCyclic (E ≃ₐ[F] E)`. Thus the acting group
is the actual finite cyclic Galois group; no generator is chosen and degree
one is included. The extension degree is `Module.finrank F E`.

The coefficients and cohomology are imported unchanged from
`Langlands.ClassField.Global.Cohomology`:
`relativeIdeleClassCohomology F E n` is Mathlib's ordinary group cohomology
of the additive wrapper of `NumberField.IdeleClassGroup (𝓞 E) E`, with its
published arithmetic action `relativeIdeleClassAut F E`. The coefficient
scalars are the published universe lift of the integers. Each cohomology
module is coerced to its carrier `Type v` to take its cardinality. No
alternative idele-class group, action, or cohomology model is introduced.

The conclusion contains `Finite` for degree one, `Finite` for degree two,
and the natural-number equality using `Nat.card`, in that order.
Finiteness is asserted rather than assumed: `Nat.card` is zero on infinite
carriers, so the equality alone would not state the finite Herbrand quotient.
Both cohomology groups have a zero element, so their finite cardinalities
are positive. Consequently the displayed equality is the division-free
form of `h²(C_E) / h¹(C_E) = [E : F]` and implies the usual lower bound
`h²(C_E) ≥ [E : F]`. These consequences are explanations of the statement;
they are not proved in this module. In particular, the statement does not
assert `H¹ = 0`, nor does it assert the second fundamental inequality.

## Source correspondence

Source: Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea
Publishing, 2009, registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The retained source is
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.

- Preliminaries §3, printed p.5 (PDF p.14), defines the Herbrand quotient
  only when the two indices are finite, and identifies these indices for a
  finite cyclic group with the orders of ordinary `H²` and `H¹`.
- Chapter V §1, Theorem 1, printed p.11 (PDF p.20), gives
  `h²(G, C_K) = n * h¹(G, C_K)` for a cyclic global-field extension `K/k`
  of degree `n`, using the natural Galois action on idele classes.
- Chapter V §4, opening paragraph, printed p.16 (PDF p.25), explicitly
  recalls that Theorem 1 proves this equality, beyond the lower bound.

The Lean field names `F`, `E` correspond to the source's `k`, `K`.
This is the number-field specialization of the source theorem; function
fields are outside this statement. The explicit finiteness conjuncts make
the source's finite-index convention part of the formal conclusion, and
multiplication avoids introducing a rational-valued quotient.
