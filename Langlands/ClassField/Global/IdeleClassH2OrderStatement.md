# The order bound for second idele-class cohomology

`Langlands.ClassField.Global.IdeleClassH2OrderBound.{u,v}` states that, for
every Galois extension `E/F` of number fields, the actual group
`H²(Gal(E/F), C_E)` is finite and its order divides `[E:F]`.
This is a `Prop`-valued definition; the module does not prove the assertion.

## Formal meaning

The fields `F : Type u` and `E : Type v` have independent arbitrary
universes. The hypotheses are their field and number-field structures, an
`Algebra F E` structure, and `IsGalois F E`. Finite dimensionality of `E`
over `F` follows from the number-field assumptions. The statement includes
degree one and does not require the Galois group to be cyclic.

The imported `relativeIdeleClassCohomology F E 2` is Mathlib's ordinary
degree-two group cohomology of
`relativeIdeleClassRepresentation F E`. Its coefficients are the additive
wrapper of the genuine quotient `NumberField.IdeleClassGroup (𝓞 E) E`,
with the published arithmetic Galois action and the published universe
lift of the integers as scalars. The module introduces no substitute
coefficient group, action, or cohomology theory.

The two conclusions are `Finite` for the carrier of this cohomology module
and the natural-number divisibility
`Nat.card (relativeIdeleClassCohomology F E 2) ∣ Module.finrank F E`.
Finiteness is a conclusion, not an assumption. The divisibility has the
cohomology order on the left and the field degree on the right.
No invariant maps, equality of orders, cyclicity of the cohomology group,
or compatibility of cohomology maps is asserted.

## Source correspondence

Source: Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea
Publishing, 2009, registered as `artin-tate-2009-class-field-theory`,
SHA256 `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The retained original is
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.

Chapter XIV §2, Lemma 1, printed pp.147–148 (PDF pp.156–157), gives the
reduction of an order divisibility in positive-degree cohomology to cyclic
prime-degree layers, assuming exact inflation–restriction sequences.
The proof uses induction through normal subgroups for prime-power layers
and detection on the primary components by Sylow restriction for general
layers. The end of §2, printed p.148, supplies the degree-two exact
sequence when degree-one cohomology vanishes.

Chapter XIV §3, printed pp.151–152 (PDF pp.160–161), applies that lemma
with `r = 2` and exponent `ν = 1`. After establishing the field-formation
property and the cyclic prime-degree second inequality, the source
concludes that the order of `H²(K/F)` divides `[K:F]` for every normal
layer. The idele-class formation is the global case under discussion.
The Lean fields `E/F` correspond to the source's `K/F`; the statement
specializes this conclusion to number fields and makes its finite-order
meaning explicit.

This is the cohomological order bound needed before constructing the
general global invariant. The norm-index second inequality and the cyclic
Herbrand-quotient formula are separate prerequisites; this declaration
neither assumes a proof of the global invariant theorem nor supplies one.
