# Finite locally free number-field S-integer extension

This derived construction supplies the number-field arithmetic input to the
integral Weil restriction in Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), Example 4.2, printed pages 9–10. It concerns the actual S-integer
subrings of the original number fields and the original field embedding. The
upper exceptional set is the full inverse image of the lower finite exceptional
set. The rings and their extension algebra are those already constructed in
`ArithmeticSIntegerExtension`.

The scoped instances in `NumberFieldSIntegers` prove that the lower ring is
Dedekind and the upper ring is its integral closure in the upper field, finite,
torsion-free and projective as a module over the lower ring. Lower Noetherianity
and the dimension bound reuse `adelicSIntegersNoetherian`. To prove integral
closedness, an element integral over the lower S-integer ring remains integral
over every required valuation ring. Integral closedness of that valuation ring
puts the element in it. These memberships construct an actual lower S-integer.
The already proved integral-closure equality supplies the upper closure instance.
Finite separable normalization over a normal Noetherian ring gives module
finiteness. Embedding into the upper field gives torsion-freeness. A torsion-free
module over a Dedekind domain is flat; finiteness over the Noetherian lower ring
gives finite presentation, so the module is projective.

`numberFieldSIntegers_local_free` explicitly proves freeness after localization
at each prime of the actual lower ring. The localized module is finite and flat
over a local ring. Together with module finiteness, these statements give the
finite locally free extension used in the source. The module's generic rank is
the original field degree, as recorded by `numberFieldSIntegers_finrank_eq` using
the two original fraction fields.

`numberFieldSIntegersFractionTensorEquiv` constructs the original generic-fiber
algebra: tensoring the upper S-integer ring with the lower field over the lower
S-integer ring gives the original upper field. It reuses
`integralClosureFractionTensorEquiv`, which localizes the actual integral closure
at all nonzero lower elements. The pure-tensor formula sends a tensor of a lower
field element and an upper integer to the product of the original field image
and that integer's underlying upper-field element. Thus the identification
preserves the specified original coefficient maps.

Both fields inhabit an arbitrary common universe. The finite exceptional set
may be empty. These statements address the finite places; the S-integer rings
do not use archimedean places. The function-field finite-local-freeness input,
actual S-integer Weil generic-fiber scheme comparison, and adelic topological
comparison remain obligations of the host task.
