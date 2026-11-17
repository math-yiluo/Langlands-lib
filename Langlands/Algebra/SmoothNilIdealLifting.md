# Lifting smooth algebra maps through arbitrary nil kernels

Worker 869.

This is an internal algebraic consequence of finite presentation, the
nilpotence of finitely generated nil ideals, and Mathlib's lifting theorem
for formally smooth algebras through nilpotent ideals. It uses no
classification or group-scheme theorem.

`LiftsThrough (A := A) q` is the proposition that every `R`-algebra
map from `A` to the target of `q` lifts along `q`. The accompanying
lemmas establish this property under the hypotheses described below.

`exists_finite_kernel_lift` starts with a finitely presented algebra `A`
over `R`, an algebra map `A → C`, and a surjective algebra map `B → C`.
Choose a finite polynomial presentation of `A` and lift the images of
its variables to `B`. The images of a finite generating set of the
presentation's relation ideal generate an ideal `J` in the kernel of
`B → C`. The provisional polynomial map descends to a map `A → B/J`
whose composition to `C` is the given map.

If the kernel consists of nilpotent elements, this finitely generated
ideal `J` is nilpotent. `exists_lift_of_nil_kernel` then applies formal
smoothness to lift `A → B/J` to `B`. The resulting map composes exactly
to the original map to `C`. `exists_lift_of_nil_ideal` specializes this
construction to `B → B/I` for any `I` contained in the nilradical.
There is no assumption that the entire kernel or `I` is nilpotent.

All rings may lie in independent universes. No locality, noetherianity,
or characteristic assumption is made.
