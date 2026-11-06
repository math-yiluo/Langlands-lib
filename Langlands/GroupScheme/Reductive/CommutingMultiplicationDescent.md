# Descent of surjective subgroup multiplication

This internal construction composes the existing base-change comparison for
actual subgroup multiplication with reflection of scheme-surjectivity. It
then specializes the finite-centre multiplication constructor over the original
field.

For any surjective morphism of schemes `b : S' ⟶ S` and group homomorphisms
`j : H ⟶ G`, `i : K ⟶ G`, the theorem
`surjective_subgroupMultiplication_of_baseChange` proves that the original
subgroup multiplication is scheme-surjective if multiplication of the
base-changed homomorphisms is scheme-surjective. There are no commutation,
closedness, flatness or smoothness hypotheses for this reflection theorem.
The proof uses `subgroupMultiplicationBaseChangeIso` and
`subgroupMultiplication_baseChange` to express the pulled-back morphism as
the composite of an isomorphism and the base-changed multiplication. Its
surjectivity then reflects by `surjective_overHom_of_baseChange`.

For a field extension `E/k` in any universe, the theorem
`surjective_subgroupMultiplication_of_fieldExtension` applies this reflection
to the surjective spectrum map supplied by `fieldExtension_fpqc`.

`semisimpleCommutingMultiplicationOfFieldExtension` takes a semisimple actual
group scheme `G` over `k`, closed subgroup inclusions `j` and `i`, smooth
connected factors `H` and `K`, commutation on every test scheme, finite full
scheme-theoretic centres of both factors, and scheme-surjectivity of the
base-changed multiplication over `E`. It returns the original actual
homomorphism `H ⊗ K ⟶ G`, together with its central-isogeny property and
semisimplicity of its actual product source. The value theorem identifies
the returned homomorphism with `commutingSubgroupMultiplicationHom j i hc`
by reflexivity. The constructor reflects surjectivity and invokes
`semisimpleCommutingMultiplication` with the unchanged original factors and maps.

These are internal consequences of the imported base-change, finite-centre
and central-isogeny interfaces. They neither construct a complement nor prove
its structural existence. Finite centres, original-factor smoothness and
connectedness, original all-test commutation, and multiplication surjectivity
after extension remain explicit inputs. No characteristic or perfectness
restriction is imposed, and smoothness of multiplication is not required.
