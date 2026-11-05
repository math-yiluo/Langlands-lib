# Complex extension of a real Lie homomorphism

For any real Lie algebra `L` and associative complex algebra `A`, equipped
with a compatible real algebra structure, `linear` extends a real-linear
map `L → A` to the actual tensor product `ℂ ⊗[ℝ] L`. Its value on
`z ⊗ X` is `z • ρ X`.

When `ρ` is a real Lie homomorphism into the associative commutator Lie
algebra of `A`, `lie` equips this same tensor extension with its complex Lie
law. Double tensor induction reduces that law to the original real Lie
law, the actual scalar-extension bracket formula and distributivity.

`enveloping` applies Mathlib's universal property to this complex Lie map.
Its domain is `UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)`, and it is a unital
complex algebra homomorphism. The two generator formulas identify its value
on any canonical Lie generator and on `ι (1 ⊗ X)`, respectively.

This is internal algebraic content. Its tensor-induction route generalizes
the existing implementation in `Langlands.Global.ArchimedeanEnvelopingAction`
from matrix differentials to any given real Lie map. No manifold derivative
or Lie law for an arbitrary differential operator is assumed by this helper:
the input Lie law must already be supplied. The independent universes of
`L` and `A` are retained.
