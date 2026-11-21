# The absolute Galois character anti-equivalence for field tori

`TorusAbsoluteCharacterEquivalenceStatement.{u}` asserts that for every
field `k : Type u`, `FieldTorus.characterFunctor k` is an equivalence
from `(FieldTorus k)ᵒᵖ` to `FreeDiscreteGaloisModule.{u,u} k`. The source
uses actual tori over `Spec k` and all group-scheme homomorphisms over `k`.
The target uses finite free integral modules with continuous action of
`Gal(kˢ/k)` in the Krull topology on the group and the discrete topology
on the module. Morphisms are equivariant integral linear maps.

The functor uses the actual character lattice of `T` over `kˢ` and the
canonical Galois action. It sends a homomorphism to pullback of characters.
`IsEquivalence` expresses full faithfulness and essential surjectivity
for this specific functor.

## Provenance

Milne, *Algebraic Groups* (2017), §12.g and Theorem 12.23, printed pp.
239–240 (PDF pp. 255–256), describe the anti-equivalence for all groups
of multiplicative type and identify the tori with the torsion-free
character objects. Finitely generated torsion-free `ℤ`-modules are finite
free. This statement gives the equivalence on the resulting full
subcategories. The torus property is Milne's Definition 12.14, printed
p. 236 (PDF p. 252).

The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
