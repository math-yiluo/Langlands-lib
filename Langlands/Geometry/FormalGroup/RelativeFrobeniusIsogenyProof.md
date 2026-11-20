# The relative Frobenius isogeny and its represented kernel rank

`Langlands.FormalGroup.ModuleLaw.relativeFrobeniusIsogeny` proves the full
`RelativeFrobeniusIsogenyStatement` for the actual `frobeniusHom`. Write
`q = p^n`. Evaluation after coefficient extension takes the `q`-th power of
each nilpotent coordinate.

For any coordinate tuple `a` over an algebra `A`, the proof forms
`A[T_i]/(T_i^q - a_i)`. It compares this quotient with the tensor product
of the individual `AdjoinRoot (X^q - C (a_i))` algebras. Evaluation at the
roots defines the maps on the quotient and the individual factors. The
inverse identities follow by checking the generators of the quotient and of
each tensor factor. The one-variable monic power bases give a basis of the
quotient indexed by `σ → Fin q`. Over the zero ring, the corresponding
modules are subsingletons and admit a basis with the same index set.

For a nilpotent target point over `A`, take `a_i` to be its coordinates.
The quotient is finitely presented by the finite family of power relations.
The basis has a nonempty index set since `q > 0`, so it gives faithful
flatness. Each universal root is nilpotent because its `q`-th power is the
image of a nilpotent coordinate. Their tuple is the required lift.

For the kernel, take all `a_i = 0` over `R`. An `R`-algebra homomorphism
from this truncated algebra to a test algebra sends the universal roots
to a point of the actual kernel. Conversely, evaluating polynomials at the
coordinates of a kernel point defines its classifying homomorphism. The
inverse identities use the coordinate generators and point extensionality.
Naturality follows by composing the coefficient maps on the universal
point. The basis gives finite projectivity and stalkwise rank
`q ^ Nat.card σ = p ^ (n * Nat.card σ)`. The empty coordinate set and
`q = 1` both give a single basis index.

This is an internal structural result for the Library's actual coordinate
Frobenius. Its motivation is the natural Frobenius quasi-isogeny that appears
in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 A, printed
p. 109, project source `drinfeld-1976-coverings-p-adic-symmetric-regions`.
