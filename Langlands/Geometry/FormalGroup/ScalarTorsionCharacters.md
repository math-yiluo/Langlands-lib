# Relative Cartier characters of scalar-power torsion

Let `M` be a coordinated formal `O`-module with `IsPiDivisible π` over
a commutative `O`-algebra `R`. At each exponent, `torsionCharacters`
applies the Library's relative Cartier character functor to the
commutative group scheme of the actual kernel of `[π^n]`. Its value
on a test scheme over `Spec R` is the additive group of homomorphisms
from the corresponding base-changed kernel to the multiplicative
group over that test scheme, expressed by the Library's relative Hom.

`torsionCharacterTower` goes from exponent `n` to `m` for `m ≤ n` by
restriction along the kernel inclusion. `torsionCharacterInclusions`
goes from `m` to `n` by pulling back along multiplication by `π^(n-m)`.
The functors are the compositions of the actual kernel group-scheme
diagrams with the contravariant relative Hom functor into the
multiplicative group. The evaluation equations follow from the
Library's evaluation lemma for precomposition.

The construction uses the relative character presheaves themselves.
Representing the presheaves by finite flat schemes and identifying
their biduals are further mathematical assertions.
