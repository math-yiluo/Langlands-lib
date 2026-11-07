# Deep-unit linearization for rank-one stability

Worker 1786 constructs the additive character `x -> chi(1+x)` on a deep
lattice and proves the exact order of its linearization parameter.
These are internal derived constructions supporting the unchanged
rank-one stability target. The finite lattice duality dependency adapts
Worker 784's published implementation, as explained in
`RankOneStabilityHelpers.md`.

For `m > 0` and `x in L_(-m)`, `valuation_one_add` proves that `1+x`
has valuation one. The actual unit `oneAddUnit` has underlying field
element `1+x`, and `oneAddUnit_mem` puts it in `U^m`.

The primary construction `deepLatticeCharacter` takes a quasicharacter
trivial on `U^a`, together with `a <= 2*m`. It returns an actual complex
additive character of `L_(-m)` with value `chi(1+x)`. Indeed,

```text
(1+x)(1+y)/(1+x+y) - 1 = xy/(1+x+y).
```

The denominator has valuation one and the numerator has depth at least
`2*m >= a`; hence the multiplicative discrepancy lies in `U^a`, where
`chi` is trivial. `deepLatticeCharacter_trivial` proves that the constructed
character is trivial on the deeper lattice `L_(-a)`.

For the actual conductor `a = a(chi)`, `exists_deep_linearization`
assumes `0 < m < a` and `a <= 2*m`. Finite lattice duality gives a field
element `c` satisfying `chi(1+x) = psi.complex(c*x)` on `L_(-m)`.
The conductor annihilator theorem puts `c` in `L_(n+a)`.
Minimality of `a` supplies a unit in `U^(a-1)` on which `chi` is
nontrivial; since `m <= a-1`, its difference from one belongs to the
linearization domain. This excludes `c=0` and `c in L_(n+a-1)`.
Discreteness then forces `ord(c) = -(a+n)`.

The argument uses `1+x` only on this sufficiently deep lattice. No
claim is made that it realizes a truncated exponential at other depths.
The prime, carrier universe, and supplied topology are unrestricted.
