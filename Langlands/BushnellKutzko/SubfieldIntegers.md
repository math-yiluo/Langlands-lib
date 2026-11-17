# A subfield `E` of `A = End_F(V)`: `𝔬_E`, `𝔭_E`, `e(E|F)` and `E → A` (Bushnell–Kutzko 1993, §1.2)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
§1.2, printed pp. 24–25 (PDF pp. 36–37; PDF page = printed page + 12).

BK93 §1.2 begins (p. 24): "suppose that, in addition to our hereditary order `𝔄` in `A`, we have
a subfield `E/F` of `A`. Thus we may view `V` as an `E`-vector space, via the given inclusion
`E → A`." Proposition (1.2.1) and (1.2.4) then use the ring of integers `𝔬_E`, its maximal ideal
`𝔭_E` and the ramification index `e(E|F)`. This module constructs these objects from `E`. It
imports only Mathlib.

## How `E` is represented

`E` is a field with an `F`-algebra structure (`[Field E] [Algebra F E]`). For the
embedding it also has an action on `V` compatible with that of `F`
(`[Module E V] [IsScalarTower F E V]`). A subfield `E` of `A` containing `F` fits this
description with `E` acting on `V` by evaluation. So does `E = F[β]` for `β ∈ A` when `F[β]` is
a field, which later tasks need. Conversely, when `V ≠ 0`, the action map `E → A` is an
injective `F`-algebra homomorphism, so `E` is isomorphic to its image, a subfield of `A`
containing `F`. When `V` is finite-dimensional over `F`, that image is finite over `F`.

No assumption about `E` beyond the field and algebra structure is made in this module. The
ring `𝔬_E`, the ideal `𝔭_E` and the integer `e(E|F)` are constructed, not supplied as extra
structure.

## `subfieldIntegers F E` (`𝔬_E`)

`subfieldIntegers F E : Subalgebra 𝒪[F] E` is the integral closure `integralClosure 𝒪[F] E` of
`𝔬_F = 𝒪[F]` in `E`. This requires only `[ValuativeRel F]`, so that `𝒪[F]` is defined. For a
finite extension `E` of a nonarchimedean local field `F`, the integral closure of `𝔬_F` in `E`
is the valuation ring `𝔬_E` of `E`, a discrete valuation ring. This standard fact is not
formalized here.

## `subfieldMaximalIdeal F E` (`𝔭_E`)

`subfieldMaximalIdeal F E : Ideal (subfieldIntegers F E)` is the Jacobson radical
`Ring.jacobson (subfieldIntegers F E)`. When `𝔬_E` is a discrete valuation ring, as above, this
is its unique maximal ideal `𝔭_E`. The Jacobson radical is used, rather than
`IsLocalRing.maximalIdeal`, because Mathlib has no `IsLocalRing` instance for an integral
closure. It is also the ideal used in the periodicity condition of
`LatticeChain (subfieldIntegers F E) E V`, so an `𝔬_E`-lattice chain in the sense of that
structure satisfies `L_{i+e'} = 𝔭_E L_i` with exactly this `𝔭_E`.

## `subfieldRamificationIndex F E` (`e(E|F)`)

`subfieldRamificationIndex F E : ℕ` is Mathlib's `Ideal.ramificationIdx` of
`subfieldMaximalIdeal F E` over `𝒪[F]`. For a prime ideal `q` of `S` over `R`, Mathlib defines
this as the length of `S_q / (q ∩ R) S_q` as an `S_q`-module. It is `0` when `q` is not prime.
For a finite extension `E/F` of nonarchimedean local fields, `q = 𝔭_E` and `q ∩ 𝔬_F = 𝔭_F`. The
length of `𝔬_E / 𝔭_F 𝔬_E` is then the integer `e` with `𝔭_F 𝔬_E = 𝔭_E^e`, the ramification
index `e(E|F)` used in BK93 (1.2.4) (p. 25).

## `subfieldEmbedding F E V` and `subfieldUnits F E V`

- `subfieldEmbedding F E V : E →ₐ[F] Module.End F V` is `Algebra.lsmul F F V`, the `F`-algebra
  map `a ↦ (v ↦ a • v)`. This is BK93's "given inclusion `E → A`" (p. 24).
  `subfieldEmbedding_apply` is the defining equation (`rfl`).
- `subfieldUnits F E V : Eˣ →* (Module.End F V)ˣ` is the induced map `E^× → G = Aut_F(V)`
  (`Units.map`). `coe_subfieldUnits` says that its value is the image of `a` under
  `subfieldEmbedding` (`rfl`). Statements about `E^× ⊆ 𝔎(𝔄)` are phrased with this map.

The centralizer `B = End_E(V)` of `E` in `A` (BK93 (1.2.2), p. 25) is Mathlib's
`Module.End E V`, embedded in `A` by `LinearMap.restrictScalars F`. It needs no separate
definition.
