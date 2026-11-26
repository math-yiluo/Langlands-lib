# Conjugating a perturbation of a simple stratum onto a second chain

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, proof of (2.4.5), printed p. 68 (PDF p. 80). There the perturbation `b'` of a simple element `γ'` is written as `b' ≡ a_{γ'}(x) (mod 𝔓''^{−r''})` and `β'` is conjugated by `1 + x`. Remark (ii) after (1.1.9), printed p. 24, gives `𝔓' ⊆ 𝔄''`. This module proves these steps in the Library's chain model, together with the invariance of simple strata under conjugation that they require.

## Conjugation by a unit of an order

- `conjAlgHom g` is the algebra endomorphism `x ↦ g⁻¹ x g` of `End_F(V)`. It is injective (`conjAlgHom_injective`) and maps `F[β]` onto `F[g⁻¹βg]` (`elementAlgebra_conj`).
- Suppose `g` and `g⁻¹` lie in the order of a chain `𝓛`. Then conjugation preserves every filtration step (`mem_endFiltration_conj_iff`), `g` normalizes the chain (`mem_stabilizer_of_mem_order`), and conjugation preserves valuations (`valuation_conj`). It also preserves the inclusions of adjoint lattices defining critical indices (`adjointLattice_le_conj`), hence critical exponents (`criticalExponent_conj`).
- `conjStratum T g` is `[𝓛,n,r,g⁻¹ T.b g]`. `isSimple_conjStratum`: it is simple when `T` is. The field part uses the Library's `normalizingUnits_conj` and `isField_of_normalizingUnits`.
- `elementInvariants_conj`: `F[g⁻¹βg]` has the ramification index and residue degree of `F[β]` (`subfieldInvariants_of_algEquiv`).

## The conjugation step

- `normalized_of_generated`: if `S` is pure and `β : E` with `F[β] = E` acts as `S.b`, then `Eˣ` normalizes `S.chain`.
- `exists_adjoint_eq_of_corestriction_eq_zero` (BK93 (1.4.10), printed p. 38): for `S = [𝓛,n,r,γ]` simple, every `z ∈ 𝔓^{−r}` with `s(z) = 0` is `γy − yγ` for some `y ∈ 𝔓^1`. If `γ` is not a scalar, this is middle exactness of the third sequence of T2 (`adjointExactness`) with `m = 1`, `k = −r−1`, followed by `centralizerLattice_mul_adjointLattice_le`. If `γ` is a scalar, the kernel of `s` is the range of the zero commutator (`TameCorestriction.range_adjointMap_eq_ker`).
- `exists_conj_sub_mem` (the conjugation step of (2.4.5)): let `𝓛'` be a second chain normalized by `E`, `b ∈ 𝔓^{−r}(𝓛)` and `s(b) ∈ 𝔓^{−ρ}(𝓛')`. Then there are `p ∈ 𝔓^{−r}(𝓛) ∩ 𝔓^{−ρ}(𝓛')` with `s(p) = s(b)` and `g ∈ U¹(𝓛)` with `g(γ + b)g⁻¹ ≡ γ + p (mod 𝔓^{1−r}(𝓛))`. The element `p` comes from `exists_corestriction_eq_of_mem`. Next, `b − p = γy − yγ` with `y ∈ 𝔓^1`, and `g = 1 + y` (`exists_mem_unitFiltration`). Then `g(γ + b) − (γ + p)g = yb − py`, which lies in `𝔓^{1−r}(𝓛)`, and `g⁻¹` lies in the order.
- `one_add_mem_order_of_sandwiched`: if every lattice of `𝓛'` lies between two consecutive lattices of `𝓛`, then `1 + y` preserves every lattice of `𝓛'` for `y ∈ 𝔓^1(𝓛)`. This is the incidence relation of Remark (ii) after (1.1.9).
