# Filtration steps of the values of a tame corestriction

Let `F` be a nonarchimedean local field, `E` a field extension of `F` acting on
a finite-dimensional `F`-vector space `V`, `A = End_F(V)` and `B = End_E(V)`.
Let `E^×` normalize the `𝔬_F`-lattice chain `𝓛`, and write
`𝔓^k = 𝓛.endFiltration k`. The module proves trace duality for a tame
corestriction `s : A → B`: `s(x) ∈ 𝔓^{1−k}` exactly when `tr_A(x y) ∈ 𝔭_F` for
every `E`-linear `y ∈ 𝔓^k`. All results are proved.

## Linear algebra (namespace `TraceAdjoint`)

- `restrictEnd`: restriction of scalars `B → A` as an `F`-linear map; it is
  injective (`restrictEnd_injective`).
- `traceForm ℓ`: the `F`-bilinear form `(b, b') ↦ ℓ(tr_B(b b'))` on `B`, for an
  `F`-linear form `ℓ` on `E`. It is nondegenerate when `ℓ ≠ 0`
  (`traceForm_nondegenerate`): for `x ≠ 0` and `x v ≠ 0`, the rank-one map
  `f ⊗ v` with `f(x v) = z`, `ℓ(z) ≠ 0`, gives `ℓ(tr_B(x (f ⊗ v))) = ℓ(z) ≠ 0`.
- `traceAdjoint ℓ hℓ : A →ₗ[F] B`, the map `s_ℓ` characterized by
  `ℓ(tr_B(s_ℓ(x) b)) = tr_A(x b)` for all `b ∈ B` (`traceAdjoint_spec`). It is a
  `(B, B)`-bimodule map (`traceAdjoint_mul_left`, `traceAdjoint_mul_right`).

## Conductor forms and images (namespace `TraceAdjoint`)

- `exists_conductor_form`: for `E/F` finite there is a nonzero `F`-linear form
  `ℓ` on `E` with `ℓ(z 𝔬_E) ⊆ 𝔭_F` exactly when `z ∈ 𝔭_E`. It is obtained by
  separating `1` from the finitely generated `𝔬_F`-submodule `𝔭_E` of `E`.
- `mem_extensionChain_endFiltration_iff_trace`: for such `ℓ` and `b ∈ B`, `b`
  lies in step `1 − k` of the chain over `𝔬_E` with the lattices of `𝓛`
  (`LatticeChain.extensionChain`) exactly when `ℓ(tr_B(b y)) ∈ 𝔭_F` for every
  `y` in step `k`.
- `traceAdjoint_image`: `s_ℓ(𝔓^n)` is the set of `b ∈ B` whose restriction of
  scalars lies in `𝔓^n`, for every `n ∈ ℤ`. One inclusion combines
  `traceAdjoint_spec` with trace duality for `𝓛`
  (`LatticeChain.mem_endFiltration_iff_trace_mul`). For the other, a `b` outside
  the image is separated from it by a form `y ↦ ℓ(tr_B(c y))`, and trace duality
  in `A` and in `B` gives a contradiction.
- `traceAdjointCorestriction`: `s_ℓ` as a `TameCorestriction 𝒪[F] F E V`.

The proof of `tameCorestriction` in the module `TameCorestrictionProof` uses a
similar trace-adjoint construction with private auxiliary definitions; this
module makes the construction public, as it needs the defining identity
`traceAdjoint_spec`.

## Trace duality for every tame corestriction

`TameCorestriction.restrictScalars_mem_endFiltration_iff_trace`: for a tame
corestriction `s` relative to `E/F` and `x ∈ A`, `s(x)` restricted to `F` lies
in `𝔓^{1−k}` exactly when `tr_A(x y) ∈ 𝔭_F` for every `E`-linear `y ∈ 𝔓^k`.
By `tameCorestriction`, `s` is a unit multiple of `s_ℓ` for a conductor form
`ℓ`, so it suffices to treat `s_ℓ`. For `s_ℓ` the claim is
`mem_extensionChain_endFiltration_iff_trace` combined with `traceAdjoint_spec`.

## Origin

Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (1.3.3)–(1.3.4), printed pp. 28–29 (PDF pp. 40–41), literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. There a
tame corestriction is defined by `ψ_A(a b) = ψ_B(s(a) b)` with additive
characters, and its images are computed by the duality (1.3.6). The module uses
the `F`-linear form `ℓ` in place of the additive character of `E`, with the
same duality argument.
