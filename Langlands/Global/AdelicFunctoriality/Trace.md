# Adelic traces and the additive character `ψ ∘ Tr`

## Contents

For a finite extension `L / K` of number fields, the module constructs the adelic trace
`A_L → A_K`. Its coordinate at a place `p` of `K` is `Σ_{q | p} Tr_{L_q / K_p}(a_q)`. From a
nontrivial additive character `ψ` of `A_K` trivial on `K`, it builds the character
`ψ ∘ Tr` of `A_L`. The module proves that `ψ ∘ Tr` is nontrivial and trivial on `L`, and
that at a finite place `q` above `p` its component is the component of `ψ` at `p`
composed with the local trace. This construction supports the proof of
`RelativeWeilTwistFunctionalEquationStatement`: there the Hecke functional equation over
an intermediate field `K` of `E / F` is applied with the additive character `ψ ∘ Tr_{K/F}`.

The constructions follow the published adelic norm (`Langlands.Global.AdelicFunctoriality.Norm`),
with traces in place of norms. All names below are in namespace
`Langlands.Global.AdelicFunctoriality`.

### Linear algebra

- `trace_baseChange`: for a field `K`, a `K`-algebra `A` and a finite `K`-algebra `B`,
  `Tr_{A ⊗ B / A}(1 ⊗ x) = Tr_{B/K}(x)` in `A`.
- `trace_pi`: the trace of an element of a finite product of finite algebras over a field is
  the sum of the traces of its coordinates.
- `trace_tensor_pi`: if `e : A ⊗[K] B ≃ₐ[A] Π_i C_i`, then
  `Σ_i Tr_{C_i/A}(e(1 ⊗ x)_i) = Tr_{B/K}(x)`.

### Local traces

- `FiniteExtension.localTrace p q`: the trace `L_q → K_p`, as a `K_p`-linear map, for a finite
  place `q` of `L` above a finite place `p` of `K`, with the published algebra structure given
  by `FiniteExtension.completionMap`. `continuous_localTrace` states its continuity.
- `FiniteExtension.localTrace_completionMap_mul`: `Tr(c · x) = c · Tr(x)` for `c ∈ K_p`.
  `FiniteExtension.localTrace_completionMap`: `Tr(c) = [L_q : K_p] · c` for `c ∈ K_p`.
- `FiniteExtension.localTrace_integral`: the local trace maps the completed integers of `L_q`
  into those of `K_p`.
- `InfiniteExtension.localTrace p q` and `InfiniteExtension.continuous_localTrace`: the same
  for an infinite place `q` of `L` above an infinite place `p` of `K`.

### Adelic traces

- `finiteTraceComponent p`: `a ↦ Σ_{q | p} Tr_{L_q/K_p}(a_q)` on families of local
  coordinates; it is continuous, and integral when the coordinates above `p` are.
- `finiteAdeleTrace : FiniteAdeleRing (𝓞 L) L →+ FiniteAdeleRing (𝓞 K) K`, with
  `finiteAdeleTrace_apply` and `continuous_finiteAdeleTrace`.
- `infiniteAdeleTrace : InfiniteAdeleRing L →+ InfiniteAdeleRing K`, with
  `infiniteAdeleTrace_apply` and `continuous_infiniteAdeleTrace`.
- `adeleTrace : AdeleRing (𝓞 L) L →+ AdeleRing (𝓞 K) K`, the product of the two; this is the
  main definition. `adeleTrace_fst`, `adeleTrace_snd` and `continuous_adeleTrace`.
- `infiniteTrace_principal`, `finiteTrace_principal`: for `x ∈ L`, the sum of the local traces
  of `x` over the places above `p` is `Tr_{L/K}(x)`. Hence `finiteAdeleTrace_principal` and
  `adeleTrace_principal`: the trace of the principal adele of `x` is the principal adele of
  `Tr_{L/K}(x)`.
- `finiteAdeleInclusion_apply_above`: at a place `q` above `p`, the published inclusion of finite
  adeles `finiteAdeleInclusion` is `completionMap p q` applied to the coordinate at `p`.
  `finiteAdeleTrace_inclusion_mul`: `Tr(ι(a) · y) = a · Tr(y)` for `a` a finite adele of `K`.
- `finiteAdeleTrace_single`: the trace of the finite adele supported at `q` with value `x` is
  supported at `p`, with value `Tr_{L_q/K_p}(x)`. This holds for every decidable-equality
  instance on the places.

### The character `ψ ∘ Tr`

`Adeles` and `diagonal` are the published `Langlands.Global.Adeles` and
`Langlands.Global.diagonal`.

- `exists_finiteAdele_ne_one`: a nontrivial unitary additive character `ψ` of `A_K` trivial on
  `K` takes a value different from `1` at some adele whose infinite part is `0`.
- `exists_adeleTrace_eq_of_fst_eq_zero`: every adele of `K` with infinite part `0` is the
  adelic trace of an adele of `L`.
- `traceAdditiveCharacter ψ hψ`: for `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)`
  and `hψ : ∀ x : K, ψ (diagonal K x) = 1`, the unitary additive character `ψ ∘ adeleTrace` of
  `A_L`. Continuity is that of `ψ` and of the trace. Nontriviality comes from the two
  preceding results. `traceAdditiveCharacter_apply` states `(ψ ∘ Tr)(a) = ψ(Tr a)`.
- `traceAdditiveCharacter_diagonal`: `ψ ∘ Tr` is trivial on `L`.
- `traceAdditiveCharacter_single`: for `q` above `p` and `x ∈ L_q`, `ψ ∘ Tr` at the adele
  `(0, x at q)` equals `ψ` at the adele `(0, Tr_{L_q/K_p}(x) at p)`. This is the identity
  that relates the component of `ψ ∘ Tr` at `q`, in the sense of the published
  `IsFiniteAdditiveComponent`, to the component of `ψ` at `p` composed with the local trace.
  The module does not itself state that comparison of components.

## Source and provenance

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), 3–26
(registered `tate-1979-number-theoretic-background`). Printed page `p` is PDF page `p + 9`.
Theorem (3.4.1) and (3.4.8), printed pp.14–15, use the additive character `ψ ∘ Tr_{E/F}` of a
finite extension `E` of a local field `F`. Section (3.5), printed pp.15–16, uses a nontrivial
additive character of `A_F / F` and its local components. The adelic character `ψ ∘ Tr` is
the global form of the same operation. This module is derived: it constructs the global
trace as a product of local traces, in the same way as the published adelic norm, and proves
the properties the functional-equation argument needs. The principal formula uses the
published tensor decompositions `K_p ⊗_K L ≅ Π_{q | p} L_q` (`finiteTensorMap`, bijective
by the published `normCompatibility`, and `infiniteTensorEquiv`).

## Proof

- `trace_baseChange` uses `Algebra.baseChange_lmul` and `LinearMap.trace_baseChange`.
  `trace_pi` is an induction on the finite index type through `Fintype.induction_empty_option`
  and `Algebra.trace_prod_apply`, transported along `Algebra.trace_eq_of_algEquiv`.
  `trace_tensor_pi` combines them.
- `continuous_localTrace` (both kinds) uses `LinearMap.continuous_of_finiteDimensional`. At
  infinite places a local `NontriviallyNormedField` instance on the completion is supplied, as
  in the published `InfiniteExtension`.
- `localTrace_integral`: the completed integers of `L_q` are a finite module over those of
  `K_p` (the published `IntegralTopology.localFinite`, which uses the published integral
  tensor decomposition). Every element is therefore integral over the integers of `K_p`.
  `Algebra.isIntegral_trace` makes its trace integral, and
  `Valuation.Integers.isIntegral_iff_v_le_one` puts the trace in the valuation ring.
- `finiteAdeleTrace` lands in the restricted product because only finitely many places of `K`
  lie under the finitely many places where an adele of `L` is not integral. Continuity is
  proved from `RestrictedProduct.continuous_dom` exactly as for `finiteAdeleNorm`.
- `finiteTrace_principal` and `infiniteTrace_principal` apply `trace_tensor_pi` to the
  tensor decompositions at `p`; `adeleTrace_principal` combines the coordinates.
- `finiteAdeleInclusion_apply_above` substitutes the place under `q` by `p`
  (`finitePlacesAbove_under`). `finiteAdeleTrace_inclusion_mul` then uses
  `localTrace_completionMap_mul` coordinatewise.
- `finiteAdeleTrace_single`: at `p` only the summand for `q` is nonzero, and at a place
  `p' ≠ p` no place above `p'` equals `q`, by `finitePlacesAbove_under`.
- `exists_finiteAdele_ne_one`: otherwise `ψ(a) = ψ(a_∞, 0)` for every adele `a`. The map
  `x ↦ ψ(x, 0)` is continuous on the infinite adeles and equals `1` on the image of `K`,
  because `ψ` is trivial on `K`. That image is dense
  (`NumberField.InfiniteAdeleRing.denseRange_algebraMap`), so `ψ` would be trivial.
- `exists_adeleTrace_eq_of_fst_eq_zero`: for `a = (0, a_f)`, take
  `b = (0, ι(a_f) · [L : K]⁻¹)`. By `finiteAdeleTrace_inclusion_mul`,
  `finiteAdeleTrace_principal` and `Algebra.trace_algebraMap`, `Tr(b) = (0, a_f)`.
- `traceAdditiveCharacter_diagonal` is `adeleTrace_principal` and the triviality of `ψ` on
  `K`. `traceAdditiveCharacter_single` is `finiteAdeleTrace_single` with
  `infiniteAdeleTrace 0 = 0`.
