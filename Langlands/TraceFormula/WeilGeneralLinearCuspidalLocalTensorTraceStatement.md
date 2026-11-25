# The local (twisted) trace factor of a cuspidal summand of `Res_{L/K} GL_n` at any finite place (statement)

Module `Langlands.TraceFormula.WeilGeneralLinearCuspidalLocalTensorTraceStatement`, namespace
`Langlands.TraceFormula`. It contains one definition, one proposition definition, and no proof:

- `Langlands.TraceFormula.tensorPullbackRepresentation`;
- `Langlands.TraceFormula.WeilGeneralLinearCuspidalLocalTensorTraceStatement.{u, uV}`.

Let `L/K` be a finite extension of number fields, `σ ∈ Aut(L/K)` and `W = Res_{L/K} GL_{r+1}`.
`Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement` asserts
that the traces on an irreducible cuspidal summand `P` of `L²([W])` split off, at a finite place
`v` of `K`, the character of *some* irreducible admissible representation of `W(K_v)`, and, for a
twist `Θ` preserving `P`, the twisted character of that representation for *some* intertwiner.
This module identifies that local factor at an **arbitrary** finite place `v` of `K`: it is the
tensor product, over all places `w` of `L` above `v`, of the Library's local components at `w`
of a cuspidal operator realization `R` over `L` attached to `P` (as in
`WeilGeneralLinearCuspidalSummandRealizationStatement`), viewed as a representation of
`GL_{r+1}(K_v ⊗_K L)` through `K_v ⊗_K L ≅ ∏_{w | v} L_w`. For the Galois twist `Θ` attached to
`σ`, the intertwiner is a `SigmaIntertwiner` for `σ_v = id ⊗ σ`. When `v` has exactly one place
above it, this is the content of `WeilGeneralLinearCuspidalLocalTwistedTraceStatement`,
up to the canonical isomorphism of a one-factor tensor product with its factor; that
module keeps the concrete form used at non-split places.

The module declares the `local instance`s `IsAffine` and `Smooth` for the general linear group
scheme (from `GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement`) and five `local instance`s of `AddCommGroup` on the
Library's form spaces `Langlands.Automorphic.RationalInvariantFunctions`,
`ContinuousRationalFunctions`, `FiniteSmoothRationalFunctions`, `AutomorphicForms` and on the
carrier of a `LocalRealization`, exactly as `WeilGeneralLinearCuspidalLocalTwistedTraceStatement`
and `GeneralLinearCuspidalLocalComponentTraceStatement` do. They are not exported. The proposition carries
`set_option maxHeartbeats 1000000`, because elaborating the whole statement exceeds the default
limit.

## The definition `tensorPullbackRepresentation`

For a commutative ring `A`, an index type `J`, commutative rings `B i`, ring maps
`h i : A →+* B i`, `ℂ`-modules `V i` and representations `ρ i` of `GL_n(B i)` on `V i`,

`tensorPullbackRepresentation n h ρ : Representation ℂ (GeneralLinear n A) (⨂[ℂ] i, V i)`

is the representation `g ↦ ⨂ᵢ ρ i (h i (g))` of `GL_n(A)` on the tensor product of the `V i`,
where `h i (g)` applies `h i` to every matrix entry (`Matrix.GeneralLinearGroup.map (h i)`). In
Lean it is Mathlib's `PiTensorProduct.mapMonoidHom` composed with the product
`MonoidHom.pi fun i => (ρ i).comp (Matrix.GeneralLinearGroup.map (h i))`. The Library's
`Langlands.BaseChange.splitTensorRep ρ` (module `Langlands.BaseChange.SplitPlace`) is, by
definition, the special case `J = Fin l`, `B i = F`, `h i` the `i`-th coordinate projection
`Fin l → F` to `F` and `ρ i = ρ` for all `i`. The definition is used here with `J` the finite
set of places above `v`; it is stated for any index type, as `PiTensorProduct` is.

## Setting and notation from the Library

Global data, realizations, `S`, `πc`, `R_S(f)`, `R(f)`, `IsTraceClass`, `operatorTrace`,
`P_P X ι_P` (for `P.orthogonalProjectionOnto ∘L X ∘L P.subtypeL`), `R`, `Ψ`, `IsWeilFormClass`,
`D : CuspidalSpectralPresentation.{u, uV} R` and its local components `D.localComponent w`:
exactly as in `WeilGeneralLinearCuspidalLocalTwistedTraceStatement` (see its Markdown).

Places and local groups.

- `v : Langlands.Global.FinitePlace K` is any finite place and `.inr v` the corresponding element
  of `Place K`. `FinitePlacesAbove L v` (module `Langlands.Global.AdelicFunctoriality.Norm`) is
  the type of finite places of `L` above `v`; it is finite (instance
  `finitePlacesAbove_finite`). For `w : FinitePlacesAbove L v`, `w.1` is the place of `L`.
- `atPlace K W (.inr v)`, `ofPlace K W (.inr v)`, `localPointsEquiv K L (r + 1) (.inr v)` and
  `gv g := localPointsEquiv K L (r + 1) (.inr v) (atPlace K W (.inr v) g)` are as in
  `WeilGeneralLinearCuspidalLocalTwistedTraceStatement`; `E_v = K_v ⊗_K L`.
- `finiteTensorMap v : E_v →ₐ[K_v] ∏_{w | v} L_w` is the canonical map `x ⊗ y ↦ (x y)_w`; it is
  bijective (`(completedTensorComparison K L).1 v`, module
  `Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof`). Its `w`-component is
  `Pi.evalRingHom _ w` composed with it.
- The instances on `E_v` and `GL_{r+1}(E_v)` (local field structure on `K_v`, module topology on
  `E_v`, Hausdorff, locally compact and totally disconnected `GL_{r+1}(E_v)`, Borel σ-algebra),
  the Haar measure `μv`, `σv := Algebra.TensorProduct.congr AlgEquiv.refl σ` (that is, `id ⊗ σ`),
  `Θ := adelicAut K (unitGaloisAut K L GLᵣ₊₁ σ)`, `hΘ`, `hΘμ` and the twisting operator `IΘ` are
  exactly as in `WeilGeneralLinearCuspidalLocalTwistedTraceStatement`.

Local representations.

- `ρv := tensorPullbackRepresentation (r + 1) h π`, with index type `FinitePlacesAbove L v`,
  `h w` the `w`-component of `finiteTensorMap v` and `π w = (D.localComponent w.1).representation`.
  So `y ∈ GL_{r+1}(E_v)` acts on `⨂_{w | v} (D.localComponent w.1).Space` by
  `⨂_w (right translation at w by the w-component of y)`. For a single place `w` above `v` the
  factor `π w` composed with `h w` is the representation `PiV` of
  `WeilGeneralLinearCuspidalLocalTwistedTraceStatement`.
- `Character.distribution μv ρv hP fv` is the trace of the finite-rank operator
  `ρv(fv) = ∫ fv(y) ρv(y) dμv(y)` for `fv ∈ SchwartzBruhat GL_{r+1}(E_v)` (module
  `Langlands.Representation.Character.Basic`).
- `SigmaIntertwiner σv (r + 1) ρv` (module `Langlands.BaseChange.TwistedCharacter`) is the type
  of isomorphisms `A` of `ρv` onto `ρv ∘ entrywiseAut σv (r + 1)`, so
  `A ∘ ρv(y) = ρv(σv(y)) ∘ A`, and `twistedDistribution μv ρv hP A fv` is the trace of
  `ρv(fv) ∘ A` (module `Langlands.BaseChange.TwistedCharacter.Basic`).

## Statement

For all data as above, assume:

1. `P` is a subspace of `S` with `[CompleteSpace P]` and `P ≠ ⊥`, invariant under every `πc a`,
   such that every closed subspace `Q ≤ P` invariant under every `πc a` is `⊥` or `P` (the
   hypotheses on `P` in `GroupSchemeCuspidalLocalTraceFactorizationStatement`);
2. `IsWeilFormClass K L r T i (Ψ f) (R.realization.toContinuous f)` for every `f : R.Space`, and
   the topological closure of the range of `Ψ` is `P`;
3. `v` is a finite place of `K` and `μv` is a Haar measure on `GL_{r+1}(E_v)`;
4. `D` is a spectral presentation of `R` such that `(D.localComponent w.1).IsIrreducible` and
   `(D.localComponent w.1).IsAdmissible` for every `w : FinitePlacesAbove L v`.

Then there is `hP : Langlands.IsAdmissible ρv` such that:

1. **Untwisted factor.** There is `C : (W(𝔸_K) → ℂ) → ℂ` with the following property. Let
   `fv ∈ SchwartzBruhat GL_{r+1}(E_v)` and let `fw : W(𝔸_K) → ℂ` satisfy
   `fw (g * ofPlace x) = fw g` for all `g` and all `x ∈ W(K_v)`. Put `f(g) = fv(gv g) · fw(g)` and
   suppose `hf : Integrable f ν`. If `P_P R_S(f) ι_P` is trace class, then
   `operatorTrace (P_P R_S(f) ι_P) = Character.distribution μv ρv hP fv · C(fw)`.
2. **Twisted factor.** For all `hΘ` and `hΘμ`, if `IΘ` maps `P` into `P`, there are
   `A : SigmaIntertwiner σv (r + 1) ρv` and `C : (W(𝔸_K) → ℂ) → ℂ` with the following property.
   For `fv`, `fw`, `f` and `hf` as in part 1, let `BP := P_P (P_S (R(f) ∘ IΘ) ι_S) ι_P`. If `BP`
   is trace class, then `operatorTrace BP = twistedDistribution μv ρv hP A fv · C(fw)`.

In each part `C` may depend on everything chosen before it, but not on `fv` or `fw`. The
statement asserts nothing about the trace class property; it computes the trace when the
property holds. The hypotheses `hΘ` and `hΘμ` are binders, as in
`GroupSchemeCuspidalLocalTraceFactorizationStatement`; this statement
neither proves nor uses that they hold for the Galois twist `Θ`. It does not compute the twisted
character of `ρv` in terms of the factors; at a place that splits completely in a cyclic
extension that is the local statement `SplitSigmaLiftStatement` (module
`Langlands.BaseChange.SplitSigmaLiftStatement`), on the Library's `splitTensorRep` and
`splitTensorShift`.

## Why the statement is true

1. **Local groups and admissibility.** `finiteTensorMap v` is a `K_v`-algebra isomorphism
   `E_v ≅ ∏_{w | v} L_w`. Both sides are finite-dimensional Hausdorff `K_v`-vector spaces with
   their unique such topology (module topology on `E_v`, product of completion topologies on the
   right), so it is a homeomorphism, and so is the induced isomorphism
   `GL_{r+1}(E_v) ≅ ∏_{w | v} GL_{r+1}(L_w)`; under it `ρv` is the external tensor product of the
   `π w`. Every open subgroup of the product contains a product `∏ K_w` of open compact
   subgroups, and, the `K_w` being compact and acting smoothly on complex spaces, the
   `∏ K_w`-fixed vectors of `⨂ V_w` are `⨂ V_w^{K_w}` (Flath, proof of Theorem 1, (iii), printed
   p. 180; Getz–Hahn, proof of Theorem 5.7.2, printed p. 152), which is finite-dimensional
   because each `π w` is admissible. Every vector of `⨂ V_w` is a finite sum of pure tensors, each fixed by
   such a product. So `ρv` is smooth and admissible.
2. **Compatibility of the identifications.** Under the comparison map `Φ` of
   `GeneralLinearWeilAdelicTwistStatement`, the
   projection `W(𝔸_K) → W(K_v)` followed by `localPointsEquiv` and `finiteTensorMap v` is the
   projection `GL_{r+1}(𝔸_L) → ∏_{w | v} GL_{r+1}(L_w)`, and `ofPlace` at `v` corresponds to the
   simultaneous insertion at all `w | v`: all maps are the canonical identifications
   `𝔸_K ⊗_K L = 𝔸_L` and `K_v ⊗_K L = ∏_{w|v} L_w`, applied to matrix entries. So, through `Ψ`
   (hypothesis 2), right translation by `∏_{w|v} GL_{r+1}(L_w)` on the forms of `R` corresponds
   to `πc ∘ ofPlace ∘ localPointsEquiv⁻¹` on `P`.
3. **Untwisted factor.** The argument for `GroupSchemeCuspidalLocalTraceFactorizationStatement`
   gives an irreducible admissible representation `ρ` of
   `W(K_v)` (the smooth vectors of the `W(K_v)`-factor `π_v` of `P ≅ π_v ⊗̂ π^v`) and `C` with
   `operatorTrace (P_P R_S(f) ι_P) = tr ρ(fv ∘ localPointsEquiv) · C(fw)`, after transporting
   `μv` to a Haar measure on `W(K_v)` (the scaling goes into `C`); here `P ≅ π_v ⊗̂ π^v` and `ρ`
   is the representation on the smooth vectors of `π_v`. The spectral presentation `D` identifies
   its finite slice, a nonzero subspace of the forms of `R` (`localComponent_le_full`), with a
   restricted tensor product of local factors over the finite places of `L` (`D.presentation`);
   `D.localComponent q` is the slice at `q` with a fixed nonzero tail at the other places, and is
   isomorphic to the factor at `q` (`FiniteTensorPresentation.localComponentEquiv`, module
   `Langlands.Automorphic.PresentedLocalComponent`). Fixing instead a nonzero pure tail away from
   the finitely many places above `v` gives a nonzero subspace of the forms of `R`, stable under
   `∏_{w|v} GL_{r+1}(L_w)` and isomorphic to `⨂_{w|v} D.localComponent w.1`, hence to `ρv`
   read on `W(K_v)` by step 1. That tensor product is irreducible (Flath, Theorem 1, (1.1),
   printed p. 179, applied to the finitely many factors; Getz–Hahn, Theorem 5.7.2 (i), printed
   p. 152). Through `Ψ` (hypothesis 2) and step 2 this subspace maps injectively and
   equivariantly into `P` (continuous functions that agree almost everywhere for a Haar measure
   agree). Composing with `id ⊗ λ : π_v ⊗̂ π^v → π_v` for a suitable continuous linear
   functional `λ` on `π^v` gives a nonzero equivariant map from `ρv` to the smooth vectors of
   `π_v`; both are irreducible, so it is an isomorphism. This is the argument of step 3 of the
   Markdown of `GeneralLinearCuspidalLocalComponentTraceStatement`, for the product group. Isomorphic admissible representations have the
   same distribution character.
4. **Twisted factor.** By `localPointsEquiv_atPlace_adelicAut`, the local action of `Θ` at `v`
   is `θ_v = entrywiseAut σv (r + 1)` in the coordinates `gv`, and
   `Θ (ofPlace x) = ofPlace (θ_v x)`. Through `finiteTensorMap v`, `σv = id ⊗ σ` acts on
   `∏_{w | v} L_w` as follows. For a place `w` above `v` with prime ideal `𝔓_w`, let `σ⁻¹w` be
   the place above `v` with prime ideal `σ⁻¹(𝔓_w)`, so that `|y|_{σ⁻¹w} = |σ(y)|_w` for
   `y ∈ L`. Then `σ` extends by continuity to an isomorphism of `K_v`-algebras
   `σ̂_w : L_{σ⁻¹w} → L_w`, and the `w`-component of `σv(z)` is `σ̂_w(z_{σ⁻¹w})`. Both sides are
   continuous and `K_v`-linear in `z`, and they agree on `1 ⊗ y`, where both give the image of
   `σ(y)` in `L_w`. On `GL_{r+1}(E_v) ≅ ∏_{w | v} GL_{r+1}(L_w)`, `θ_v` applies these maps to
   the matrix entries. So `σv` moves the factor at `σ⁻¹w` to the factor at `w` and also acts on
   its entries. If `σ^m` fixes `w`, then the `m`-th iterate of `σv`, restricted to the factor at
   `w`, is the continuous extension of `σ^m` to `L_w`. This is an automorphism of `L_w` over
   `K_v`, and it need not be the identity. This is the formula of Arthur–Clozel, Chapter 1, §5,
   printed p. 48, written in these coordinates. Let `L/K` be cyclic of degree `ℓ` with generator
   `σ`, let `m` be the number of places above `v`, and fix one of them, `w_1`. Put
   `w_i = σ^{-(i-1)} w_1` for `1 ≤ i ≤ m`, so that `σ⁻¹w_i = w_{i+1}` for `i < m` and
   `σ⁻¹w_m = w_1`. Identify `L_{w_i}` with `E_1 = L_{w_1}` by `σ̂_{w_1} ∘ ⋯ ∘ σ̂_{w_{i-1}}`
   (the identity for `i = 1`). Then
   `σv` becomes `(x_1, …, x_m) ↦ (x_2, …, x_m, τ(x_1))`, where `τ` is the extension of `σ^m` to
   `E_1`, a generator of `Gal(E_1/K_v)`. Only when `v` splits completely (`m = ℓ`,
   `L_w = K_v` canonically, `τ = id`) is this the plain cyclic shift of the factors. That is
   the shift of the Library's `splitCyclicShift`. The argument for
   `GroupSchemeCuspidalLocalTraceFactorizationStatement` gives a bijective `A_v` on the space of
   `ρ` with `A_v ∘ ρ(y) = ρ(θ_v y) ∘ A_v` and `C` with
   `operatorTrace BP = tr (ρ(fv) ∘ A_v) · C(fw)`. Transporting `A_v` by an isomorphism
   `ρ ≅ ρv` from step 3 gives `A : SigmaIntertwiner σv (r + 1) ρv` with the same twisted trace.
   The direction `σv` (not `σv⁻¹`) comes from `IΘ R(y) = R(Θ y) IΘ` and the convention
   `A ∘ ρv(y) = ρv(σv(y)) ∘ A` of `SigmaIntertwiner`.

## Provenance

This is derived content, formulated for this project:
`GroupSchemeCuspidalLocalTraceFactorizationStatement` for the group `W`, with the local
factor at `v` identified through `W(K_v) = ∏_{w|v} GL_{r+1}(L_w)` and the tensor product
factorization of cuspidal representations of `GL_{r+1}(𝔸_L)`.

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024): §13.4, printed p. 350
  (`Res_{E/F} GL_n(𝔸_F) := GL_n(𝔸_E)`); §1.4, printed p. 12 (the Weil restriction of scalars
  `Res_{k'/k} X'(R) := X'(R ⊗_k k')`); Flath's theorem 5.7.1, printed p. 152, and (11.14),
  printed p. 300 (factorization of cuspidal representations); (18.33), printed p. 487 (pullback
  convention for the twist), as cited in the Markdown of
  `GroupSchemeCuspidalLocalTraceFactorizationStatement`.
- D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math. 33,
  part 1 (1979), Theorems 1 and 3 (printed pp. 179–181): irreducible admissible representations
  of a product of groups are tensor products.
- Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace formula*
  (1989), Chapter 1. §5, printed p. 48: `E = k' ⊗ F ≅ E_1 × ⋯ × E_1` (`m` factors, `E_1/F`
  cyclic). For a generator `σ` of `Gal(k'/k)`, `τ = σ^m` generates `Gal(E_1/F)`, and `σ` acts
  on `E`, and by the same formula on `G(E) ≅ G(E_1) × ⋯ × G(E_1)`, by a cyclic permutation of
  the factors with `τ` applied to the wrap-around coordinate:
  `σ(x_1, x_2, …, x_m) = (x_2, …, x_m, x_1^τ)`. The book prints the right-hand side as
  `(x_2, x_3, … x_{m-1}, x_1^τ)`. The last equation of (5.1), `x_m^{-1} δ_m x_1^τ = δ_m`, has
  `τ` on the wrap-around coordinate. The proof
  of Theorem 6.2, printed p. 56, writes the Whittaker functional `λ` and the operator `I_σ` as
  tensor products `λ = ⊗_v λ_v`, `I_σ = ⊗_v I_{σ,v}` over the places `v` of `k`, with
  `I_{σ,v} λ_v = λ_v`. Printed p. 57 gives the example of a local tensor power at a split place:
  `Π_{v₁} ≅ (π_{v₁})^{⊗ℓ}`. Step 4 above relates the §5 formula to the coordinates
  `∏_{w|v} L_w` used here. The identification `K_v ⊗_K L ≅ ∏_{w|v} L_w` is the Library's
  `finiteTensorMap` with `completedTensorComparison`.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non
  nulle* (2011), Proposition of II.6.5 (printed pp. 121–122): the global operator `I_σ(Π)` is the
  tensor product of the normalized local operators `I_σ(Π_v)`, indexed by the places `v` of the
  base field, each acting on the local component `Π_v` of `Π`, a representation of `G(E_v)` with
  `E_v = E ⊗_F F_v` (a product over the places of `E` above `v`).
- The Library statements `GroupSchemeCuspidalLocalTraceFactorizationStatement` and
  `GeneralLinearCuspidalLocalComponentTraceStatement`, whose form is followed, and the
  Library's `Langlands.BaseChange.splitTensorRep`, of which `tensorPullbackRepresentation`
  generalizes the definition.

Differences from the sources, all of which keep the content: one place `v` is split off, so the
remaining factor is an arbitrary functional `C`; the local components are the Library's
`CuspidalSpectralPresentation.localComponent` at the places above `v`, and their tensor product
is read on `GL_{r+1}(K_v ⊗_K L)`; irreducibility and admissibility of those local components are
hypotheses, as the Library states them on local components; the intertwiner is not normalized;
the trace class property is a hypothesis.

## Use

The statement serves the comparison of the twisted trace formula for `W` with the
trace formula for `GL_{r+1}` over `K` at places `v` of `K` that split in `L`, where
`W(K_v) = ∏_{w|v} GL_{r+1}(L_w)`, in local cyclic base change for `GL_n`. For a cyclic
extension of prime degree `l` and `v` split, that comparison relates the local factor `ρv` of a
`σ`-stable cuspidal summand to the Library's
`splitTensorRep` of one local component, and `SplitSigmaLiftStatement` relates the
twisted character of the latter to the character of that component; neither step is part of
this statement. This is the input for the description of cuspidal cyclic base change at split
places. At places with one place above them
`WeilGeneralLinearCuspidalLocalTwistedTraceStatement` gives the same factor without the tensor
product.
