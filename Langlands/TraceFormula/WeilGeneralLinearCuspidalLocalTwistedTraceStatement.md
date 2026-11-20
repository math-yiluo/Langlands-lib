# The local twisted trace factor of a cuspidal summand of `Res_{L/K} GL_n` (statement)

Module `Langlands.TraceFormula.WeilGeneralLinearCuspidalLocalTwistedTraceStatement`, namespace
`Langlands.TraceFormula`. It contains one proposition definition and no proof:

- `Langlands.TraceFormula.WeilGeneralLinearCuspidalLocalTwistedTraceStatement.{u, uV}`.

Let `L/K` be a finite extension of number fields, `σ ∈ Aut(L/K)` and `W = Res_{L/K} GL_{r+1}`.
Task 7701 (`Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement`) asserts
that the traces on an irreducible cuspidal summand `P` of `L²([W])` split off, at a finite place
`v` of `K`, the character of *some* irreducible admissible representation of `W(K_v)`, and, for a
twist `Θ` preserving `P`, the twisted character of that representation for *some* intertwiner.
This module identifies the local factor at a finite place `v` of `K` with exactly one place `w`
of `L` above it: it is the Library's local component at `w` of a cuspidal operator realization
`R` over `L` attached to `P` (as in `WeilGeneralLinearCuspidalSummandRealizationStatement`),
viewed as a representation of `GL_{r+1}(K_v ⊗_K L)`. For the Galois twist `Θ` attached to `σ`,
the intertwiner is a `SigmaIntertwiner` for `σ_v = id ⊗ σ`, the object of the Library's local
base change statements (`Langlands.BaseChange.TwistedCharacter`). It is the analogue for `W` of
`GeneralLinearCuspidalLocalComponentTraceStatement` (Task 7819; staged candidate
`7dc598a7-504c-4632-95ec-9b5eea52eb9a`, not in the Library at the base commit and not imported
here), which treats `GL_{r+1}` over one field and only the untwisted part. At an arbitrary finite
place of `K` the local factor is the tensor product of the local components above it
(`WeilGeneralLinearCuspidalLocalTensorTraceStatement`, in the same task).

The module declares the `local instance`s `IsAffine` and `Smooth` for the general linear group
scheme (from `GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement`) and five `local instance`s of `AddCommGroup` on the
Library's form spaces `Langlands.Automorphic.RationalInvariantFunctions`,
`ContinuousRationalFunctions`, `FiniteSmoothRationalFunctions`, `AutomorphicForms` and on the
carrier of a `LocalRealization`, as Task 7819 and the Library's own modules do (for example
`Langlands.Automorphic.PresentedLocalCategory`). They are not exported. The definition carries
`set_option maxHeartbeats 1000000`, because elaborating the whole statement exceeds the default
limit (each of its parts elaborates within the default limit when checked separately).

## Setting and notation from the Library

Global data. As in `WeilGeneralLinearCuspidalSummandRealizationStatement`: number fields
`K L : Type u` with `[Algebra K L]`, `[FiniteDimensional K L]` and compact adele quotient of `L`;
`σ : L ≃ₐ[K] L`; `r : ℕ`; `W = weilGroup K L GLᵣ₊₁` (written `Wᵣ` in the Lean file); `hPD`; the
binder `hG : IsConnectedReductive W`; `T`, `i`, `hi`, `I`, `e`, `hc` and right invariance of Haar
measure on the norm-one subgroup; `ν` a Haar measure on `W(𝔸_K)`. Then

- `S := fullAEL2CuspidalSubmodule K W hPD hG T i hi I e hc` is the closed cuspidal subspace of
  `L²(Q)`, `Q = PositiveRationalQuotient K W T i` with quotient Haar measure
  `μQ = positiveRationalQuotientHaarMeasure K W T i`, and `πc a` is right translation by `a` on
  `S`;
- for `hf : Integrable f ν`, `fullAEL2CuspidalIntegratedAction K W hPD hG T i hi I e hc ν f hf`
  (written `R_S(f)`) is `∫ f(a) πc(a) dν(a)` on `S`, and
  `haarQuotientL2IntegratedAction K W T i hi I e hc ν f hf` (written `R(f)`) is the same integral
  on all of `L²(Q)`;
- `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace. For a
  complete subspace `P`, `P_P X ι_P` denotes `P.orthogonalProjectionOnto ∘L X ∘L P.subtypeL`.

Realizations. `R : CuspidalOperatorRealization L r`, `Ψ : R.Space →ₗ[ℂ] S` and the predicate
`IsWeilFormClass` (through the comparison map `Φ : W(𝔸_K) → GL_{r+1}(𝔸_L)` of Task 7670) are as
in `WeilGeneralLinearCuspidalSummandRealizationStatement`.
`D : Langlands.Automorphic.CuspidalSpectralPresentation.{u, uV} R` is a spectral presentation of
`R` (module `Langlands.Automorphic.CuspidalSpectralPresentation`). For a finite place `w` of `L`
its local component `D.localComponent w : LocalRealization L (r + 1) w` is a nonzero subspace of
automorphic forms in the image of `R`, stable under right translation by
`GL_{r+1}(L_w) = FiniteLocalGL L (r + 1) w` (`localComponent_le_full`); its `representation` is
that right translation; `IsIrreducible` and `IsAdmissible` are the Library's irreducibility and
admissibility for the completion topology. Among presentations whose local component at `w` is
irreducible, its isomorphism class does not depend on the presentation
(`localComponent_isoClass_eq`, module `Langlands.Automorphic.AssociatedPresentationComparison`).

Places and local groups.

- `v : Langlands.Global.FinitePlace K` is a finite place and `.inr v` the corresponding element
  of `Place K`. `w : FinitePlacesAbove L v` is a finite place of `L` above `v`, and the hypothesis
  `∀ w', w' = w` says that it is the only one.
- `atPlace K W (.inr v)` is the projection `g ↦ g_v` of `W(𝔸_K)` to `W(K_v)`, and
  `ofPlace K W (.inr v)` the insertion of a local point at `v`.
- `localPointsEquiv K L (r + 1) (.inr v) : W(K_v) ≃* GL_{r+1}(K_v ⊗_K L)` (module
  `Langlands.TraceFormula.GeneralLinearBaseChangeLocal`) is the Library's identification of the
  local points of `W` with `GL_{r+1}` of `E_v = K_v ⊗_K L` (`LocalBaseChangeAlgebra`, written
  `GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)` in the statement). The statement writes
  `gv g := localPointsEquiv K L (r + 1) (.inr v) (atPlace K W (.inr v) g)`.
- `finiteTensorMap v : K_v ⊗_K L →ₐ[K_v] ∏_{q | v} L_q` (module
  `Langlands.Global.AdelicFunctoriality.Norm`) is the canonical map `x ⊗ y ↦ (x y)_q`. It is
  bijective (`(completedTensorComparison K L).1 v`, module
  `Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof`). Followed by the
  evaluation at `w` it is a ring isomorphism `E_v ≅ L_w` when `w` is the only place above `v`.
- Instances on `E_v` and `GL_{r+1}(E_v)`, all local to the statement: the valuative relation and
  nonarchimedean local field structure of `K_v` from `CompletionPadic.topologicalData v`; the
  module topology of `E_v` over `K_v` (`IsModuleTopology`, topological ring); Hausdorff, locally
  compact and totally disconnected `GL_{r+1}(E_v)` from the Library lemmas
  `generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite` and
  `generalLinear_totallyDisconnectedSpace_of_finite`; and the Borel σ-algebra. This is the
  instance block of the draft `CuspidalCyclicBaseChangeLiftStatement` (Task 7846, not in the
  Library) with the Borel σ-algebra added. `μv` is a Haar measure on `GL_{r+1}(E_v)`.
- `σv := Algebra.TensorProduct.congr AlgEquiv.refl σ : E_v ≃ₐ[K_v] E_v` is `id ⊗ σ`; it is the
  Library's `localGalois K L σ (.inr v)`.
- `Θ := adelicAut K (unitGaloisAut K L GLᵣ₊₁ σ)` is the automorphism of `W(𝔸_K)` induced by the
  algebraic automorphism of `W` attached to `σ`. The Library lemma
  `localPointsEquiv_atPlace_adelicAut` gives `gv (Θ g) = entrywiseAut σv (r + 1) (gv g)`.
- For `hΘ` (`Θ` preserves `positiveRationalSubgroup K W T i`) and `hΘμ` (the induced map of `Q`
  preserves `μQ`), `IΘ := twistOperator (positiveRationalSubgroup K W T i) Θ hΘ μQ hΘμ` is the
  twisting operator on `L²(Q)`, `IΘ φ = φ ∘ Θ̄⁻¹`, so that `IΘ R(y) = R(Θ y) IΘ`.

Local representations.

- `PiV` is `(D.localComponent w).representation` composed with
  `GL_{r+1}(E_v) → GL_{r+1}(L_w)` induced by the evaluation at `w` composed with
  `finiteTensorMap v`. So `y ∈ GL_{r+1}(E_v)` acts on a form by right translation at `w` by the
  image of `y`. It is the representation `tensorPlaceAboveRepresentation` of the draft of Task 7846, written
  inline so that this statement does not depend on Task 7846.
- `SchwartzBruhat GL_{r+1}(E_v)` is the space of locally constant compactly supported functions,
  and `Character.distribution μv PiV hP fv` is the trace of the finite-rank operator
  `PiV(fv) = ∫ fv(y) PiV(y) dμv(y)` (module `Langlands.Representation.Character.Basic`).
- `SigmaIntertwiner σv (r + 1) PiV` (module `Langlands.BaseChange.TwistedCharacter`) is the type
  of isomorphisms `A` of `PiV` onto `PiV ∘ entrywiseAut σv (r + 1)`, so
  `A ∘ PiV(y) = PiV(σv(y)) ∘ A`, and `twistedDistribution μv PiV hP A fv` is the trace of
  `PiV(fv) ∘ A` (module `Langlands.BaseChange.TwistedCharacter.Basic`).

## Statement

For all data as above, assume:

1. `P` is a subspace of `S` with `[CompleteSpace P]` and `P ≠ ⊥`, invariant under every `πc a`,
   such that every closed subspace `Q ≤ P` invariant under every `πc a` is `⊥` or `P` (the
   hypotheses on `P` in Task 7701);
2. `IsWeilFormClass K L r T i (Ψ f) (R.realization.toContinuous f)` for every `f : R.Space`, and
   the topological closure of the range of `Ψ` is `P` (the output of
   `WeilGeneralLinearCuspidalSummandRealizationStatement`);
3. `v` is a finite place of `K`, `w` is the only place of `L` above `v`, and `μv` is a Haar
   measure on `GL_{r+1}(E_v)`;
4. `D` is a spectral presentation of `R` with `(D.localComponent w).IsIrreducible` and
   `(D.localComponent w).IsAdmissible`.

Then there is `hP : Langlands.IsAdmissible PiV` such that:

1. **Untwisted factor.** There is `C : (W(𝔸_K) → ℂ) → ℂ` with the following property. Let
   `fv ∈ SchwartzBruhat GL_{r+1}(E_v)` and let `fw : W(𝔸_K) → ℂ` satisfy
   `fw (g * ofPlace x) = fw g` for all `g` and all `x ∈ W(K_v)`. Put `f(g) = fv(gv g) · fw(g)` and
   suppose `hf : Integrable f ν`. If `P_P R_S(f) ι_P` is trace class, then
   `operatorTrace (P_P R_S(f) ι_P) = Character.distribution μv PiV hP fv · C(fw)`.
2. **Twisted factor.** For all `hΘ` and `hΘμ` as above, if `IΘ` maps `P` into `P`, there are
   `A : SigmaIntertwiner σv (r + 1) PiV` and `C : (W(𝔸_K) → ℂ) → ℂ` with the following property.
   For `fv`, `fw`, `f` and `hf` as in part 1, let `BP := P_P (P_S (R(f) ∘ IΘ) ι_S) ι_P`. If `BP`
   is trace class, then `operatorTrace BP = twistedDistribution μv PiV hP A fv · C(fw)`.

In each part `C` may depend on everything chosen before it, but not on `fv` or `fw`. The
statement asserts nothing about the trace class property; it computes the trace when the
property holds. The hypotheses `hΘ` and `hΘμ` are binders, as in Task 7701; this statement
neither proves nor uses that they hold for the Galois twist `Θ`.

## Why the statement is true

1. **Local groups.** With `w` the only place above `v`, the evaluation at `w` composed with
   `finiteTensorMap v` is a `K_v`-algebra isomorphism `E_v ≅ L_w`. Both sides carry their unique
   Hausdorff `K_v`-vector space topology (module topology on `E_v`, completion topology on
   `L_w`), so it is a homeomorphism, and so is the induced isomorphism
   `GL_{r+1}(E_v) ≅ GL_{r+1}(L_w)`. Hence `PiV` is admissible because `D.localComponent w` is:
   open compact subgroups and their fixed vectors correspond.
2. **Compatibility of the identifications.** Under `Φ`, the projection `W(𝔸_K) → W(K_v)`
   followed by `localPointsEquiv` and `GL_{r+1}(E_v) ≅ GL_{r+1}(L_w)` is the projection
   `GL_{r+1}(𝔸_L) → GL_{r+1}(L_w)`: all maps are the canonical identifications
   `𝔸_K ⊗_K L = 𝔸_L` and `K_v ⊗_K L = ∏_{q|v} L_q`, applied to matrix entries. Likewise `ofPlace`
   at `v` corresponds to the insertion at `w`. So, through `Ψ` (hypothesis 2), right translation
   at `w` on the forms of `R` corresponds to `πc ∘ ofPlace ∘ localPointsEquiv⁻¹` on `P`.
3. **Untwisted factor.** The argument for Task 7701 (`W(𝔸_K) = W(K_v) × W(𝔸_K^v)` with
   `W(K_v)` of type I) writes the irreducible unitary representation on `P` as a Hilbert tensor
   product `π_v ⊗̂ π^v` and gives `C` with
   `operatorTrace (P_P R_S(f) ι_P) = tr ρ(fv ∘ localPointsEquiv) · C(fw)`, where `ρ` is the
   irreducible admissible representation of `W(K_v)` on the smooth vectors of `π_v`, after
   transporting `μv` to a Haar measure on `W(K_v)` (the scaling goes into `C`). By
   `localComponent_le_full`, every vector of `D.localComponent w` is the function of a unique
   vector of `R`, and `Ψ` (hypothesis 2) sends it to its `L²` class in `P`; this gives an
   injective linear map `j` from `D.localComponent w` to `P` (continuous functions that agree
   almost everywhere for a Haar measure agree), which by step 2 intertwines `PiV(y)` with
   `πc (ofPlace (localPointsEquiv⁻¹ y))`. For a nonzero `x` and a continuous linear functional
   `λ` on `π^v` with `(id ⊗ λ)(j x) ≠ 0`, the map `(id ⊗ λ) ∘ j` is a nonzero equivariant map
   from `PiV` (read on `W(K_v)`) to the smooth vectors of `π_v`; both are irreducible, so it is an
   isomorphism. This is the argument of step 3 of the Markdown of Task 7819, the analytic form
   of Flath's remark (proof of Theorem 1, printed p. 180) that the restriction of `W_1 ⊗ W_2` to
   `G_1` is `W_1`-isotypic. Isomorphic admissible representations have the same distribution
   character.
4. **Twisted factor.** By `localPointsEquiv_atPlace_adelicAut`, the local action of `Θ` at `v`
   is `θ_v = entrywiseAut σv (r + 1)` in the coordinates `gv`, and `Θ (ofPlace x) = ofPlace (θ_v x)`.
   Task 7701 gives a bijective `A_v` on the space of `ρ` with `A_v ∘ ρ(y) = ρ(θ_v y) ∘ A_v` and
   `C` with `operatorTrace BP = tr (ρ(fv) ∘ A_v) · C(fw)`. Transporting `A_v` by an isomorphism
   `ρ ≅ PiV` from step 3 gives `A : SigmaIntertwiner σv (r + 1) PiV` with the same twisted
   trace. The direction `σv` (not `σv⁻¹`) comes from `IΘ R(y) = R(Θ y) IΘ` and the convention
   `A ∘ PiV(y) = PiV(σv(y)) ∘ A` of `SigmaIntertwiner`.

## Provenance

This is derived content, formulated for this project: Task 7701 for the group `W`, with the local
factor identified as in Task 7819 through the identification of `W` with `GL_{r+1}` over `L`.

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non
  nulle* (2011), Proposition of II.6.5 (printed pp. 121–122): for a cuspidal automorphic
  representation `Π` of `G(𝔸_E)`, `G = GL_n`, in `L²_0`, the global operator `I_σ(Π)` is the
  tensor product of the normalized local operators: for every place `v` of the base field `F`
  one can take for `A_{Π_v}` the normalized operator `I_σ(Π_v)` on the local component `Π_v` of
  `Π`, a representation of `G(E_v)` with `E_v = E ⊗_F F_v` (the proof treats `σ`-stable `Π`);
  this is the twisted factorization used in their trace comparison II.6.6.
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024): §13.4, printed p. 350
  (`Res_{E/F} GL_n(𝔸_F) := GL_n(𝔸_E)`); Theorem 9.7.3, printed p. 265; Flath's theorem 5.7.1,
  printed p. 152, and (11.14), printed p. 300 (factorization of cuspidal representations);
  (18.33), printed p. 487 (pullback convention for the twist), as cited in Task 7701.
- D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math. 33,
  part 1 (1979), Theorems 1 and 3 (printed pp. 179–181), as cited in Task 7819.
- The Library statement `GroupSchemeCuspidalLocalTraceFactorizationStatement` (Task 7701) and the
  statement `GeneralLinearCuspidalLocalComponentTraceStatement` of Task 7819 (staged, not yet in
  the Library), whose form is followed.

Differences from the sources, all of which keep the content: one place `v` is split off, so the
remaining factor is an arbitrary functional `C`; the local component is the Library's
`CuspidalSpectralPresentation.localComponent` at the unique place above `v`, read on
`GL_{r+1}(K_v ⊗_K L)`; irreducibility and admissibility of that local component are hypotheses,
as the Library states them on local components; the intertwiner is not normalized (any nonzero
rescaling of `A` is absorbed into `C`); the trace class property is a hypothesis.

## Use

Task 7340 uses the statement in the comparison of the twisted trace formula for `W` with the
trace formula for `GL_{r+1}` over `K`, at places `v` of `K` with one place above them (in
particular at places that do not split in a cyclic extension of prime degree): the twisted
traces of cuspidal summands of `L²([W])` become twisted characters of the Library's local
components, the objects on which the local base change statements (`IsSigmaLift`,
`IsSigmaStable`, supercuspidality) are stated. At places of `K` with several places above them
(for example places that split in `L`) the local group is a product of several groups
`GL_{r+1}(L_q)`; that case is `WeilGeneralLinearCuspidalLocalTensorTraceStatement` (in the same
task).
