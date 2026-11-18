# Lifts on a single chart are derivations; flat base change on a chart

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. The setting is
square-zero lifting data `(f, I, x₀, s)` over `C`, a base lift `e`, and a
chart `ch` (affine opens `V ⊆ S`, `U ⊆ f⁻¹V`, and an element `g`). We
assume `hg : IsUnit (algebraMap C C ch.g)`, so the chart covers all of
`Spec C`.

## Auxiliary facts

- `restrC_self`: restricting a global lift along `C → C` gives the same
  lift.
- `isGlobalLift_of_isLift_self`: a lift on `C` itself, in the sense of
  `IsLift`, is a global lift.
- `Chart.rep_θ_apply`, `Chart.grep_sub_mem`, and `Chart.algebraMap_base` are
  identities for chart representatives on `C`.

## Algebra structures

The derivation statements take algebra structures as instance arguments,
together with two equations:
- `Γ(S, V) → Γ(X, U)` is the chart map `ch.θ` (hypothesis `hθ`);
- `Γ(X, U) → C` is the chart representative of `e` (hypothesis `hφ`).

## Lifts and derivations

- `Chart.der y` is the `Γ(S, V)`-derivation `Γ(X, U) → I C` given by the
  difference of chart representatives of `y` and `e`. `Chart.derLin` is
  the underlying linear map. Leibniz holds because `(I C)² = 0`.
- `Chart.homOfDer d` is the ring map `b ↦ e(b) + d(b)`.
  `Chart.liftOfDer d` is the corresponding global lift, obtained with
  `Chart.isLift_of_hom`. The supporting identities are `homOfDer_θ`,
  `homOfDer_red`, and `grep_liftOfDer`.
- `Chart.derEquiv` gives
  `LiftModule hI e ≃ₗ[C] Derivation Γ(S, V) Γ(X, U) (redIdeal I C)`.
  Its value formula is `derEquiv_apply_val`. Linearity comes from
  `LiftModule.grep_lin`.

## Flat base change on a chart

- `Chart.grep_bc_res`: the chart representative of `y|_T` for the
  base-changed chart `ch.bc T` is `algebraMap C T` applied to the chart
  representative of `y` on `C`.
- `Chart.isBaseChange_resLin` assumes `[Smooth f]`, `hg`, and a flat
  `C`-algebra `T`. It states `IsBaseChange T (LiftModule.resLin T hI e)`.

  Proof. The chart map `θ` is smooth by `Smooth.smooth_appLE`, so
  `Γ(X, U)` is formally smooth and of finite presentation over `Γ(S, V)`.
  Apply `Chart.derEquiv` on `C` and on `T`. These are compatible with
  restriction by `grep_bc_res`. This reduces the claim to
  `isBaseChange_derMap`.

Provenance: internal to Task 6989 (Worker 496). This is the local
identification of lifts with derivations, as in the Stacks proof of
Lemma 37.11.7 (Tag 02H6). Here it is phrased with chart ring maps instead
of the sheaf `Hom(a*Ω_{X/S}, C_{T/T'})`.
