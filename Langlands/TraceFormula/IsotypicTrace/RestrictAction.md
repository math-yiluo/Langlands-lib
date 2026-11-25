# Restriction of an isometric action to a closed invariant subspace

Module `Langlands.TraceFormula.IsotypicTrace.RestrictAction`. Internal to the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence.
It contains general Hilbert-space plumbing.

* `restrictAction π P hP : A →* (P →L[ℂ] P)`: the action on a complete subspace `P` invariant
  under `π`. Its values on `P` are those of `π` (`restrictAction_apply`), and it preserves
  inner products if `π` does (`restrictAction_inner`).
* `restrictAction_irreducible`: if `P` has no closed `π`-invariant subspaces of `E` other than
  `⊥` and `P`, then the restricted action has no closed invariant subspaces other than `⊥` and
  `⊤`. A closed invariant subspace `Q` of `P` maps to the subspace `Q.map P.subtype` of `E`,
  which is closed (`P` is closed, being complete) and invariant.
* `compression_integratedIsometricAction`: the compression `P_P ∘ R ∘ ι_P` of the integrated
  isometric action `R` of an integrable function is the integrated restricted action. The
  integrand stays in `P`, and the subtype inclusion commutes with Bochner integration.
* `nestedRestrict S P J = P_P ∘ P_S ∘ J ∘ ι_S ∘ ι_P` for subspaces `P ≤ S ≤ L` and `J` on `L`.
  If `J` maps `P` into `P`, this operator agrees with `J` on `P` (`nestedRestrict_val`).
  `nested_compression_comp`: for `RS` on `S` agreeing with `RL` on `L`, the compression of
  `RL ∘ J` to `P` is `(P_P ∘ RS ∘ ι_P) ∘ nestedRestrict S P J`. `nestedRestrict_covariant`:
  covariance `J ∘ πL a = πL (Θ a) ∘ J` passes to the induced operator on `P`.
