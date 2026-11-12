# Statement: continuity of the action of `GL_{d+1}(F)` on Drinfeld's upper half space

Author: Worker 21.

This module states, without proof, that the action `omegaAction F K d` of
`GL_{d+1}(F)` on Drinfeld's upper half space `Ω` (module
`DrinfeldGroupAction`) is continuous in Berkovich's sense
(`IsContinuousAction`, module `ContinuousAnalyticAction`). Since the
underlying space of `omegaAction F K d` is already known to be Hausdorff, a
proof of this statement would show that `omegaAction F K d` satisfies
`gSpaceProperty`, that is, `Ω` is a `GSpace`. That consequence is not
formalized here.

## The statement

`OmegaActionContinuityStatement : Prop` (namespace
`Langlands.Analytic.DrinfeldUpperHalfSpace`). Let `F` be a nontrivially normed
field with compact closed balls (`ProperSpace F`), let `K` be a nontrivially
normed, ultrametric, complete field that is a normed `F`-algebra, and let
`d ≥ 1` (`NeZero d`). Then the homomorphism
`(omegaAction F K d).ρAut : GL_{d+1}(F) →* Aut(Ω)` satisfies
`IsContinuousAction`. The group `GL_{d+1}(F)` carries Mathlib's topology on the
units of the matrix algebra `Matrix (Fin (d + 1)) (Fin (d + 1)) F` (the topology
induced by `γ ↦ (γ, γ⁻¹)` from the product topology).

The statement quantifies over `F`, `K` and `d` in the universes `v` (for `F`)
and `u` (for `K`).

Unfolded, it says: for every test triple `(U, f, t)` of the saturated
presentation of `Ω` (an affinoid domain `U` inside some member `V_N` of the
exhaustion, a function `f` on `U` and `t > 0`), the set of `γ` with
`d(ρ(γ), 1) < (U, f, t)` is a neighbourhood of `1`. In particular `γ(U) = U`
and `|γ*f − f| ≤ t` on `U` for all `γ` close to `1`.

## Original sources and derived provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.1,
printed p.2:

- "We say that the action of a topological group G on an analytic space is
  continuous if the induced homomorphism G → G(X) is continuous."
- Example 1.1.1(ii): "It is easy to verify that the homomorphism
  G(X/k°) → G_k(X_η) is continuous. In particular, if a topological group G
  acts continuously on X, then it acts continuously on X_η." Here `X` is a
  formal scheme locally finitely presented over `k°`, or a special formal
  scheme if the valuation of `k` is discrete.
- "An analytic space X endowed with a continuous action of a topological group
  G will be called a G-space."

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`, §2,
printed p.109 / PDF p.3: "THEOREM. We may represent the functor G by the formal
scheme Ω̂^d ⊗̂ Ô^nr. The action of GL(d, K) × D* on the functor G corresponds to
the natural action of PGL(d, K) on Ω̂^d …" and "Here Ω̂^d is the formal scheme
over O defined by P. Deligne." The opening paragraph (printed p.107) says that
`Ω^d` "arises from some formal scheme Ω̂^d over the ring of integers of K".

The statement is derived from these sources. Drinfeld's `Ω^d` is the generic
fibre of Deligne's formal scheme, on which `PGL(d, K)` acts, and by Berkovich's
Example 1.1.1(ii) a continuous action on the formal scheme gives a continuous
action on the generic fibre. The Lean statement is about the Library's
construction instead, which uses the exhaustion atlas and the explicit
pullbacks. Its identification with the generic fibre of Deligne's formal
scheme is not formalized.

A direct proof is expected to run as follows; none of it is formalized here.

1. For `γ` congruent to `1` modulo a high power of the uniformizer, the closed
   polydiscs `|Tᵢ| ≤ ‖ϖ‖⁻ᴺ` are mapped onto themselves. Since `|ℓ_{γ_0}| = 1`
   there, the map moves each coordinate by a small amount (ultrametric
   inequality).
2. Rational domains `{|g_i| ≤ |g_0|}` of such a polydisc, with `g_0` bounded
   below on the domain, are then preserved, and pullbacks of functions on them
   move by a small amount.
3. General affinoid domains reduce to rational ones by the Gerritzen–Grauert
   theorem.

## Scope

This is a `lean.statement`: nothing is proved here. Its proof is a separate
obligation.
