# Deviation from a unipotent constant term for families of functions

Let `j : U ⟶ G` be a closed immersion of a smooth connected unipotent group over a number field,
and let `g_U` be the normalized constant term `subgroupConstantTerm F j g`, the average of `g(u x)`
over `U(F) \ U(𝔸)` for the probability Haar measure. The module
`Langlands.Global.AdelicUnipotentFamilyOscillation` proves a version, for families indexed by an
arbitrary measure space, of the estimate of a function minus its constant term by its oscillation
along archimedean points of `U`.

`adelicUnipotentFamilyOscillation`: for a compact set `Yf` of finite adelic points and an open
subgroup `L` of `G(𝔸_f)`, there is a compact set `D` of archimedean points of `U` with the
following property. Let `(Ω, m)` be any measure space and `g o` (for `o ∈ Ω`) continuous functions
on `G(𝔸)`, jointly measurable in `(o, x)`, left invariant under `U(F)` and right invariant under
`L`. Then for every `x` with finite component in `Yf`,

`∫_Ω ‖g o x − (g o)_U(x)‖ dm ≤ sup_{v ∈ D} ∫_Ω ‖g o x − g o (v x)‖ dm`.

**Proof.** `adelicUnipotentArchimedeanRepresentatives` gives the compact set `D`: for every point
`u` of `U(𝔸)` there are `v ∈ D` and `q ∈ U(F)` such that `q u x = v x l` for some `l ∈ L`, whenever
the finite component of `x` lies in `Yf`. Hence `g o (u x) = g o (v x)` for all `o`. The constant term is
the integral of `g o (u x)` against the normalized Haar measure on a relatively compact fundamental
domain of `U(F)` in `U(𝔸)` (`LeftCosetSpace.relativelyCompactFundamentalDomain`). Hence
`‖g o x − (g o)_U(x)‖` is at most the average of `‖g o x − g o (u x)‖` over the fundamental domain,
and `lintegral_lintegral_le_mul_iSup` (module `Langlands.Analysis.FamilyLIntegral`) bounds its
integral over `Ω` by the supremum over `U(𝔸)`. The archimedean representatives bound that
supremum by the one over `D`. A countable dense subset of `D` detects vanishing, by continuity.
