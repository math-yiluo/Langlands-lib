# Existence and classification of `β`-extensions (V2)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Theorem (5.2.2)(i)–(ii), printed p. 166 (PDF p. 178). This is statement V2 of Task 7427. Part (iii) of (5.2.2) is not included, as the task contract specifies.

`BetaExtensionStatement` quantifies, as in V1, over `F`, `V` (independent universes), `ψF` with `IsBKAdditiveCharacter`, a simple stratum `S = [𝔄, n, 0, β]` with `S.r = 0` and proof `hS : S.IsSimple`, a defining-sequence choice `q`, `θ ∈ C(𝔄, 0, β)`, and a representation `η` of `J^1 = J^1(β, 𝔄)` lying over `θ` (`IsHeisenbergRepresentation`). Write `J = J(β, 𝔄) = simpleJ …` and `U(𝔅_β) = relativeUnitFiltration S.chain S.b 0`. It asserts:

- (i) there are `d` and a `β`-extension `κ` of `η` (`IsBetaExtension`, definition 3) on `Fin d → ℂ`.
- (ii) for every `β`-extension `κ` of `η` and every smooth (`IsSmoothRepresentation`) finite-dimensional irreducible representation `κ'` of `J` (carriers in arbitrary universes): `κ'` is a `β`-extension of `η` if and only if there is a character `ξ : J →* ℂˣ` such that
  - `ξ` is trivial on `J^1`;
  - `ξ = χ ∘ det_B` on `U(𝔅_β)` for some character `χ` of `k_E^×`; and
  - `κ' ≅ κ ⊗ ξ` (`Representation.tprod` with `characterRepresentation ξ`).

The determinant condition is written as follows. `E = F[β]` is `elementAlgebra S.b`, made a field by `hS` (as in Task 7422's `factorsThroughCentralizerDet`); `𝔬_E = subfieldIntegers F E` with residue field `k_E = ResidueField 𝔬_E`; `B_β^× = Aut_E(V)` is `(Module.End E V)ˣ`, mapped into `G` by `relativeEndUnits E`. The condition says: there is `χ : k_E^× →* ℂˣ` such that for every `x ∈ Aut_E(V)` whose image lies in `U(𝔅_β)` and every unit `a` of `𝔬_E` with `a = det_E(x)`, `ξ(x) = χ(a mod 𝔭_E)`. For `x ∈ U(𝔅_β)` the determinant `det_E(x)` is a unit of `𝔬_E`, so this says `ξ | U(𝔅_β) = χ ∘ (det_B mod 𝔭_E)`, which is BK93's `χ ∘ det_B` with `χ` a character of `U(𝔬_E)/U^1(𝔬_E) = k_E^×`. BK93 writes `κ ⊗ χ ∘ det_B` with `χ ∘ det_B` extended to `J` through `J/J^1 = U(𝔅_β)/U^1(𝔅_β)`; following the contract, the statement instead quantifies over characters `ξ` of `J` trivial on `J^1` with the prescribed restriction to `U(𝔅_β)`, and does not use `J = U(𝔅_β) J^1`.

The smoothness and finite-dimensionality hypotheses on `κ'` express the convention that "representation of `J`" means a smooth finite-dimensional one. This is the proposition only; its proof is a separate task.
