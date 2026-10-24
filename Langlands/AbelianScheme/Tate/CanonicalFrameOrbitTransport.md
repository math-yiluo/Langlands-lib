# Canonical comparisons of geometric fixed Tate-frame orbits

Author: Worker 142.

This module constructs canonical equivalences between the full, and separately
the prime-to-modulus, fixed Tate-frame orbit spaces at two geometric points.
Each construction takes the published proposition `GeometricPathExists` as an
explicit hypothesis. It chooses a path and proves equality with transport along
every path between those endpoints. Identity, composition, inverse, right
translation and level-forgetting laws follow. These are ambient tensor-linear
frame orbits; no polarization-pairing condition is imposed.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Section III.1, printed pp.91–92 / PDF pp.99–100. Registered source
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  Page 91 defines fundamental-group-invariant right orbits of Tate frames,
  states canonical independence of the geometric point for the moduli problem,
  and gives right precomposition under the conjugate-subgroup inclusion.
  Page 92 introduces the corresponding prime-to-p orbit data.
- Grothendieck et al., *Revêtements étales et groupe fondamental* (SGA 1),
  recomposed annotated edition, arXiv:math/0206203v2, Exposé V §7,
  printed p.115 / PDF p.131. Registered source `sga1-arxiv-math-0206203v2`,
  SHA256
  `8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
  Its final paragraph asserts the existence of an isomorphism between the
  finite geometric fibre functors for two geometric points of a connected,
  locally noetherian scheme, allowing different algebraically closed fields.

These original passages were read from local PDF text extractions. No
source-specific errata directory was present in the supplied Library.
This is a **derived** intermediate construction, rather than the full
Harris–Taylor moduli comparison. It uses the published
`AdelicFrameTransport` and `PrimeToAdelicFrameTransport` constructions and
their path-independence and coherence laws. The additional ingredient is
classical choice from the explicit geometric existence proposition, followed
by those laws. The SGA existence theorem itself is not proved here.

## Exact hypotheses and orbit spaces

The base `S : Scheme.{u}` has instances `ConnectedSpace S` and
`IsLocallyNoetherian S`. Fix an actual `A : AbelianScheme S`, a rational
algebra `D`, and `i : D →ₐ[ℚ] Rationalization.End A`. The geometric points
`s`, `t`, and, for composition, `r` have independently quantified
algebraically closed fields in universe `u`. The fields need no identification
or embedding into one another. Finite-fibre hypotheses `hs`, `ht`, and `hr`
are explicit, for every actual `FiniteEtale.Cover S`.

For the full construction retain
`h : Global.RationalProfiniteIntegerAdeleComparison`, an arbitrary module `V`
over `D ⊗[ℚ] Global.FiniteAdeles ℚ`, an arbitrary group `G` with representation
`ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V)`, and a subgroup `U`.
The same scalar comparison and endomorphism action are used at every endpoint.
Also retain `htor : TorsionFiniteEtaleStatement` and invertibility on `S` of
every positive torsion order:
`hu : ∀ n : GroupScheme.Tate.Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))`.

The source and target are exactly the published `AdelicFrameOrbit` types.
Their frames are tensor-algebra-linear equivalences from `V` to the actual
`RationalFull A (Over.mk s)` or its analogue at `t`, whose underlying Tate
carrier is the rationalization over the integers of the coherent actual
torsion sections. Their right action is `eta · g = eta ∘ ρ(g)`. The orbit
classes must be fixed under the actual finite fibre-functor automorphism
group acting by target monodromy; representatives need not be fixed.

The away construction takes any natural modulus `m`, the same kind of full
comparison `h`, and
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`.
The coefficient ring is `D ⊗[ℚ] Global.PrimeToFiniteAdeles m` and the target
carrier is `RationalAway A (Over.mk s) m`. Its integral inverse system selects
positive orders coprime to `m` before rationalization. Here `hu` requires
invertibility only for those retained orders; no primality of `m` or
invertibility of every order is assumed. Prime `m = p` gives the prime-to-p
specialization. Common `h` and `hAway` are retained across endpoints.

Neither construction assumes frames or fixed orbit spaces are nonempty.
No independence of scalar-comparison witnesses is asserted.

## Definitions and implemented laws

The hypothesis

```lean
hp : FiniteEtale.GeometricPathExists s t hs ht
```

has body `Nonempty (fiberFunctor s hs ≅ fiberFunctor t ht)`. It is not a
structure field hiding a comparison of Tate modules. The definition
`adelicFrameOrbitCanonicalEquiv` applies `adelicFrameOrbitTransport` to
`Classical.choice hp`; `primeToAdelicFrameOrbitCanonicalEquiv` applies its
away counterpart in the same way. Both return equivalences of the actual
fixed-orbit spaces described above.

Each declaration family has the following laws:

- `_eq_transport` identifies the whole canonical equivalence with transport
  along any supplied path with the same endpoints. The proof applies the
  published fixed-orbit path-independence theorem to the chosen and supplied
  paths. Thus canonicity is a property of the orbit equivalence, not of the
  chosen path, fundamental-group identification or representative transport.
- `_refl` compares the chosen path to the identity path and applies the
  existing identity transport law. It holds for any supplied existence proof
  at the repeated point.
- `_trans` takes existence proofs for the three endpoint pairs and compares
  the directly chosen path to the composite of the two successively chosen
  paths. The transport composition theorem gives `E_sr = E_st.trans E_tr`,
  meaning first transport from `s` to `t`, then from `t` to `r`.
- `_symm` compares the reverse-direction chosen path to the inverse of the
  forward chosen path and applies the transport inverse law.
- `_translate` commutes the equivalence with right translation by `g` under
  `∀ u ∈ U, g⁻¹ * u * g ∈ U'`. It is the existing transport/translation square
  at `Classical.choice hp`. `_forget` uses the corresponding published square
  for `U ≤ U'`.

The away proofs use exactly the corresponding away path-transport laws.
The path choice uses classical choice; the definitions are in a noncomputable
section.

## Remaining scope

Geometric path existence is an explicit, unproved dependency in this module.
The published statement is imported unchanged. The module neither establishes
that existence theorem nor removes the explicit finite-etaleness,
finite-fibre or scalar-comparison inputs. It constructs coherent canonical
comparisons of ambient fixed-orbit spaces conditional on these inputs.

Actual Weil pairings, preservation of polarization forms and their twists,
the similitude-frame subtype, rational topology, geometric pointed base
change, and the unpointed PEL moduli functor remain separate constructions.
There is no asserted map from full frames to away frames here, and no claim
of parent-task completion.
