# The regular σ-lift identity implies the σ-lift identity

`Langlands.BaseChange.RegularSigmaLiftUpgradeStatement.{u, v, uV, uW}` is a
proposition. Under the eight premises below, an `IsRegularSigmaLift` between
irreducible admissible representations implies an `IsSigmaLift` for the same
intertwiner `A` and scalar `c`.

## Setting

The binders are those of `SigmaLiftCharacterIdentityForwardStatement`.
The base `F : Type u` is a nonarchimedean local field of characteristic zero
with the `Field`, `ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField`
and `CharZero` instances. The upper algebra `E : Type v` is a commutative
topological `F`-algebra with its module topology (`CommRing`, `Algebra`,
`TopologicalSpace`, `IsTopologicalRing` and `IsModuleTopology`).

For every `σ : E ≃ₐ[F] E` and `l n : ℕ`, the hypothesis
`hE : IsCyclicAlgebra σ l` from `Langlands.BaseChange.Norm` says that `E` is finite and
reduced, has dimension `l` over `F`, and that `σ` has order `l` with fixed
subalgebra equal to the image of `F`. This includes split cyclic algebras and
composite degrees. The instance block takes `Module.Finite F E` from `hE.1`.
It gives `GeneralLinear n F` and `GeneralLinear n E` their Hausdorff, locally
compact and totally disconnected instances via
`LocalFieldTopology.generalLinear_t2Space`,
`LocalFieldTopology.generalLinear_locallyCompactSpace`,
`LocalFieldTopology.generalLinear_totallyDisconnectedSpace`,
`generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite`
and `generalLinear_totallyDisconnectedSpace_of_finite`.

Here `GeneralLinear n R` is `GL_n(R)`. The carriers `V : Type uV` and
`W : Type uW` are implicit and carry `AddCommGroup` and `Module ℂ` instances.
The representations `π` of `GL_n(F)` on `V` and `τ` of `GL_n(E)` on `W` have
`hπ : IsAdmissible π` and `hτ : IsAdmissible τ`. Admissibility includes smoothness
and finite-dimensional invariants under every open subgroup. The proposition
assumes `π.IsIrreducible` and `τ.IsIrreducible`. It quantifies over every
`A : SigmaIntertwiner σ n τ`, an equivalence from `τ` to `τ` precomposed with
the entrywise action of `σ`, and every `c : ℂ`.

## Premises

The first five premises are those of `SigmaLiftCharacterIdentityForwardStatement`
and the last three are those of `SigmaLiftCharacterIdentityReverseStatement`,
in the following order.

1. `TwistedCharacterRegularValuesStatement.{u, u, uV}` gives local character
   values on the ordinary regular semisimple locus by taking the trivial
   cyclic algebra `F/F` and the identity intertwiner.
2. `TwistedCharacterRegularValuesStatement.{u, v, uW}` gives local twisted
   character values on the σ-regular locus. A local value means that the
   distribution on test functions supported near the point is that value
   times their Haar integral.
3. `RegularTransferStatement.{u, v}` gives concordant regularly supported
   transfers for σ-regularly supported test functions, and transfers in the
   opposite direction for regularly supported functions whose orbital
   integrals vanish off norms.
4. `ConcordantIntegralEqualityStatement.{u, v}` equates the total integrals
   of concordant Schwartz–Bruhat functions for the Haar measures used in
   concordance.
5. `SigmaLiftCharacterIdentity.SigmaRegularOpenStatement.{u, v}` gives
   openness of the σ-regular locus.
6. `ConcordantIntegrableIntegralEqualityStatement.{u, v}` equates the total
   integrals of concordant integrable functions.
7. `CharacterLocalIntegrabilityStatement.{u, uV}` supplies an ordinary
   character function that represents the distribution, is locally
   integrable for every Haar measure, and is locally constant at regular
   semisimple elements.
8. `TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}` supplies the
   corresponding function for the twisted distribution, locally constant
   at σ-regular elements.

## Conclusion

```lean
IsRegularSigmaLift σ l π hπ τ hτ A c → IsSigmaLift σ l π hπ τ hτ A c
```

Both predicates include `c ≠ 0` and use the trace identity
`tr(τ(φ) ∘ A) = c · tr π(f)` for every pair of Haar measures and concordant
Schwartz–Bruhat functions `φ` on `GL_n(E)` and `f` on `GL_n(F)`. Concordance
matches twisted and ordinary orbital integrals on associated regular
classes and requires the ordinary orbital integrals to vanish at regular
non-norms. `IsRegularSigmaLift` from `SigmaDiscreteRegularDescentStatement`
requires σ-regular support for `φ`, regular semisimple support for `f`, and
`det g ∈ N_{E/F}(Eˣ)` wherever `f g ≠ 0`. `IsSigmaLift` from `TwistedCharacter`
extends the identity to all concordant pairs.

## Proof plan

1. Adapt `sigmaLiftCharacterIdentityForward`
   to derive `IsShintaniLift`, the corresponding identity of local character
   values at each norm-associated pair `(δ, γ)` with `γ` regular semisimple.
   Its test pair starts with the characteristic function of a compact open
   σ-regular neighborhood of `δ` and a regularly supported transfer.
   The forward proof localizes the pair by cutting along characteristic
   polynomial coefficients of the matrix norm on the twisted side and of
   the base-changed matrix on the ordinary side.
2. Impose the norm-determinant support condition on this localized pair
   before using the regular trace identity. The scalar norm image
   `N_{E/F}(Eˣ)` is an open subgroup because it contains the `l`th powers of
   base units, which contain a neighborhood of `1` by
   `Langlands.Global.AdelicFunctoriality.range_pow_mem_nhds_one` for the
   compatible local field norm. The subgroup is therefore clopen.
   Cut the ordinary function by the preimage under the determinant.
   `IsNormAssociated.norm_determinant_units_eq` from `CyclicAlgebraDeterminant`
   gives `det γ = N_{E/F}(det δ)` on associated pairs. The cutoff factor is
   thus `1` on the associated ordinary orbits, matching the factor `1`
   everywhere on the twisted side. At regular non-norms the cutoff
   multiplies a zero orbital integral by a constant on the orbit. This is
   the orbitwise calculation of
   `ConcordanceLocalization.concordant_cutoff`.
   Use the regular trace identity and the equality of total integrals,
   then cancel the nonzero integral of the localized twisted function to
   obtain the Shintani identity.
3. Apply `sigmaLiftCharacterIdentityReverse`
   with premises 6–8 to pass from the Shintani identity to `IsSigmaLift`.

For a cyclic field extension, this implication connects
`SigmaDiscreteRegularDescentStatement` to `SigmaDiscreteDescentStatement`.
The former asks for an irreducible square-integrable descent with
`IsRegularSigmaLift`, and `IsSigmaDiscreteSeries` supplies the irreducibility
of the upper representation. An unconditional descent by this route calls
for the regular descent and discharge of the eight displayed premises at
their stated universes.

## Sources

- Guy Henniart and Bertrand Lemaire, *Changement de base et induction
  automorphe pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011).
  The proposition and corollary of II.2.9 compare the distributional lift,
  the Shintani character identity and the identity on regularly supported
  concordant pairs (printed pp. 69–71, especially pp. 69–70, PDF pp. 77–79).
  II.6.13 uses the regular test identity to conclude the local σ-lift
  (printed pp. 129–130, PDF pp. 137–138), writing the scalar on the twisted
  trace side. Here `c` multiplies the ordinary trace, following II.2.7
  (printed p. 67, PDF p. 75). The norm-determinant support restriction and eight explicit
  premises adapt this step to the Library's regular lift and conditional
  character identity statements.
  Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
  SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  [Original text](https://www.numdam.org/item/10.24033/msmf.436.pdf)
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the
  Advanced Theory of the Trace Formula*, Annals of Mathematics Studies 120
  (1989). Chapter 1, §6.3, derives a local character identity on the image
  of the norm in the proof of Theorem 6.2(b) (printed p. 57, PDF p. 71).
  Source ID `arthur-clozel-1989-base-change`,
  SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  [Original text](https://www.claymath.org/library/cw/arthur/pdf/30.pdf)
