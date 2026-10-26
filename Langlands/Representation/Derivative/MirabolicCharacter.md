# Positive mirabolic localization character

Author: Worker 653.

This module constructs the character used by Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), §3.1,
printed p.450 (PDF page 11, zero-based index 10). Sections 3.1–3.2,
printed pp.450–451, identify the groups and the subsequent functor setting;
§1.8, printed p.444 (PDF page 5), specifies character localization.
The registered original is `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
No applicable errata entry for this source was found in the supplied public
notes or literature.

The source's `P_m` is the subgroup of `GL_m` with final row `(0,...,0,1)`.
The Library's `GeneralLinear.mirabolic n F` is therefore `P_(n+1)`, and
`GeneralLinear.Mirabolic.radical n F` is `V_(n+1)`. In this module the
character with parameter `n` is on `radical (n+1) F = V_(n+2)`, normalized
by the actual standard embedded `P_(n+1)`. These groups and embeddings
are imported from `Langlands.Group.GL.MirabolicRadical`.

The source and the implemented interface both use a nontrivial additive
character. The Library's `HarmonicAnalysis.UnitaryAdditiveCharacter` bundles
continuity and nontriviality with its circle-valued additive character.
The proofs below do not invoke the nontriviality field, but that field
remains a hypothesis of every character-dependent declaration. The coordinate,
invariance, continuity, open-kernel and restriction proofs below are derived
implementation results. The algebraic helpers work over every commutative
ring in arbitrary universe `uF`.

## Character and positive entry formula

In namespace `Langlands.Derivative.Mirabolic`,
`lastCoordinate n : radical (n+1) F →* Multiplicative F` composes the
published radical coordinate group equivalence with additive evaluation
at `Fin.last n`. Thus `lastCoordinate_apply` extracts the matrix entry
`u.val.val.val (Fin.last n).castSucc (Fin.last (n+1))`.

`theta ψ n : radical (n+1) F →* ℂˣ` then applies the additive character
and the canonical map from the circle to complex units. It is a group
homomorphism by composition. The formulas `theta_apply` and
`theta_radicalElement` give

```
(theta ψ n u : ℂ) = ψ.complex (radicalCoordinates u (Fin.last n))
(theta ψ n (radicalElement v) : ℂ) = ψ.complex (v (Fin.last n)).
```

This is the positive final adjacent entry prescribed in BZ77 §3.1.
`norm_theta` proves that its complex value has norm one.

## Invariance under the actual embedded mirabolic

`theta_isInvariant` has exactly the published
`Jacquet.Localization.IsInvariant` type, with
`U = radical (n+1) F`, `M = successorSubgroup n F`, and the imported
`successorSubgroup_le_normalizer` witness. Here `M` is the actual range
of `successor : mirabolic n F →* mirabolic (n+1) F`; its genuine
identification with the smaller mirabolic is `successorEquiv`.

The proof first writes an element of `M` as a successor image and an
element of `U` as `u(v)`, using the two equivalences' surjectivity.
The imported concrete conjugation formula becomes

```
diag(g,1) * u(v) * diag(g,1)⁻¹ = u(g.val.val.mulVec v)
```

for `g : mirabolic n F`. `mulVec_last` expands the last row
`(0,...,0,1)` to prove that the last coordinate of this matrix-vector
product is `v (Fin.last n)`. Applying the character gives invariance
with the same conjugation orientation as `Jacquet.Localization`.

## Agreement with the standard Whittaker character

The imported `radicalToUpperUnipotent` includes the radical into the
actual ambient upper-unipotent matrix group while preserving its matrix.
`superdiagonalSum_radical` splits the sum of adjacent entries into its
first `n` terms and its last term. The fixed identity columns make every
first term zero, since its row and column indices differ; the last term
is precisely the extracted last coordinate.

Extensionality on complex units and that sum identity prove the literal
homomorphism equality

```
theta ψ n =
  (Whittaker.standardCharacter ψ (n+1)).comp radicalToUpperUnipotent.
```

The theorem is `theta_eq_standardCharacter_comp`. It uses the published
positive `standardCharacter`, with its rank parameter shifted so that
its ambient matrices have size `n+2`.

## Continuity and the supplied p-adic topology

For any topology on the commutative ring `F`, `thetaContinuous ψ n`
bundles the same homomorphism as a continuous monoid homomorphism.
The proof composes continuous matrix-entry extraction with the supplied
continuous circle-valued character. It checks continuity of both the
value and inverse value in the units topology, using inversion in the
circle. This needs no topological-ring assumption.

`theta_isOpen_ker` applies the published
`Langlands.isOpen_ker_of_continuous_complex_character` when the actual
radical has a `NonarchimedeanGroup` instance. That result obtains an
open subgroup inside a small character neighborhood; the bound on all
powers forces the character to be one there and hence makes its kernel
open.

Namespace `Langlands.PadicField.TopologicalData` specializes this construction
for every prime `p`, `[Fact p.Prime]`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and character
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`:

- `T.mirabolicTheta ψ n` is the same complex-unit homomorphism.
- `T.mirabolicThetaContinuous ψ n` supplies continuity for `T.topology`.
- `T.mirabolicTheta_isOpen_ker ψ n` proves its actual kernel open for that
  topology. The proof installs `T.valuativeRel` and `T.localField`, applies
  `Langlands.valuativeGeneralLinearNonarchimedean` to the actual
  `GL_(n+2)`, and uses the published subgroup instance twice, for the
  mirabolic and then its radical.

No representation carrier is a parameter or restricted by these results.
All character constructions include `n=0`: they then concern `V_2` and
the embedded trivial `P_1`. The imported group module separately includes
`V_1`, `P_1`, and the actual `GL_0`. This module constructs no normalized
functor or modulus comparison.
