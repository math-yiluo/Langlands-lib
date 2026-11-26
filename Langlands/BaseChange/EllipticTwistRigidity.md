# Twist rigidity of essentially square-integrable traces on elliptic determinant regions

The module `Langlands.BaseChange.EllipticTwistRigidity` proves three results used to identify the
fibres of local cyclic base change over an essentially square-integrable representation of
`GL_n(F)`, `F` a nonarchimedean local field of characteristic zero:

- `ellipticTwistRigidity_of_separation`: from finite elliptic trace separation
  (`EllipticDiscreteTraceSeparationStatement`, taken as a hypothesis), proportional traces on the
  regular elliptic elements with determinant in an open subgroup `H` of finite index of `Fˣ`
  force a nonzero factor and a twist by a character of `Fˣ/H`;
- `IsCyclicAlgebra.normRange_isOpen_finiteIndex`: for a cyclic field extension `E/F`, the norm
  group `N_{E/F}(Eˣ)` is open and of finite index in `Fˣ`;
- `vanishesOffNorms_of_isNorm_support`: a function that is nonzero only at norms has vanishing
  orbital integrals at every regular semisimple non-norm.

The module does not prove `EllipticDiscreteTraceSeparationStatement`; the first result is
conditional on it.

## Notation (Library and Mathlib)

`GeneralLinear n F` is `GL_n(F)`, `GeneralLinear.determinant` its determinant.
`Character.distribution μ π hπ` (module `Langlands.Representation.Character.Basic`) is the
distribution character `f ↦ trace π(f)` for a Haar measure `μ`. `IsEllipticSupported f` (module
`Langlands.BaseChange.EllipticSupport`) says that `f` is nonzero only at regular elliptic
elements. `IsEssentiallySquareIntegrable` is the Library's essential square-integrability
(module `Langlands.JacquetLanglands.EssentiallySquareIntegrable`), `twist χ π` is
`g ↦ χ(g) • π(g)`, and `Representation.IsIrreducible`, `Representation.Equiv` are Mathlib's.
`IsNorm`, `IsCyclicAlgebra` are in `Langlands.BaseChange.Norm`; `VanishesOffNorms` in
`Langlands.BaseChange.OrbitalIntegral`.

## `ellipticTwistRigidity_of_separation`

Hypothesis `hSep : EllipticDiscreteTraceSeparationStatement.{u, u, max uV uV', uV'}`. For
`F : Type u` as above, `0 < n`, `H : Subgroup Fˣ` with `IsOpen (H : Set Fˣ)` and
`[H.FiniteIndex]`, the Borel σ-algebra and the `LocalFieldTopology` instances on `GL_n(F)`, a
Haar measure `μ`, irreducible admissible essentially square-integrable `π` on `V : Type uV` and
`π'` on `V' : Type uV'`, and `t : ℂ`: if

`Character.distribution μ π' hπ' f = t * Character.distribution μ π hπ f`

for every `f` with `IsEllipticSupported f` and `det g ∈ H` whenever `f g ≠ 0`, then `t ≠ 0` and
there is `κ : Fˣ →* ℂˣ` with `κ x = 1` for `x ∈ H` and
`Nonempty (π'.Equiv (twist (κ.comp GeneralLinear.determinant) π))`.

Proof.

1. *Characters of `Q = Fˣ/H`.* `Q` is finite and, `H` being open, discrete; let `d` be the
   composite of the determinant with `Fˣ → Q`. The characters `χ : Q →* ℂˣ` form a finite set
   (`Langlands.FiniteRep.AbelianNormalBrauer.charFintype`), and
   `Σ_χ χ(y) = |Q|` if `y = 1` and `0` otherwise (`sum_char_apply`). Each `χ ∘ d` is locally
   constant with open kernel and unitary values (finite order), so the twists `T₁ χ = (χ ∘ d) ⊗ π`
   and `T₂ χ = (χ ∘ d) ⊗ π'` are admissible (`isAdmissible_twist_iff`), irreducible
   (`isIrreducible_twist_iff`) and essentially square-integrable
   (`isSquareIntegrableModCenter_unitaryTwist` after the real `|det|` twist).
2. *Averaging.* The trace of a twist `(χ ∘ d) ⊗ ρ` at `f` is the trace of `ρ` at `(χ ∘ d) f`.
   Summing over `χ` turns `f` into `|Q|` times its cut-off to the clopen set `{det ∈ H}`
   (`ConcordanceLocalization.cutoff`). For a regular elliptic test `f` the cut-off satisfies the
   hypothesis, so `Σ_χ tr T₂ χ (f) = t · Σ_χ tr T₁ χ (f)`.
3. *Self-twists.* Let `S` be the set of `χ` with `π' ≅ T₂ χ`; it contains `1`. All its terms
   equal `tr π'(f)`, so `|S| tr π'(f) + Σ_{χ ∉ S} tr T₂ χ (f) = t · Σ_χ tr T₁ χ (f)` on regular
   elliptic tests.
4. *`t ≠ 0`.* If `t = 0`, `tr π'` is the combination `-(1/|S|) Σ_{χ ∉ S} tr T₂ χ` on regular
   elliptic tests. After lifting the carriers to a common universe
   (`universeLiftRepresentation`, `universeLiftEquiv`), separation, with index type the subtype
   `D₂` of characters `χ ∉ S` (empty when every twist of `π'` is a self-twist), makes `π'`
   equivalent to some `T₂ χ` with `χ ∉ S`, which contradicts the definition of `S`.
5. *The twist.* In general `tr π'` is the combination of all `tr T₁ χ` with coefficients
   `t/|S|` and of the `tr T₂ χ`, `χ ∉ S`, with coefficients `-1/|S|`. Separation, with index
   type the disjoint sum `D ⊕ D₂` of the character group `D` of `Q` and the subtype `D₂`, gives an
   equivalence of `π'` with a member of this family. It cannot be a `T₂ χ` with `χ ∉ S`, so
   `π' ≅ T₁ χ = (κ ∘ det) ⊗ π` with `κ = χ ∘ (Fˣ → Q)`, trivial on `H`.

## `IsCyclicAlgebra.normRange_isOpen_finiteIndex`

For `F` as above, a field `E` with `IsCyclicAlgebra σ l` (a cyclic Galois extension of degree
`l`), the subgroup `(Units.map (Algebra.norm F : E →* F)).range` of `Fˣ` is open and of finite
index. The proof realizes `F` as a finite extension of `ℚ_p` on its own carrier
(`CharZeroLocalField.padicField`, `CharZeroLocalField.topologicalData`) and `E` as a `p`-adic field
(`PadicField.ofField`), so that the norm range is the norm subgroup of local class field theory;
`isOpen_normSubgroup_of_isAbelianGalois` gives openness and
`NormUnitImage.normSubgroup_index_eq_finrank` gives index `[E : F]`. The extension is abelian
since its Galois group is generated by `σ` (`IsCyclicAlgebra.isGalois`,
`IsAbelianGalois.of_isCyclic`).

## `vanishesOffNorms_of_isNorm_support`

If `σ ^ l = 1` (here from `IsCyclicAlgebra σ l`) and `f g ≠ 0` implies `IsNorm σ l g`, then
`VanishesOffNorms σ l μ f` for every measure `μ`: for a regular semisimple non-norm `γ`, every
conjugate `x⁻¹ γ x` is a non-norm (`IsNormAssociated.twistedConj`), so the integrand of the
orbital integral of `f` at `γ` is identically zero.

## Sources and comparison

The averaging argument is that of G. Henniart and B. Lemaire, *Changement de base et induction
automorphe pour GL_n en caractéristique non nulle*, Mém. SMF 124 (2011), II.4.8, formula (3) and
the proof of the Lemme, printed pp. 90–91 (source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`), for
`H = N_{E/F}(Eˣ)`: the indicator of `{det ∈ H}` is the average of the characters of `Fˣ/H`
composed with the determinant. Henniart–Lemaire combine it with the elliptic orthogonality
relations (II.4.8, formulas (1)–(2), from Clozel 1991, Theorem 3); here those relations enter only
through `EllipticDiscreteTraceSeparationStatement`, whose Markdown derives it from them. The
conclusion `t ≠ 0` corresponds to their Lemme (1) (the character of an essentially discrete
representation is not zero on the elliptic norms), applied to `π'`. The norm subgroup result is
the openness and the index formula of local class field theory for the cyclic extension `E/F`.
