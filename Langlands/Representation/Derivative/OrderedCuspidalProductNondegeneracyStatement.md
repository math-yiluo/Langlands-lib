# Ordered cuspidal products have no degenerate mirabolic submodules

Author: Worker 1166.

This module states Theorem 4.11 of Bernstein and Zelevinsky (1977) for actual
general linear groups over finite extensions of p-adic fields. Take an
ordered family of irreducible cuspidal representations `ρ_1, …, ρ_r` with
`ρ_j ≇ ν ρ_i` whenever `i < j`. Then every nonzero mirabolic submodule of the
normalized product `ρ_1 × ⋯ × ρ_r` has nonzero top derivative. The module
contains one proposition definition. It asserts no proof and takes no theorem
as a hypothesis.

## The declaration

`Langlands.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF,uV} F T : Prop`

The outer parameters are a prime `p` (`[Fact p.Prime]`), an actual finite
extension `F : PadicField.{uF} p` of `ℚ_p`, and a supplied topological
realization `T : F.TopologicalData`. The body starts with
`letI := T.topology`; no canonical topology is substituted. The proposition
says:

> For every `ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`,
> every `N : ℕ`, every block shape `B : BlockShape (N+1)` and every family
> `A : ∀ i : Fin B.length, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)`,
> assume that for all `i j : Fin B.length` with `i < j`
>
> ```lean
> (⟨B.size j, (A j).isoClass⟩ :
>     Σ d : ℕ, SupercuspidalClass.{uV,uF} (F := F.Carrier) (n := d)) ≠
>   ⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (A i).isoClass⟩
> ```
>
> Let `Π := (T.normalizedProductInductionFunctor.{uF,uV} B).obj (fun i => (A i).obj)`
> and `R := (generalLinearRestriction.{uF,max uF uV} T N).obj Π`. Then every
> `U : Subrepresentation R.representation` with `U ≠ ⊥` satisfies
>
> ```lean
> Nontrivial
>   ((mirabolicDerivativeOfOrder.{uF,max uF uV} T ψ N (N+1)
>       ⟨Nat.zero_lt_succ N, le_rfl⟩).obj
>     (SmoothRep.subrepresentation R U))
> ```

In the Lean source `Π` and `R` are written out inline at both occurrences;
there is no `let`.

## The objects and their source counterparts

### Groups and ranks

The source group is `G_n = GL_n(F)` with `n = N + 1`. The source mirabolic
subgroup `P_n` (BZ77 §3.1: last row `(0, …, 0, 1)`) is the Library's
`GeneralLinear.mirabolic N F.Carrier`. The Library indexes the mirabolic
group by `N` and embeds it in `GL_(N+1)`. No `P_0` is introduced, and every
`N : ℕ` is allowed, including `N = 0` (see Boundary cases).

### The additive character

`ψ` is a bundled continuous nontrivial additive character of `F` for
`T.topology`. BZ77 §3.1 fixes one nontrivial additive character `ψ` and uses
it only through the character `θ((v_ij)) = ψ(v_(n-1,n))` of the radical `V_n`.
This character enters the definition of `Φ⁻`. The Library's `Φ⁻` localizes
at `T.mirabolicTheta ψ n`, which is `ψ` of the last radical coordinate. The
statement quantifies over every such `ψ`, so it asserts the theorem for each
choice the source could fix. It does not claim that the derivative is
independent of `ψ`.

### The cuspidal blocks

`B : BlockShape (N+1)` is an ordered partition `N + 1 = n_1 + ⋯ + n_r` into
positive block sizes `n_i = B.size i`, with `r = B.length`. This is the
partition `(n_1, …, n_r)` of BZ77 §4.1. Since `N + 1 > 0`, there is at least
one block.

Each `A i` is an actual object of `GeneralLinear.SupercuspidalRep` of rank
`B.size i`. Its complex carrier lies in the independent universe `uV`. This
bundled object supplies its own hypotheses: it is a smooth complex
representation with `SmoothRep.IsIrreducible`, and it satisfies
`GeneralLinear.IsSupercuspidal`. That predicate means admissible, with
subsingleton Jacquet coinvariants for every proper standard block unipotent
radical (`B'.parabolic F ≠ ⊤`) and every conjugate of it. This is BZ77 §2.4
(printed p.446): an admissible quasicuspidal representation is *cuspidal*.
Vanishing for the standard radicals already forces vanishing for their
conjugates. So `A i` is exactly a representative of a cuspidal element
`ρ_i ∈ Irr G_(n_i)` as in the hypothesis of Theorem 4.11. No further
irreducibility, admissibility or vanishing premise is added. The actual
supplied representatives are used, and repetitions of equal classes are
allowed.

### The ordered condition `ρ_j ≇ ν ρ_i` for `i < j`

BZ77 §4.2 defines `ν(g) = |det g|`. In the Library, `ν^s` on `GL_d(F)` is
`T.determinantPowerCharacter d s`, the real power of `T.determinantNorm d`,
built from the residue-normalized absolute value (`|ϖ| = q^(-1)`). The
published class map `T.supercuspidalClassRealPowerTwist d 1` sends the class
of `ρ` to the class of `ρ ⊗ |det|^1 = ν ρ`. The exponent is `+1`.

The blocks may have different ranks, so the comparison is an inequality in
the sigma type `Σ d : ℕ, SupercuspidalClass (n := d)` of rank-indexed
isomorphism classes. Equality of first components is equality of ranks.
Given equal ranks, equality of second components is the existence of an
actual isomorphism (`SupercuspidalRep.isoClass_eq_iff`). Hence the hypothesis
for a pair `i < j` says: either `n_j ≠ n_i`, or `n_j = n_i` and
`ρ_j ≇ ν ρ_i`. This is the source condition "`ρ_j ≇ νρ_i` for any `i, j`
such that `i < j`" (BZ77 §4.11, printed p.456). No cast between ranks is
needed.

The hypothesis is imposed only for `i < j` (the order on `Fin B.length`).
It is not imposed for all pairs, the twist is not reversed, and both
orientations are not required. The relation `ρ_i ≅ ν ρ_j` with `i < j` is
allowed. So is `ρ_i ≅ ρ_j`.

### The product

`Π = (T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)`. By
the published `normalizedProductInductionFunctor_obj` (`rfl`), its
representation is `T.normalizedProductInduced B` of the blocks. This is
normalized parabolic induction from the standard upper block parabolic of
`B`, acting by right translation, with covariance

`f(p g) = δ_P(m)^(1/2) (ρ_1(m_1) ⊗ ⋯ ⊗ ρ_r(m_r)) f(g)`

(`normalizedProductInduced_covariant`), where `m` is the Levi part of `p` and
`δ_P = T.leviModulus B`. The normalizing character is the positive half
modulus `T.leviHalfCharacter B`. This is the product `ρ_1 × ⋯ × ρ_r` of BZ77
§4.1, with the induction conventions of §1.8(a) and §§2.2–2.3. It is also
case (I) of the product functors of §4.12 (printed pp.456–457). The carrier
of `Π` lies in universe `max uF uV`. The input universe `uV` is not
saturated.

### Restriction to the mirabolic group

`R = (Derivative.generalLinearRestriction T N).obj Π` is the restriction of
`Π` along the actual continuous inclusion `P_(N+1) ≤ GL_(N+1)`. It keeps the
carrier and is the source's `π |_P` (BZ77 §4.3).

### Mirabolic submodules

`U : Subrepresentation R.representation` is Mathlib's invariant subspace of
the actual `P_(N+1)`-action on the carrier of `Π`. These are BZ77's
`P`-submodules of `π`. They are actual subspaces, not isomorphism classes.
They need not be `GL_(N+1)`-invariant. `U ≠ ⊥` says that `U` is nonzero.
`SmoothRep.subrepresentation R U` (module `Representation.Category.Subquotients`)
is the smooth representation of `P_(N+1)` on `U` with the restricted action.

### The top derivative

BZ77 §3.5 (printed p.452) defines, for `τ ∈ Alg P_n` and `k = 1, …, n`, the
`k`-th derivative `τ^(k) = Ψ⁻ (Φ⁻)^(k-1) (τ) ∈ Alg G_(n-k)`. BZ77 §4.7
(printed p.455) calls `τ ∈ Alg G_n` or `τ ∈ Alg P_n` *non-degenerate* if
`τ^(n) ≠ 0` and *degenerate* if `τ^(n) = 0`.

The Library's `Derivative.mirabolicDerivativeOfOrder T ψ N k hk`, for
`0 < k ≤ N + 1`, is the derivative of order `k` on `P_(N+1)`. By
`mirabolicDerivativeOfOrder_eq` (`rfl`), it is
`mirabolicRankCast T h ⋙ mirabolicDerivative T ψ (N+1-k) (k-1)`, where
`h : N = (N+1-k) + (k-1)` is the proved rank equality. By
`mirabolicDerivative_eq` (`rfl`), `mirabolicDerivative T ψ m j` is
`phiMinusIterate T ψ m j ⋙ Mirabolic.psiMinus T m`, that is,
`Ψ⁻ ∘ (Φ⁻)^j`. The statement uses the top order `k = N + 1 = n`, with the
proof `⟨Nat.zero_lt_succ N, le_rfl⟩` of `0 < N+1 ∧ N+1 ≤ N+1`. Thus the
derivative is the rank transport along `N = 0 + N`, followed by
`Ψ⁻ (Φ⁻)^N`. This is `τ^(n) = Ψ⁻ (Φ⁻)^(n-1) (τ)`. Its value is a smooth
representation of `GL_(N+1-(N+1))`. That rank equals `0` only
propositionally; the statement keeps the published wrapper's codomain and
does not cast it.

`Nontrivial X` for the carrier of a complex vector space `X` says `X ≠ 0`.
So the conclusion says that `U` is non-degenerate in the sense of BZ77 §4.7.

## Correspondence with Theorem 4.11

BZ77 §4.11 (printed p.456) reads: "Let `ρ_i ∈ Irr G_(n_i)` be cuspidal
(`i = 1, …, r`). Suppose that `ρ_j ≇ νρ_i` for any `i, j` such that `i < j`.
Then the representation `π = ρ_1 × ⋯ × ρ_r` has no non-zero degenerate
`P`-submodules."

A nonzero degenerate `P`-submodule is a nonzero `P`-invariant subspace `ω` of
`π |_P` with `ω^(n) = 0`. Its absence means: every nonzero `P`-submodule `ω`
has `ω^(n) ≠ 0`. The Lean statement asserts this for every actual nonzero
`U`. The hypotheses correspond as described above: the blocks `A i` are the
cuspidal `ρ_i`, the sigma-class inequality for `i < j` is `ρ_j ≇ νρ_i`, and
`Π` is the normalized product.

## Normalizations

- `ν = |det|^1` with the residue-normalized absolute value, as in BZ77 §4.2.
- The product uses the positive half modulus `δ_P^(1/2)` (BZ77 §1.8(a),
  §2.3). Here `δ_P` is the explicit block modulus `T.leviModulus B` of
  `Group.GL.BlockModulus`. The published theorem `Langlands.glBlockModulusHaar`
  (module `Group.GL.BlockModulusHaarProof`, Worker 117) proves that it is the
  Haar module of Levi conjugation on the block unipotent radical, which is
  the source's `mod_U`. That theorem is not imported here; it is cited only
  as a proved comparison.
- `Ψ⁻` and `Φ⁻` are the published determinant-normalized minus functors of
  `Derivative.MirabolicMinus`: the unnormalized localization, twisted by
  `|det|^(-1/2)` on `GL_m` and on `P_(m+1)`, respectively. The sign follows
  BZ77 §1.8(b) and §3.2. The published theorems
  `psiMinusHaarInverseHalf_eq` and `phiMinusHaarInverseHalf_eq` (module
  `Derivative.MirabolicMinusNormalization`, Worker 710) prove that these
  characters are the inverse halves of the actual radical Haar moduli, which
  is the source's `mod_U^(-1/2)`. That module is not imported here either.
- The twist by a character keeps the carrier (`psiMinus_obj_carrier`,
  `phiMinus_obj_carrier`). The normalization of the minus functors changes
  only actions. Informally, the determinant characters are trivial on the
  unipotent radicals, so nonvanishing of the top derivative does not depend
  on that normalization. This remark is not formalized. The statement uses
  the published normalized functors.

No comparison remains open at the statement stage: both normalization
comparisons are proved and published. The proof successor still has to
connect them to whatever lower results it uses, by proved inputs.

## Boundary cases

- `N = 0`. Then `G_1 = GL_1(F)`, and `B` has a single block of size `1`.
  `A 0` is an irreducible supercuspidal representation of `GL_1(F)`. The Library
  `mirabolic 0` is the source's `P_1`, the trivial group. The derivative of
  order `1` is the rank transport along `0 = 0 + 0` followed by `Ψ⁻` at rank
  `0`, landing in `GL_0`. This case is included.
- `r = 1`. The ordered hypothesis is vacuous. The statement then says that a
  single irreducible cuspidal representation, restricted to `P_n`, has no
  nonzero degenerate submodule. BZ77 §4.15 derives this case from §4.4.
- Repeated classes. If `ρ_i ≅ ρ_j` for `i < j`, the hypothesis for that pair
  still holds, because the classes of `ρ` and `νρ` are different (BZ77
  Remark 4.2(1)). This is not used or asserted in Lean; the hypothesis is
  stated directly.

## What is not stated

- The converse in the remark following Theorem 4.11 (BZ77 p.456): if
  `ρ_j ≅ νρ_i` for some `i < j`, then `π` has a nonzero degenerate
  `G`-submodule. It is not stated.
- Theorem 4.9 and the Kirillov-model Remark 4.10 are not stated.
- No irreducibility of `Π`, no finite length, no existence of irreducible
  submodules, no value of the ambient top derivative, and no Grothendieck
  group identity is asserted.
- No finite-length, finite-dimensional, unitarity, genericity,
  segment-existence or derivative-theorem premise is added. The conclusion is
  not weakened to ambient top-derivative nonvanishing, to one chosen
  constituent, or to `GL_(N+1)`-invariant subspaces.

## Universes

`uF` is the field universe and `uV` the universe of the block carriers; they
are independent. The product `Π`, its restriction `R`, the subrepresentations
`U` and their derivatives live at carrier universe `max uF uV`. Accordingly
`generalLinearRestriction` and `mirabolicDerivativeOfOrder` are instantiated
at `.{uF, max uF uV}`. The proposition has exactly the level parameters
`uF, uV`.

## Imports and import closure

The direct imports are:

- `Langlands.Representation.Classification.SupercuspidalTwist`, for
  `SupercuspidalRep`, `SupercuspidalClass`, `SupercuspidalRep.isoClass` and
  `supercuspidalClassRealPowerTwist`;
- `Langlands.Representation.Induction.BlockFactors`, for
  `normalizedProductInductionFunctor`;
- `Langlands.Representation.Derivative.Homogeneity`, for
  `mirabolicDerivativeOfOrder`. It imports `Derivative.Iteration`
  (`generalLinearRestriction`) and `Category.Subquotients`
  (`SmoothRep.subrepresentation`).

`Classification.SupercuspidalProductStatement` is not imported. Its
irreducibility criterion uses an all-pairs condition and is not an input.

The transitive `Langlands` import closure at Library
`e3944f764d2c00d53ac87227e98601bb667f348f` has 72 modules besides this one. It
was computed from the `import` lines of the Library sources. Every one of
these Lean/Markdown pairs is byte-identical to the Library; none was edited.

- `Langlands.Group` (12): `GL.Basic`, `GL.BlockModulus`, `GL.Blocks`,
  `GL.Mirabolic`, `GL.MirabolicRadical`, `GL.Nonarchimedean`,
  `GL.NonarchimedeanStatement`, `GL.NormalizedCharacter`, `GL.Padic`,
  `GL.PadicBlocks`, `GL.RankMaps`, `GL.UpperUnipotent`
- `Langlands.HarmonicAnalysis` (1): `Basic`
- `Langlands.LocalField` (6): `Canonical`, `Definitions`,
  `Normalization.Definitions`, `Normalization.Proof`,
  `Normalization.Statement`, `Topology`
- `Langlands.Representation.Category` (3): `Basic`, `Subquotients`, `Twist`
- `Langlands.Representation.Classification` (2): `Supercuspidal`,
  `SupercuspidalTwist`
- `Langlands.Representation.Derivative` (4): `Homogeneity`, `Iteration`,
  `MirabolicCharacter`, `MirabolicMinus`
- `Langlands.Representation.Dual` (1): `Definitions`
- `Langlands.Representation.Induction` (3): `BlockFactors`, `Definitions`,
  `Parabolic`
- `Langlands.Representation.Jacquet` (5): `CharacterTwistEquiv`,
  `Coinvariants`, `Localization`, `PositiveCharacter`, `SmoothTwist`
- `Langlands.Representation.MatrixCoefficient` (3): `Definitions`,
  `LawsProof`, `LawsStatement`
- `Langlands.Representation.Smooth` (13): `Admissibility.CofinalProof`,
  `Admissibility.CofinalStatement`, `Admissibility.EquivalenceProof`,
  `Admissibility.EquivalenceStatement`, `Definitions`,
  `FixedVectors.Definitions`, `SmoothPart.BasicProof`,
  `SmoothPart.BasicStatement`, `SmoothPart.Definitions`,
  `Transfer.PullbackProof`, `Transfer.PullbackStatement`,
  `Transfer.SubquotientProof`, `Transfer.SubquotientStatement`
- `Langlands.Representation.Tensor` (1): `Finite`
- `Langlands.Representation.Twist` (13): `AdmissibilityProof`,
  `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`,
  `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`,
  `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`,
  `SubquotientProof`, `SubquotientStatement`
- `Langlands.Representation.Unitary` (1): `Basic`
- `Langlands.Representation.Whittaker` (2): `Algebraic`, `GeneralLinear`
- `Langlands.Topology` (2): `CompactNormCharacter`, `Nonarchimedean.Subgroup`

The closure consists of group, field, smooth-representation, twist,
induction, Jacquet-localization and derivative-construction infrastructure.
The proof modules in it prove basic laws: field normalization, matrix
coefficients, admissibility, smooth parts, transfer and twists. A file and
module-name scan for the excluded families found no match. The scan covered
segment, socle, head, Jacquet formula, two-supercuspidal, Leibniz, exactness,
support shift, coinvariant finiteness, mirabolic finite length,
classification and exhaustion. The closure contains no derivative theorem,
no segment or classification result, and no conclusion of any task excluded
by the contract. Importing these modules uses only their definitions.

## Proof in the source

BZ77 proves Theorem 4.11 in §4.15 (printed pp.458–459), by induction on `r`.
The case `r = 1` follows from §4.4 (Gelfand–Kazhdan: the derivatives of an
irreducible cuspidal representation). For `r > 1` it writes
`π = ρ_1 × π°` and reduces to an irreducible degenerate submodule `ω`. Using
the exact sequence of §4.13(a), it treats `ω ⊂ (ρ_1 |_P) × π°` with
§4.13(c), (d), §4.4, §3.5 and induction. It treats `ω ⊂ ρ_1 × (π° |_P)` with
§4.14(a) and Lemma 4.7(b). The product functors used there are defined in
§4.12, and §4.13 is proved in §7. These are references for the proof
successor only. They are not hypotheses of this statement. The reduction to
an irreducible `ω` and the exactness steps need independently proved inputs.

## Original source

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Literature ID
`bernstein-zelevinsky-1977-induced-i`, PDF SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

- Theorem 4.11 and the remark after it: printed p.456, one-based PDF p.17.
- Degenerate and non-degenerate: §4.7, printed p.455, PDF p.16.
- Derivatives `τ^(k) = Ψ⁻(Φ⁻)^(k-1)(τ)`: §3.5, printed p.452, PDF p.13.
- Restriction to `P` and derivatives of `G_n`-modules: §4.3, printed p.454,
  PDF p.15.
- Products, `ν` and Remark 4.2(1): §§4.1–4.2, printed p.454, PDF p.15.
- Cuspidal representations: §2.4, printed p.446, PDF p.7.
- `P_n`, `V_n`, `θ`, `Ψ⁻`, `Φ⁻`: §§3.1–3.2, printed pp.450–451, PDF
  pp.11–12.
- Normalizations: §1.8, printed pp.444–445, PDF pp.5–6.
- Product functors: §4.12, printed pp.456–458, PDF pp.17–19.
- Proof: §§4.13–4.15, printed pp.458–459, PDF pp.19–20.

The order `i < j`, the twist `νρ_i`, the definition of degeneration and the
derivative exponents were checked on the extracted text and on rendered page
images of PDF pp.13, 16 and 17. A bounded search of the supplied literature and
public notes found no applicable erratum. This is not a global absence claim.
