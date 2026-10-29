# Bernstein–Zelevinsky derivatives by iterated minus functors

Author: Worker 818.

This module builds the Bernstein–Zelevinsky derivative functors on smooth
complex representations of the actual mirabolic groups and of the actual
groups `GL_N`. They are composites of the published determinant-normalized
minus functors `Mirabolic.phiMinus` and `Mirabolic.psiMinus` from
`Langlands.Representation.Derivative.MirabolicMinus`. The module defines
functors and proves only elementary construction equations: defining
composites, first and top derivatives, object and morphism descriptions, rank
transports and independence of the proof of `k ≤ N`. It proves no exactness,
finite length, nonvanishing, highest-derivative, filtration or classification
statement. It defines no highest-derivative predicate.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
printed page numbers below were checked against the PDF.

- §3.5, printed p.452 (one-based PDF page 13): for `τ ∈ Alg P_n` the source
  defines `τ^(k) = Ψ⁻ ∘ (Φ⁻)^(k-1)(τ) ∈ Alg G_(n-k)` for `k = 1, …, n` and
  calls it the `k`-th derivative. Its footnote (2) says that `(Φ⁻)^m` means
  the composite `Alg P_n → Alg P_(n-1) → … → Alg P_(n-m)`, so the rank drops
  by one at each step. The rest of §3.5 (the filtration and the corollary on
  irreducible representations of `P_n`) is not used here.
- §4.3, printed p.454 (one-based PDF page 15): for `π ∈ Alg G_n` the source
  defines `π^(0) = π` and `π^(k) = (π|_(P_n))^(k)` for `k = 1, …, n`, where
  `π|_(P_n)` is the restriction to `P_n`.
- §3.2, printed pp.450–451 (one-based PDF pages 11–12): `Ψ⁻` and `Φ⁻` are
  the normalized localizations of §1.8. The source notes that they differ from
  the functors of its reference [1] by a twist with `mod^(1/2)`.

No errata entry for this source is registered in the project literature index,
the central library or the public notes. The published
`MirabolicMinus` pair records the same.

## Parameters

Throughout, `p : ℕ` is prime (`[Fact p.Prime]`) and `F : PadicField.{uF} p`.
`F` is implicit, determined by `T : F.TopologicalData`, as in
`MirabolicMinus`. This is what the call spelling
`generalLinearDerivative T ψ N k hk` requires. Every type installs
`letI := T.topology`; no canonical topology is substituted. The additive
character is `ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`. It
bundles continuity and nontriviality, so the trivial additive character is not
covered. `ψ` is used only through `Mirabolic.phiMinus T ψ`.

Every functor goes between actual categories `SmoothRep.{0, uF, uV} ℂ _`. The
carrier universe `uV` is independent of `uF` and is never enlarged. Every
functor and functor equation has the universe parameters `.{uF, uV}` in that
order; the three rank equalities have none. The checked
types are, for example,

```
generalLinearDerivative.{uF, uV} T ψ (N k : ℕ) (hk : k ≤ N) :
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier) ⥤
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N - k) F.Carrier)
generalLinearDerivativePositive.{uF, uV} T ψ (n k : ℕ) :
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + k + 1) F.Carrier) ⥤
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)
```

## Rank and order conventions

`GeneralLinear.mirabolic n F.Carrier` is the source's `P_(n+1)`. Hence, from
`MirabolicMinus`:

- `Mirabolic.phiMinus T ψ m` is the source's `Φ⁻ : P_(m+2) → P_(m+1)`, with
  Lean type `SmoothRep ℂ (mirabolic (m+1)) ⥤ SmoothRep ℂ (mirabolic m)`;
- `Mirabolic.psiMinus T n` is the source's `Ψ⁻ : P_(n+1) → GL_n`, with Lean
  type `SmoothRep ℂ (mirabolic n) ⥤ SmoothRep ℂ (GeneralLinear n)`.

The declarations here have the following meaning, with `k : ℕ` the number of
`Φ⁻` steps:

| Lean | Source | Ranks | Derivative order |
| --- | --- | --- | --- |
| `phiMinusIterate T ψ n k` | `(Φ⁻)^k` | `P_(n+k+1) → P_(n+1)` | none |
| `mirabolicDerivative T ψ n k` | `τ ↦ τ^(k+1) = Ψ⁻ ∘ (Φ⁻)^k(τ)` | `P_(n+k+1) → GL_n` | `k + 1` |
| `generalLinearRestriction T n` | restriction of `π` to `P_(n+1)` | `GL_(n+1) → P_(n+1)` | none |
| `generalLinearDerivativePositive T ψ n k` | `π ↦ π^(k+1)` | `GL_(n+k+1) → GL_n` | `k + 1` |
| `generalLinearDerivative T ψ N k hk` | `π ↦ π^(k)` | `GL_N → GL_(N-k)` | `k` |

For the mirabolic derivative, take `N = n + k + 1` and order `j = k + 1` in
§3.5. Then `τ^(j) = Ψ⁻ ∘ (Φ⁻)^(j-1)(τ) ∈ Alg G_(N-j)` and `N - j = n`.

## Iterated Φ⁻

`phiMinusIterate T ψ n k` is defined by structural recursion on `k`:

```
phiMinusIterate T ψ n 0       = 𝟭 _
phiMinusIterate T ψ n (k + 1) = Mirabolic.phiMinus T ψ (n + k) ⋙ phiMinusIterate T ψ n k
```

The source of the successor case is `mirabolic (n + (k + 1))`, which is
definitionally `mirabolic ((n + k) + 1)`, the source of
`Mirabolic.phiMinus T ψ (n + k)`. So no arithmetic transport is needed. The
first functor applied is `Φ⁻` at the largest rank, and the ranks then drop one
at a time, as in footnote (2). It is not a power of a fixed-rank endofunctor.
The laws are:

- `phiMinusIterate_zero`: the `k = 0` case is the identity functor (`rfl`);
- `phiMinusIterate_succ`: the successor equation above (`rfl`);
- `phiMinusIterate_one`: `phiMinusIterate T ψ n 1 = Mirabolic.phiMinus T ψ n`
  (`Functor.comp_id`);
- `phiMinusIterate_obj_succ` and `phiMinusIterate_map_succ`: on objects and on
  morphisms, the `k + 1` iterate is the `k` iterate applied to the image under
  `Mirabolic.phiMinus T ψ (n + k)` (`rfl`).

## Mirabolic derivatives

`mirabolicDerivative T ψ n k` is the composite
`phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n`. The laws are:

- `mirabolicDerivative_eq`: this defining composite (`rfl`);
- `mirabolicDerivative_zero`: the first mirabolic derivative is
  `Mirabolic.psiMinus T n` (`Functor.id_comp`);
- `mirabolicDerivative_succ`:
  `mirabolicDerivative T ψ n (k + 1) = Mirabolic.phiMinus T ψ (n + k) ⋙ mirabolicDerivative T ψ n k`
  (`Functor.assoc`);
- `mirabolicDerivative_obj` and `mirabolicDerivative_map`: objects and
  morphisms are those of `Ψ⁻` applied to the images under the iterate (`rfl`).

## Restriction to the mirabolic subgroup

`generalLinearRestriction T n` is
`Mirabolic.continuousPullbackFunctor (mirabolic n F.Carrier).subtype continuous_subtype_val`.
This is pullback along the actual subgroup inclusion
`mirabolic n F.Carrier →* GeneralLinear (n + 1) F.Carrier`, which is
continuous for the subspace topology. The elementary pullback functor is the
one published in `MirabolicMinus`. The laws are:

- `generalLinearRestriction_eq`: this definition (`rfl`);
- `generalLinearRestriction_obj_carrier`: the carrier of the restricted object
  is the carrier of `A` (`rfl`);
- `generalLinearRestriction_obj_representation`: the restricted action is
  `A.representation.comp (mirabolic n F.Carrier).subtype` (`rfl`);
- `generalLinearRestriction_action`: for `h : mirabolic n F.Carrier` and
  `v : A`, the restricted action of `h` on `v` is `A.representation (h : GL_(n+1)) v`
  (`rfl`);
- `generalLinearRestriction_map_toLinearMap` and
  `generalLinearRestriction_map_apply`: the restriction of a morphism has the
  same underlying linear map and the same values (`rfl`).

## Positive-order GL derivatives

`generalLinearDerivativePositive T ψ n k` is the composite
`generalLinearRestriction T (n + k) ⋙ mirabolicDerivative T ψ n k`. This is
§4.3 at order `k + 1`, with §3.5 applied to `π|_(P_(n+k+1))`. The laws are:

- `generalLinearDerivativePositive_eq`: this defining composite (`rfl`);
- `generalLinearDerivativePositive_eq_comp`: the fully unfolded composite
  `generalLinearRestriction T (n + k) ⋙ phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n`
  (`rfl`);
- `generalLinearDerivativePositive_zero`: the first derivative is
  `generalLinearRestriction T n ⋙ Mirabolic.psiMinus T n`;
- `generalLinearDerivativePositive_succ`: the order `k + 2` derivative is
  `generalLinearRestriction T (n + k + 1) ⋙ Mirabolic.phiMinus T ψ (n + k) ⋙ mirabolicDerivative T ψ n k`;
- `generalLinearDerivativePositive_obj` and `generalLinearDerivativePositive_map`:
  objects and morphisms are the mirabolic derivative applied to the restricted
  object or morphism (`rfl`).

## Rank transport

`generalLinearRankCast T (h : a = b)` is a functor
`SmoothRep ℂ (GeneralLinear a F.Carrier) ⥤ SmoothRep ℂ (GeneralLinear b F.Carrier)`.
It is `Eq.rec` of the identity functor along `h`, with motive
`c ↦ (SmoothRep ℂ (GeneralLinear a) ⥤ SmoothRep ℂ (GeneralLinear c))`. It is
internal packaging, not a source construction. It is an equation-level
transport, not a natural isomorphism. The laws are:

- `generalLinearRankCast_refl`: for every proof `h : a = a` it is the identity
  functor (`rfl`);
- `generalLinearRankCast_obj`: on objects it is
  `cast (congrArg (fun c => SmoothRep ℂ (GeneralLinear c F.Carrier)) h)`;
- `generalLinearRankCast_map_heq`: on morphisms the image of `f` is
  heterogeneously equal to `f`;
- `generalLinearRankCast_trans`, `generalLinearRankCast_symm_comp` and
  `generalLinearRankCast_comp_symm`: transports compose along `h.trans h'`, and
  the transports along `h` and `h.symm` are mutually inverse, as equalities of
  functors.

## Derivatives indexed by source rank and order

The rank equalities are proved by `omega`:

```
rank_eq_of_succ_le  (hk : k + 1 ≤ N)        : N = N - (k + 1) + k + 1
rank_eq_of_pos_le   (hk : k ≤ N) (0 < k)    : N = N - k + (k - 1) + 1
rank_eq_top_of_pos  (0 < N)                 : N = 0 + (N - 1) + 1
```

`generalLinearDerivative T ψ N k hk` is defined by matching on `k`:

```
generalLinearDerivative T ψ N 0 _        = 𝟭 _
generalLinearDerivative T ψ N (k + 1) hk =
  generalLinearRankCast T (rank_eq_of_succ_le hk) ⋙
    generalLinearDerivativePositive T ψ (N - (k + 1)) k
```

At `k = 0` the target `GL_(N - 0)` is definitionally `GL_N`, so the identity
needs no transport. At order `k + 1` the rank cast moves `GL_N` to
`GL_((N - (k + 1)) + k + 1)`, the source of the positive derivative, whose
target is `GL_(N - (k + 1))`. Only the source rank is transported. The
positive derivative itself is the actual composite above. The laws are:

- `generalLinearDerivative_proof_irrel`: for `hk hk' : k ≤ N` the two functors
  are equal (`rfl`, by proof irrelevance). Every equation below holds for any
  proof of the order bound and of the rank equalities, since these are
  propositions;
- `generalLinearDerivative_zero`: the zeroth derivative is the identity functor
  of `SmoothRep ℂ (GeneralLinear N F.Carrier)` (`rfl`);
- `generalLinearDerivative_succ`: the order `k + 1` defining equation (`rfl`);
- `generalLinearDerivative_of_pos`: for `0 < k ≤ N`,
  `generalLinearDerivative T ψ N k hk = generalLinearRankCast T (rank_eq_of_pos_le hk hpos) ⋙ generalLinearDerivativePositive T ψ (N - k) (k - 1)`.
  This is the positive-order identification with the transport along
  `(N - k) + (k - 1) + 1 = N`;
- `generalLinearDerivative_succ_obj` and `generalLinearDerivative_succ_map`:
  objects and morphisms are the positive derivative applied to the transported
  object or morphism (`rfl`).

### Boundary cases

- `N = 0, k = 0`: `generalLinearDerivative_zero_zero`, the identity functor of
  `SmoothRep ℂ (GeneralLinear 0 F.Carrier)`.
- `N = 1`: `generalLinearDerivative_one_zero` gives the identity at `k = 0`.
  `generalLinearDerivative_one_one` gives
  `generalLinearDerivative T ψ 1 1 hk = generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0`,
  the functor `GL_1 → P_1 → GL_0`.
- First derivative in general: `generalLinearDerivative_one` gives
  `generalLinearDerivative T ψ (n + 1) 1 hk = generalLinearRestriction T n ⋙ Mirabolic.psiMinus T n`.
  The rank cast here is along a proof of `n + 1 = n + 1`, so it is the identity.
- Top order `k = N`: the target is `GL_(N - N)`, which is not definitionally
  `GL_0` for a variable `N`. The top equations therefore compose with
  `generalLinearRankCast T (Nat.sub_self N)` to land in
  `SmoothRep ℂ (GeneralLinear 0 F.Carrier)`.
  - `generalLinearDerivative_top_zero`: for `N = 0` the result is the identity
    of `GL_0`.
  - `generalLinearDerivative_top_succ`: for `N = n + 1` the result is
    `generalLinearRankCast T (Nat.zero_add (n + 1)).symm ⋙ generalLinearDerivativePositive T ψ 0 n`,
    the order `n + 1` derivative `GL_(0+n+1) → GL_0`.
  - `generalLinearDerivative_top`: the same for every `0 < N`, with
    `generalLinearRankCast T (rank_eq_top_of_pos hpos) ⋙ generalLinearDerivativePositive T ψ 0 (N - 1)`.

  All these statements are equalities of functors, so they include the action
  on morphisms. No objectwise isomorphism-class statement stands in for them.

No convention or claim is made for `k > N`. The wrapper takes `hk : k ≤ N`.

## Normalization limitation

The source functors use the inverse-half Haar-modulus normalization of §1.8.
The Library functors composed here use explicit determinant twists:
`Mirabolic.psiMinus T n` twists by `|det|^(-1/2)` on `GL_n` and
`Mirabolic.phiMinus T ψ m` twists by `|det|^(-1/2)` on `P_(m+1) ⊂ GL_(m+1)`.
Here `|·|` is `T.determinantNorm`, the residue-normalized absolute value of
the determinant. The derivatives here therefore have, at each step, exactly
these determinant-normalized twists, and the restriction step has no twist.
This module does not prove that the Haar automorphism modulus equals the
determinant norm. That comparison is a separate proof obligation, and no
source citation here is claimed to supply it.

## What the source supplies and what is internal

The source supplies the composite `Ψ⁻ ∘ (Φ⁻)^(k-1)`, the rank drop at each
step, the zeroth derivative `π^(0) = π`, and restriction to `P_n` before the
mirabolic derivative. The following are internal Lean packaging:

- the indexing of the iterate and the mirabolic and positive derivatives by
  the target rank `n` and the number `k` of `Φ⁻` steps;
- the rank transport `generalLinearRankCast` and the rank equalities;
- the wrapper indexed by `(N, k, hk)`, with its match on `k`;
- the extra cast `Nat.sub_self N` in the top equations;
- the functor equalities about identity, composition, objects and maps, which
  are elementary consequences of the definitions.

## Imports and independence

The module imports only `Langlands.Representation.Derivative.MirabolicMinus`.
The transitive `Langlands` import closure is 50 modules: that module and its
49 modules on groups, local fields, smooth representations, twists,
localization and Whittaker characters. It contains no classification,
segment, multisegment, square-integrable, tempered or socle module. Neither
the module nor its closure uses `SegmentHeadProductIrreducibility`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
or any result of the excluded exhaustion, existence, coverage, conversion,
uniqueness or segment-classification tasks. No exactness or other
representation-theoretic property is assumed as an input.
