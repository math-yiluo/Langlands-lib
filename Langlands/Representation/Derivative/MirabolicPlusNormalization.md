# Normalized mirabolic plus functors

Author: Worker 984.

This module constructs the normalized Bernstein–Zelevinsky plus functors
`Ψ⁺ : Alg GL_n → Alg P_(n+1)` and `Φ⁺ : Alg P_(n+1) → Alg P_(n+2)` on the
actual published smooth complex representations. Each functor first twists
the input by the canonical positive half of the actual radical Haar
character, which is the determinant real power `|det|^(1/2)`, and then
applies the published unnormalized functor of
`Langlands.Representation.Derivative.MirabolicPlus`. The module proves the
characters' Haar comparison and open kernels, the whole-functor
comparisons, and the elementary action, covariance, support, smoothness and
morphism laws. It constructs no adjunction, unit or counit, exactness,
submodule-lattice equivalence, Fourier detection, highest derivative,
pairing or irreducibility statement, and assumes none of them as data.

Its direct imports are `Langlands.Representation.Derivative.MirabolicPlus`
and `Langlands.Representation.Derivative.MirabolicMinusNormalization`. The
latter imports `Langlands.Group.GL.MirabolicModulusProof`. No existing
Library file is changed.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
source `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
PDF page is the printed page minus 439.

- §1.7, printed p.444/PDF5: for a closed subgroup `U` normalized by `g`,
  `mod_U(g)` is the module of the automorphism `u ↦ g u g⁻¹`, defined by
  `∫ f(σ⁻¹(u)) dμ(u) = mod_U(σ) · ∫ f(u) dμ(u)`.
- §1.8(a), printed p.444/PDF5: for closed `M`, `U` with `M` normalizing
  `U`, `M ∩ U = {e}`, closed `P = MU`, and a character `θ` of `U`
  normalized by `M`, the space `I(L)` consists of `f : G → L` with
  `f(umg) = θ(u) mod_U^(1/2)(m) ρ(m)(f(g))` and one open subgroup of
  right stabilizers; `G` acts by right translation. The compactly induced
  `i_(U,θ)(ρ)` is the subspace of functions compactly supported modulo
  `P`. The exponent is positive, `+1/2`. By contrast, the localization
  `r_(U,θ)` of §1.8(b) uses `mod_U^(-1/2)`; that is the normalization of
  the published minus functors.
- §1.8, last paragraph, printed p.445/PDF6: if `MU = G`, then
  `I_(U,θ)(ρ) = i_(U,θ)(ρ)` acts on the same space as `ρ`.
- §1.9, printed p.445/PDF6, lists properties of these functors. Its
  adjunction and exactness assertions are not used or stated here.
- §3.1, printed p.450/PDF11: `P_n` is the mirabolic subgroup of
  `G_n = GL(n, F)` (last row `(0, …, 0, 1)`), `V = V_n` is its unipotent
  radical, `G_(n-1)` normalizes `V`, `G_(n-1) ∩ V = {e}`,
  `G_(n-1) V = P_n`, and `θ(v) = ψ(v_(n-1,n))` for a nontrivial additive
  character `ψ`; `P_(n-1)` normalizes `θ`.
- §3.2, printed pp.450–451/PDF11–12: `Ψ⁺ = i_(V,1) : Alg G_(n-1) → Alg P_n`
  and `Φ⁺ = i_(V,θ) : Alg P_(n-1) → Alg P_n`. The source notes that these
  functors differ from those of its reference [1] (Bernstein–Zelevinsky
  1976) by twisting with `mod^(1/2)`. The published unnormalized functors
  follow [1].

The rest of §3.2 (exactness, adjunctions, vanishing composites and
adjunction isomorphisms) and Remark 3.3 are not stated here. No errata entry
for this source is registered in the literature index, and the Library has
no errata note for it.

### Correspondence

Fix the source's `θ` and positive exponent. In `Φ⁺`, `M = P_(n-1)`
(source indexing) and `MU = P_(n-1) V_n` is the published `plusSubgroup`.
Unfolding §1.8(a), a vector of `Φ⁺(τ)` is a function with

`f(u m x) = θ(u) mod_V(m)^(1/2) τ(m) f(x)`,

one open subgroup of right stabilizers, and support compact modulo
`P_(n-1) V_n`. The proved radical Haar comparison below gives
`mod_V(m)^(1/2) = |det m|^(1/2)`. Hence `Φ⁺(τ)` is the unnormalized
compact induction of [1] applied to the twist `|det|^(1/2) ⊗ τ`, which is
how this module defines it.

For `Ψ⁺` the subgroup `G_(n-1) V_n` is all of `P_n`, so the source functor
acts on the same space. A vector is determined by its value `f(e)`, and for
`g = u a` with `u ∈ V_n`, `a ∈ G_(n-1)`, right translation gives
`f(u a) = |det a|^(1/2) ρ(a) f(e)`. Thus `Ψ⁺(ρ)` is the inflation along the
projection `P_n → G_(n-1)` of `|det|^(1/2) ⊗ ρ`, which is how this module
defines it. This is an implementation of the source's identification "on
the same space", not a separate theorem of the source; the module uses the
published inflation `psiPlusUnnormalized` instead of a one-point function
space.

### Rank shift

`GeneralLinear.mirabolic n F.Carrier` is the source's `P_(n+1)`, and
`GeneralLinear.Mirabolic.radical n F.Carrier` is its `V_(n+1)`. Hence:

- `psiPlus T n` is the source's `Ψ⁺ : Alg G_n → Alg P_(n+1)` (source index
  `n + 1`), using the radical `V_(n+1)`;
- `phiPlus T ψ n` is the source's `Φ⁺ : Alg P_(n+1) → Alg P_(n+2)` (source
  index `n + 2`), using the radical `radical (n + 1) F.Carrier = V_(n+2)`
  of the larger group;
- `plusSubgroup n F.Carrier` is the source's `P_(n+1) V_(n+2)`.

Every `n : ℕ` is allowed, including `n = 0`, with no special case. At
`n = 0`, `Ψ⁺` goes from `GL_0` to the trivial group `P_1`, `Φ⁺` goes from
`P_1` to `P_2`, and `plusSubgroup 0 F.Carrier` is the radical `V_2`
(published `plusSubgroup_zero`). The definitions need no case split.

## Parameters, topology and universes

Throughout, `p : ℕ` is prime (`[Fact p.Prime]`), `F : PadicField.{uF} p`,
and `T : F.TopologicalData` is an arbitrary supplied topological
realization. Every topological statement installs `letI := T.topology`;
compact-induction statements also install
`letI := T.generalLinearTopologicalGroup (n + 1 + 1)`, exactly as the
unnormalized module does. The Haar half characters additionally use the
supplied `T.fieldT2`, `T.generalLinearTopologicalGroup` and
`T.generalLinearLocallyCompactSpace`, and the published local compactness
of the mirabolic group. No canonical topology is substituted. The additive
character is `ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`,
whose type bundles continuity and nontriviality; the proofs here do not use
nontriviality explicitly.

The coefficient universe of `SmoothRep` is `0` (complex coefficients), the
group universe is `uF`, and the input carrier universe `uV` is an
independent universe parameter. The inspected complete types are:

```lean
psiPlusCharacter : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  F.TopologicalData → (n : ℕ) → GeneralLinear n F.Carrier →* ℂˣ
phiPlusCharacter : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  F.TopologicalData → (n : ℕ) → mirabolic n F.Carrier →* ℂˣ
psiPlus.{uV, uF} : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  (T : F.TopologicalData) → (n : ℕ) →
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)
phiPlus.{uV, uF} : {p : ℕ} → [Fact p.Prime] → {F : PadicField.{uF} p} →
  (T : F.TopologicalData) → UnitaryAdditiveCharacter F.Carrier → (n : ℕ) →
  SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
    SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier)
```

The level parameters of `psiPlus` and `phiPlus` are exactly `uV, uF`. The
output carrier universe `max uF uV` of `Φ⁺` is the universe of the actual
function space `Induction.CompactFunctions`; it is not resized, identified
with `uV`, or simplified by an assumption `uF ≤ uV`. Later adjunction or
pairing statements comparing `Φ⁺` with `Φ⁻` must handle this universe
difference explicitly.

All main declarations depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Positive-half characters

- `psiPlusCharacter T n : GeneralLinear n F.Carrier →* ℂˣ` is
  `realPowerCharacter (T.determinantNorm n) (1 / 2 : ℝ)`, that is,
  `g ↦ |det g|^(1/2)` for the supplied determinant norm.
- `phiPlusCharacter T n : mirabolic n F.Carrier →* ℂˣ` is
  `realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype) (1 / 2 : ℝ)`,
  the rank-`(n + 1)` determinant norm restricted to `P_(n+1)`.

Both are `abbrev`s, mirroring the published `psiMinusCharacter` and
`phiMinusCharacter`, which are the same real powers with exponent
`-(1 / 2)`. The laws are:

- `isOpen_ker_psiPlusCharacter` and `isOpen_ker_phiPlusCharacter`: open
  kernels under `T.topology`, from the published open kernel of the
  determinant norm (pulled back along the continuous subtype inclusion for
  `Φ`) and `isOpen_ker_realPowerCharacter`;
- `psiPlusCharacter_eq_inv`: `psiPlusCharacter T n = (psiMinusCharacter T n)⁻¹`,
  and `phiPlusCharacter_eq_inv`, the analogue for `Φ`, both from
  `realPowerCharacter_neg` and `inv_inv`;
- `psiPlusCharacter_mul_psiMinusCharacter` and
  `phiPlusCharacter_mul_phiMinusCharacter`: the product of the plus and
  minus characters is `1`.

## The actual radical Haar comparison

The generic identity `Jacquet.complexPositiveHalfCharacter_comp`, for
arbitrary groups `G : Type uG`, `H : Type uH`, a positive character
`δ : G →* ℝ≥0ˣ` and `φ : H →* G`, states that the complex embedding of the
canonical positive square root of `δ` commutes with pullback along `φ`. It
is definitional (`rfl`); it is the positive analogue of the published
`Jacquet.inverseHalfCharacter_comp`.

The module defines the actual Haar half characters:

- `psiPlusHaarHalf T n : GeneralLinear n F.Carrier →* ℂˣ` is the published
  `HaarModulus.closedHalfCharacter` of the closed radical
  `radical n F.Carrier` of `P_(n+1)`, restricted to the standard Levi
  subgroup `leviSubgroup n F.Carrier` and pulled back to `GL_n` by
  `leviEquiv`;
- `phiPlusHaarHalf T n : mirabolic n F.Carrier →* ℂˣ` is the
  `closedHalfCharacter` of the closed radical `radical (n + 1) F.Carrier`
  of `P_(n+2)`, restricted to `successorSubgroup n F.Carrier` and pulled
  back to `P_(n+1)` by `successorEquiv`.

`HaarModulus.closedHalfCharacter` is
`Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ)` for the actual
restricted normalizer Haar character `δ = closedRestrictCharacter …`, whose
value at `g` is Mathlib's Haar character of `u ↦ g u g⁻¹`. Its Markdown
identifies this with the convention of §1.7, so `δ` is the source's
`mod_U` and the half character is the canonical positive `mod_U^(1/2)`.

`psiPlusHaarHalf_eq` and `phiPlusHaarHalf_eq` prove
`psiPlusHaarHalf T n = psiPlusCharacter T n` and
`phiPlusHaarHalf T n = phiPlusCharacter T n`. Each proof unfolds the
closed wrapper by `change`, moves the pullback inside the positive half
with `Jacquet.complexPositiveHalfCharacter_comp`, rewrites the pulled-back
Haar character with the published proved theorem
`GeneralLinear.Mirabolic.leviRadical_haarCharacter` (respectively
`successorRadical_haarCharacter`) from
`Langlands.Group.GL.MirabolicModulusProof`, and applies the published
`Jacquet.positiveHalfCharacter_eq_realPowerCharacter`. The Haar character
is never identified with a determinant by definition: the determinant
appears only through the proved radical Haar theorems, which compute the
actual Haar character by coordinate transport and scalar/matrix Haar
scaling.

`psiPlusHaarHalf_eq_inv` and `phiPlusHaarHalf_eq_inv` show that the
positive halves are the inverses of the published
`psiMinusHaarInverseHalf T n` and `phiMinusHaarInverseHalf T n`, combining
the comparisons above with the published `psiMinusHaarInverseHalf_eq`,
`phiMinusHaarInverseHalf_eq` and the character inverse laws.
`isOpen_ker_psiPlusHaarHalf` and `isOpen_ker_phiPlusHaarHalf` transport the
open-kernel certificates through the comparisons.

## Normalized Ψ⁺

`psiPlus T n` is defined as

```lean
SmoothRep.twistFunctor (psiPlusCharacter T n) (isOpen_ker_psiPlusCharacter T n) ⋙
  psiPlusUnnormalized T n
```

`psiPlus_eq` states this whole-functor equality (`rfl`).
`psiPlus_haarNormalization` states that `psiPlus T n` equals the same
composite with `psiPlusHaarHalf T n` and its open-kernel witness; the proof
rewrites by `psiPlusHaarHalf_eq`, and proof irrelevance identifies the
witnesses. `psiPlus_eq_unnormalized_twist` states the equivalent order
`psiPlusUnnormalized T n ⋙ SmoothRep.twistFunctor ((psiPlusCharacter T n).comp projection) _`
(`rfl`). These are equalities of functors, so they include maps.

Its laws, for all `A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)`:

- `psiPlus_obj_carrier`: the carrier of `(psiPlus T n).obj A` is the
  carrier of `A` (`rfl`);
- `psiPlus_obj_representation`: the action is
  `(Langlands.twist (psiPlusCharacter T n) A.representation).comp projection`;
- `psiPlus_action`:
  `Ψ⁺(ρ)(g) v = (psiPlusCharacter T n (projection g) : ℂ) • ρ(projection g) v`;
- `psiPlus_radical`: every element of `radical n F.Carrier` acts trivially,
  since its projection is `1` (published `projection_eq_one_iff`);
- `psiPlus_levi`: `Ψ⁺(ρ)(levi a) = |det a|^(1/2) • ρ(a)` (published
  `projection_levi`);
- `psiPlus_radicalElement_mul_levi`: in the published radical-first
  coordinates, `Ψ⁺(ρ)((radicalElement v).val * levi a) = |det a|^(1/2) • ρ(a)`
  (published `projection_radicalElement_mul_levi`); this is the source
  formula `f(u a) = mod_V(a)^(1/2) ρ(a) f(e)` above;
- `psiPlus_isSmooth`: output objects are smooth;
- `psiPlus_map_apply`: the image of `f` has the same underlying linear map
  as `f` (`rfl`);
- `psiPlus_map_equivariant`, `psiPlus_map_id` and `psiPlus_map_comp`.

## Normalized Φ⁺

`phiPlus T ψ n` is defined as

```lean
SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
  phiPlusUnnormalized T ψ n
```

`phiPlus_eq` states this whole-functor equality (`rfl`), and
`phiPlus_haarNormalization` the equality with the composite using
`phiPlusHaarHalf T n`, as for `Ψ⁺`.

### Carrier

For `τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)`, write
`τ'' = plusTwistRepresentation ψ n (Langlands.twist (phiPlusCharacter T n) τ.representation)`,
the published plus-subgroup representation of the positively normalized
inducing representation.

- `phiPlus_obj_carrier`: the carrier of `(phiPlus T ψ n).obj τ` is
  `Induction.CompactFunctions (plusSubgroup n F.Carrier) τ''`, in
  `Type (max uF uV)` (`rfl`);
- `phiPlus_obj`: the object is
  `SmoothRep.of (Induction.compactInduced Q τ'') (Induction.compactInduced_smooth Q τ'')`
  with `Q = plusSubgroup n F.Carrier` (`rfl`);
- `phiPlus_obj_representation`: the action of `g` on `φ` is
  `Induction.compactInduced Q τ'' g φ`, stated pointwise as in the
  unnormalized module (`rfl`).

These are the published actual compact functions: covariant functions with
one open subgroup of right stabilizers and compact projected nonzero
support in `Q \ P_(n+2)`, acted on by right translation. No second compact
induction is implemented.

### Evaluation interface

`phiPlusNormalizedEval T ψ n τ φ x : τ` is the value at
`x : mirabolic (n + 1) F.Carrier` of `φ : (phiPlus T ψ n).obj τ`. It is
the published `phiPlusEval` for the twisted input
`(SmoothRep.twistFunctor (phiPlusCharacter T n) _).obj τ`, whose carrier is
that of `τ`; `phiPlusNormalizedEval_eq` records this (`rfl`). Its laws
reuse the corresponding published `phiPlusEval_*` lemmas:

- `phiPlusNormalizedEval_injective`: vectors are determined by their
  values;
- `phiPlusNormalizedEval_covariant`: for `q ∈ Q`,
  `φ(q x) = (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) • τ(plusProjection q)(φ x)`,
  the source covariance with `mod_V^(1/2) = |det|^(1/2)`;
- `phiPlusNormalizedEval_successor_mul_radical`: in the Levi-first
  coordinates of the unnormalized module,
  `φ(successor g * u * x) = Θ(u) • |det g|^(1/2) • τ(g)(φ x)` for
  `g ∈ P_(n+1)` and `u ∈ radical (n + 1)`. The general covariance above
  covers every element of `Q`, in particular the radical-first products
  `u m` of §1.8(a), since `thetaPlus` and `plusProjection` are
  homomorphisms on `Q`;
- `phiPlusNormalizedEval_radical_mul`: `φ(u x) = Θ(u) • φ(x)`;
- `phiPlusNormalizedEval_successor_mul`:
  `φ(successor g * x) = |det g|^(1/2) • τ(g)(φ x)`;
- `phiPlusNormalizedEval_isCompact_quotientSupport`: the projected nonzero
  support in `Q \ P_(n+2)` is compact;
- `phiPlusNormalizedEval_exists_openSubgroup`: one open subgroup `K` of
  `mirabolic (n + 1)` with `φ(x k) = φ(x)` for all `k ∈ K` and all `x`;
- `phiPlusNormalizedMk T ψ n τ f hcov K hK hc` builds a vector from a
  function with the normalized covariance `hcov`, one open subgroup `K` of
  right stabilizers and compact projected support, using the published
  `phiPlusMk`; `phiPlusNormalizedEval_mk` says its values are `f` (`rfl`).

Here `Θ(u) = theta ψ n u` is the published radical character, which
`thetaPlus` extends to `Q`.

### Action, smoothness and functoriality

- `phiPlus_action`: right translation,
  `phiPlusNormalizedEval (g • φ) x = phiPlusNormalizedEval φ (x * g)` (`rfl`);
- `phiPlus_isSmooth`: output objects are smooth;
- `phiPlus_map_hom`: the image of `f : τ ⟶ σ` is
  `Induction.compactInducedMap Q` of the underlying intertwiner of
  `(plusTwistFunctor T ψ n).map ((SmoothRep.twistFunctor (phiPlusCharacter T n) _).map f)`,
  whose linear map is that of `f` (`rfl`);
- `phiPlus_map_eval`: on values the image is postcomposition by the
  original morphism, `(Φ⁺ f)(φ)(x) = f(φ x)` (`rfl`);
- `phiPlus_map_equivariant`, `phiPlus_map_id` and `phiPlus_map_comp`.

## Provenance

The normalized functors are the source's definitions, implemented as the
published unnormalized functors (which follow [1]) after the source's
`mod^(1/2)` twist; the correspondence above derives this from §1.8(a). The
characters, Haar comparisons and laws are internal derivations from the
cited Library constructions, the proved radical Haar theorems, and Mathlib.
The module asserts no further original-literature theorem. The modular
function of the full mirabolic group is not used.

## Import and dependency audit

The recursive `Langlands` import closure of this module at Library base
`c59c0940bd7d47ad634dc767445532ca1108111f` consists of 65 modules. All
are published and paired, and their Lean and Markdown bytes in the
authoring workspace match that tree and the later Library commit
`2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11`, so the closure is unchanged
there. They are the `GL`, mirabolic and
radical-Haar group modules; the harmonic-analysis modules (additive
characters and p-adic Haar scaling); local-field, topology and
nonarchimedean-subgroup modules; and the smooth, twist, real-power,
matrix-coefficient, dual, admissibility, Whittaker, Jacquet
coinvariant/localization/positive-character, induction and category
representation modules. The only derivative modules are
`MirabolicCharacter`, `MirabolicMinus`, `MirabolicMinusNormalization` and
`MirabolicPlus`, all actual constructions and character adapters.

The closure contains no classification, segment, multisegment, socle, head,
Jacquet-formula, square-integrability, tempered, exhaustion, product
irreducibility, detection, highest-derivative or pairing module. Hence
neither this module nor any import depends on the tasks listed in the
Independence restrictions of task `562456a0-6ff7-4895-a1e5-fcf99f122ff8`
(including `67279e36…`, `4ca79bbd…`, `aca8805b…`, `5eece9e8…`,
`3bfb61fa…`, `ebea9a8a…`, `20e4e1c6…`, `8252833d…`, `52e97845…`,
`1cb45da2…`, `cd8ab97c…`, `bf433f0a…`, `8364e73f…`, `30341ae4…`,
`23189526…`, `f3a69bc8…`, `2ae5cbe5…`, `e3634665…`, `ed48ae06…`,
`55ad1e10…`, `b95105c6…` and `92aea10f…`), their conclusions or
consequences. It does not depend on the consumers `3c9849a4…` and
`a925b519…`, the `TwoSupercuspidalProductStructure` conclusion, parent
task `ab61f565…`, the segment-socle part of `8e5b4563…`, or the paused
minus-exactness proof `b65bc667…`. It uses no Zelevinsky 1980 result
(neither the segment derivative formulas of §3.5/§9.6, nor 4.2, 9.3 or
9.7), and no BZ77 derivative theorem (3.2–3.8): only the §1.8 and §3.2
definitions are implemented. No derivative result, exactness, adjunction
or classification theorem is assumed, and no theorem-valued premise is
added. The proofs use no `sorry`, `admit` or new axiom. This closure
inventory is an author audit, not independent acceptance evidence.
