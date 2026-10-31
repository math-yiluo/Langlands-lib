# The sheafified alternating Čech complex of an ordered affine cover

Author: Worker 958.

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.Complex`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution`. It builds, for an ordered affine cover
`𝒰 : X.OrderedAffineCover` of a scheme `X : Scheme.{u}` and an `𝒪_X`-module `M`, the
`ℕ`-indexed cochain complex of `𝒪_X`-modules

```
C⁰ ⟶ C¹ ⟶ C² ⟶ ⋯,    Cᵖ = ⨁_{s} (j_{𝒰.inter s})_* (M|_{𝒰.inter s}),
```

where `s` runs over the strictly increasing tuples `Fin (p + 1) → 𝒰.ι`, together with its
augmentation `M ⟶ C⁰`. Its sections over an open `V` are the alternating Čech cochains of `M`
for the cover `𝒰.U i ⊓ V` of `V`; over `V = ⊤` they are the cochains
`OModulePresheaf.cochain` of the Anthropic FLT port, with the same differential
`OModulePresheaf.d` (the comparison is not part of this module).

## Imported interface

The cover structure comes from the port of the Anthropic FLT file
`Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean`, module
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`
(namespace `AlgebraicGeometry.Scheme.OrderedAffineCover`). This module uses its declarations
unchanged:

- `𝒰.ι : Type u` with `Fintype` and `LinearOrder` instances, the affine opens `𝒰.U i`
  (`𝒰.isAffineOpen`), and `𝒰.iSup_eq_top : ⨆ i, 𝒰.U i = ⊤`;
- `𝒰.Idx p := {s : Fin (p + 1) → 𝒰.ι // StrictMono s}` (finite, with decidable equality);
- `𝒰.inter s := ⨅ j, 𝒰.U (s.1 j)`;
- `𝒰.face t j : 𝒰.Idx p` for `t : 𝒰.Idx (p + 1)` and `j : Fin (p + 2)`, the tuple
  `t.1 ∘ Fin.succAbove j` (omit the `j`-th entry), with `𝒰.face_val` and
  `𝒰.inter_le_inter_face t j : 𝒰.inter t ≤ 𝒰.inter (𝒰.face t j)`.

The ported module is imported from the Library; no local copy is used.

## Declarations

With `𝒰 : X.OrderedAffineCover` and `M : X.Modules`:

- `cechTerm 𝒰 M p : X.Modules` (an `abbrev`) is the biproduct
  `⨁ fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)` (`sheafOn` from
  `Langlands.AlgebraicGeometry.Modules.CechResolution.Basic`).
- `cechD 𝒰 M p : cechTerm 𝒰 M p ⟶ cechTerm 𝒰 M (p + 1)` is `biproduct.lift` of the family
  whose component at `t : 𝒰.Idx (p + 1)` is
  `∑ j : Fin (p + 2), (-1)^j • (biproduct.π _ (𝒰.face t j) ≫ res M (𝒰.inter_le_inter_face t j))`.
  `cechD_π` records this component. On sections this is the alternating Čech differential
  `(d c)_t = ∑_j (-1)^j c_{face t j}|`, the formula of `OModulePresheaf.d_apply`.
- `π_res_congr`: the composite `biproduct.π _ t ≫ res M hW` depends only on `t` up to equality
  (used to compare components indexed by equal tuples).
- `succAbove_comp_succAbove h : Fin.succAbove j.succ ∘ Fin.succAbove i =
  Fin.succAbove i.castSucc ∘ Fin.succAbove j` for `i ≤ j` (the simplicial identity for face
  maps).
- `cechD_comp_cechD 𝒰 M p : cechD 𝒰 M p ≫ cechD 𝒰 M (p + 1) = 0`. Proof: after expanding both
  differentials and composing restrictions (`res_comp`), the double sum over pairs
  `(a, b) ∈ Fin (p + 3) × Fin (p + 2)` splits into the pairs with `a ≤ b` and the others;
  `(a, b) ↦ (b + 1, a)` is a bijection between the two parts (`Finset.sum_bij`) under which
  the faces agree (`succAbove_comp_succAbove`) and the signs `(-1)^(a+b)` and
  `(-1)^(b+1+a)` are opposite.
- `cechComplex 𝒰 M : CochainComplex X.Modules ℕ` is `CochainComplex.of (cechTerm 𝒰 M)
  (cechD 𝒰 M) (cechD_comp_cechD 𝒰 M)`.
- `augmentation 𝒰 M : M ⟶ cechTerm 𝒰 M 0` is `biproduct.lift fun s => unit M (𝒰.inter s)`;
  `augmentation_π` records its components. `augmentation_cechD 𝒰 M :
  augmentation 𝒰 M ≫ cechD 𝒰 M 0 = 0` follows from `unit_res`: both face terms of a pair
  `t : 𝒰.Idx 1` are the unit `M ⟶ sheafOn M (𝒰.inter t)`, with opposite signs.
- `cechAug 𝒰 M : (CochainComplex.single₀ X.Modules).obj M ⟶ cechComplex 𝒰 M` is the
  morphism of complexes corresponding to `augmentation 𝒰 M` under
  `CochainComplex.fromSingle₀Equiv`.
- `augSc 𝒰 M` is the short complex `M ⟶ C⁰ ⟶ C¹` (maps `augmentation`, `cechD 𝒰 M 0`), and
  `cechSc 𝒰 M n` is the short complex `Cⁿ ⟶ Cⁿ⁺¹ ⟶ Cⁿ⁺²` (maps `cechD 𝒰 M n`,
  `cechD 𝒰 M (n + 1)`).
- `quasiIso_cechAug_of_exact 𝒰 M hmono h0 hn : QuasiIso (cechAug 𝒰 M)` given
  `hmono : Mono (augmentation 𝒰 M)`, `h0 : (augSc 𝒰 M).Exact` and
  `hn : ∀ n, (cechSc 𝒰 M n).Exact`. Proof: in degree `0`,
  `CochainComplex.quasiIsoAt₀_iff` and `ShortComplex.quasiIso_iff_of_zeros` reduce the claim
  to exactness of `M ⟶ C⁰ ⟶ C¹` together with `Mono (augmentation 𝒰 M)`, transported along
  the evident isomorphism of short complexes. In degree `n + 1` the source complex is exact
  (`CochainComplex.exactAt_succ_single_obj`), so `quasiIsoAt_iff_exactAt` reduces the claim
  to exactness of `cechComplex 𝒰 M` at `n + 1`, which is `hn n` up to the isomorphism of
  short complexes given by `HomologicalComplex.exactAt_iff'`. The hypotheses are discharged
  in `Langlands.AlgebraicGeometry.Modules.CechResolution.Exact`.

## Provenance

The complex is the complex `𝔆^•(𝒰, 𝓕)` of Stacks Project, Cohomology of Sheaves,
Lemma `lemma-covering-resolution` (tag 02FU), restricted to strictly increasing index
tuples of a finite totally ordered cover, which Stacks calls the ordered Čech complex
(Section `section-alternating-cech`, tag 01FG, "The alternating Čech complex"; the ordered
and alternating complexes are isomorphic there, and for strictly increasing tuples the FLT files use the name
"alternating"). Source: `cohomology.tex` of the registered folder
`stacks-flasque-affine-vanishing-kunneth-a04446e5` (Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`), Section 01FG from line 4071 and Lemma 02FU
from line 4571. The differential and the index conventions follow `OModulePresheaf.d` of the
Anthropic FLT source (registered as `anthropic-flt-complete-lean-source-6e837e75`); the
Lean construction and proofs here are this module's own.
