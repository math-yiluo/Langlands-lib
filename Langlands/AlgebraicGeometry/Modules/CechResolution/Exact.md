# Exactness of the sheafified Čech complex

Author: Worker 958.

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.Exact`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution`. It proves that for every ordered affine
cover `𝒰 : X.OrderedAffineCover` of a scheme `X : Scheme.{u}` and every `𝒪_X`-module `M`
(no quasi-coherence or other hypothesis) the augmented sheafified alternating Čech complex

```
0 ⟶ M ⟶ C⁰ ⟶ C¹ ⟶ C² ⟶ ⋯
```

of `Langlands.AlgebraicGeometry.Modules.CechResolution.Complex` is exact. The main result is

```lean
theorem quasiIso_cechAug : QuasiIso (cechAug 𝒰 M)
```

that is, `cechComplex 𝒰 M` is a resolution of `M`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`. Affineness of the cover opens is not used here.

## Combinatorics of strictly increasing tuples

For a linearly ordered type `ι`, a tuple `s : Fin n → ι` and `k : ι`:

- `pos s k` is the number `#{i | s i < k}`; `pos_le`, `lt_pos_iff` (for monotone `s`,
  `i < pos s k ↔ s i < k`), and `pos_eq` (characterisation of `pos s k` by this property).
- `val_succAbove a i` computes `(a.succAbove i : ℕ)` as `i` if `i < a` and `i + 1` otherwise.

For `𝒰 : X.OrderedAffineCover` (index tuples `𝒰.Idx p`, faces `𝒰.face t j`):

- `idx_ext_range`: strictly increasing tuples with the same range are equal;
  `range_face`: the range of `𝒰.face t j` is the range of `t` minus `t j`.
- `insPos 𝒰 s k : Fin (p + 2)` is the insertion position `pos s.1 k`, and
  `insIdx 𝒰 s k hk : 𝒰.Idx (p + 1)` for `k ∉ Set.range s.1` is the strictly increasing tuple
  `Fin.insertNth (insPos 𝒰 s k) k s.1` (the set `s ∪ {k}`).
- `insIdx_apply_succAbove`, `range_insIdx` (range `insert k (range s)`), `face_insIdx`
  (omitting the inserted entry gives back `s`), `notMem_range_face`,
  `face_insIdx_succAbove` (omitting another entry commutes with inserting `k`),
  `self_notMem_range_face`, `self_mem_range_face`, `insIdx_face_self` (re-inserting the
  omitted entry `t m` into `𝒰.face t m` gives `t`), `pos_face_self`
  (`pos (𝒰.face t m).1 (t.1 m) = m`), `pos_face`, and the sign identity
  `sign_face : j + pos (𝒰.face t j).1 k + 1 = pos t.1 k + (insPos 𝒰 t k).succAbove j`.
- `single i : 𝒰.Idx 0` is the one-entry tuple `(i)`; `idx_zero_eq_single` and
  `face_insIdx_zero`.

## Families of sections over an open

With `M : X.Modules` and an open `W`:

- `cechOpen 𝒰 s W` (an `abbrev`) is `(𝒰.inter s).ι ''ᵁ ((𝒰.inter s).ι ⁻¹ᵁ W)`, which equals
  `𝒰.inter s ⊓ W` (`cechOpen_eq`); `cechOpen_le_of_range`: if `W ≤ 𝒰.U k` and
  `range s' ⊆ insert k (range s)` then `cechOpen 𝒰 s W ≤ cechOpen 𝒰 s' W`.
- `Sec 𝒰 M p W := ∀ s : 𝒰.Idx p, Γ(M, cechOpen 𝒰 s W)`, the alternating Čech `p`-cochains of
  `M` for the cover `{𝒰.U i ⊓ W}` of `W`.
- `cr c s h` is the restriction of the component `c s` to an open `W' ≤ cechOpen 𝒰 s W`, with
  `cr_def`, `cr_congr`, `map_cr` (restricting further) and `cr_self`.
- `dSec c : Sec 𝒰 M (p + 1) W` is the alternating differential
  `(dSec c) t = ∑ j, (-1)^j • (c (𝒰.face t j))|`, and `aug0 m : Sec 𝒰 M 0 W` restricts
  `m : Γ(M, W)` to every `𝒰.U i ⊓ W`.

## The contracting homotopy over `W ≤ 𝒰.U k`

Fix `k : 𝒰.ι` and `hW : W ≤ 𝒰.U k`.

- `contr k hW c : Sec 𝒰 M p W` for `c : Sec 𝒰 M (p + 1) W` is
  `(contr k hW c) s = 0` if `k` is an entry of `s`, and otherwise
  `(contr k hW c) s = (-1)^(pos s.1 k) • (c (insIdx 𝒰 s k hk))|`, the restriction being along
  `cechOpen_le_insIdx` (here `W ≤ 𝒰.U k` is used); `contr_of_mem`, `contr_of_notMem`.
- `cocycle_insIdx`: if `dSec c = 0` and `k ∉ range t`, the cocycle condition at `insIdx t k`,
  restricted to `cechOpen 𝒰 t W` and split at the face `insPos 𝒰 t k` (which gives `c t`),
  reads `(-1)^(pos t.1 k) • c t + ∑ j, (-1)^((insPos 𝒰 t k).succAbove j) • (c (face …))| = 0`.
- `dSec_contr k hW c hc : dSec (contr k hW c) = c` for every cocycle
  `c : Sec 𝒰 M (p + 1) W` (`hc : dSec c = 0`): exactness in positive degrees. Proof, at a
  tuple `t`: if `k = t m`, only the face `j = m` avoids `k`, and its term is
  `(-1)^m (-1)^(pos (face t m) k) c t = c t` by `pos_face_self` and `insIdx_face_self`; if
  `k ∉ t`, every face term is `(-1)^(j + pos (face t j) k) c (face (insIdx t k) (succAbove j))`
  (`face_insIdx_succAbove`), and `cocycle_insIdx` together with `sign_face` identifies the
  sum with `c t`.
- `aug0_cr_single k hW c hc : aug0 (cr c (single k) _) = c` for every `c : Sec 𝒰 M 0 W` with
  `dSec c = 0`: exactness in degree `0`, using the cocycle condition on the pair `{s 0, k}`.
- Helpers: `sign_mul_self` (`(-1)^n * (-1)^n = 1`) and `eq_of_sign_add_eq_one`.

## Passage to the sheaf complex

- `exists_mem_U 𝒰 x`: every point lies in some `𝒰.U k` (from `𝒰.iSup_eq_top`).
- `app_map_apply`: naturality of a morphism of `𝒪_X`-modules on a section.
- `toSec M W : Γ(cechTerm 𝒰 M p, W) → Sec 𝒰 M p W` takes the biproduct components; it is
  bijective (`toSec_injective`, `toSec_surjective`, from the biproduct lemmas of `Basic`),
  `toSec_zero`, and it intertwines the differentials and the augmentation:
  `toSec_cechD : toSec M W ((cechD 𝒰 M p).app W x) = dSec (toSec M W x)` and
  `toSec_augmentation : toSec M W ((augmentation 𝒰 M).app W m) = aug0 m`.
- `mono_augmentation M : Mono (augmentation 𝒰 M)`: sections of `M` over `V` with equal
  restrictions to all `𝒰.U i ⊓ V` are equal, by the sheaf axiom
  (`TopCat.Sheaf.eq_of_locally_eq'`), since these opens cover `V`.
- `cechD_locally_exact` and `augmentation_locally_exact`: over `W ≤ 𝒰.U k`, every section of
  `Cⁿ⁺¹` (respectively `C⁰`) killed by the differential is the image of a section of `Cⁿ`
  (respectively `M`) over `W`, by `dSec_contr` (respectively `aug0_cr_single`) through `toSec`.
- `exact_cechSc M n : (cechSc 𝒰 M n).Exact` and `exact_augSc M : (augSc 𝒰 M).Exact`, from
  `exact_of_locally` of `Basic`: a point `x ∈ V` lies in some `𝒰.U k`, and the previous lemma
  applies over `V ⊓ 𝒰.U k` to the restricted section.
- `quasiIso_cechAug 𝒰 M : QuasiIso (cechAug 𝒰 M)` is `quasiIso_cechAug_of_exact` of `Complex`
  applied to `mono_augmentation`, `exact_augSc` and `exact_cechSc`.

## Provenance

This is Stacks Project, Cohomology of Sheaves, Lemma `lemma-covering-resolution` (tag 02FU)
for the complex on strictly increasing index tuples. The Stacks proof checks exactness on
stalks with the homotopy `h(s)_{i_0 … i_{p-1}} = s_{i_fix i_0 … i_{p-1}}` for the full Čech
complex; the Lean proof works with sections over the opens `V ⊓ 𝒰.U k` instead of stalks and
uses the homotopy of the second proof of Lemma `lemma-alternating-cech-trivial` (tag 0G6T)
for the complex on strictly increasing tuples (`h(s)_{i_0 … i_p} = 0` if the fixed index
occurs among the `i_j`, and otherwise `±` the component at the tuple with the fixed index
inserted). Only the identity `d h c = c` for cocycles `c` is proved, which is what exactness
needs; the sign `(-1)^(pos s k)` is chosen so that it holds without a sign change. Source:
`cohomology.tex` of the registered folder `stacks-flasque-affine-vanishing-kunneth-a04446e5`
(Stacks commit `a04446e57ec1fbc252a871afcec7752fb2807b14`), Lemma 0G6T from line 4455 and
Lemma 02FU from line 4571. The Lean proofs are this module's own.
