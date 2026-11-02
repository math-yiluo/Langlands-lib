# Proof: the real Deligne torus is a non-split torus

Authors: Worker 207 and Worker 293. Worker 207 wrote the Lean proof and the
first version of this Markdown; Worker 293 checked and corrected the Markdown
and submitted the proof.

`Langlands.Shimura.DeligneTorus.nonSplitTorusStatement` proves the published
proposition `Langlands.Shimura.DeligneTorus.NonSplitTorusStatement` from the
module `Langlands.Shimura.Unitary.DeligneNonSplitStatement`. That proposition is
the conjunction

```lean
Smooth groupScheme.X.hom ∧ GroupScheme.IsSplitTorus complexGroupScheme ∧
  ¬ GroupScheme.IsSplitTorus groupScheme
```

for the published real Deligne group scheme `groupScheme` over
`Spec (CommRingCat.of ℝ)` and its pullback `complexGroupScheme` along
`complexBaseMap : Spec ℂ ⟶ Spec ℝ`. The theorem has exactly this type and takes
no arguments or hypotheses. The proof uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Split over `ℂ`

The second conjunct is the published theorem `isSplitTorus_complexGroupScheme`
from `Langlands.Shimura.Unitary.DeligneSplitTorus`. Its isomorphism
`complexSplitTorusIso` identifies `complexGroupScheme` with
`splitTorus (Spec ℂ) (PUnit ⊕ PUnit)`, a split torus on a two-element index
type.

## Smoothness

- `complexBaseMap_fpqc` shows that `complexBaseMap` is surjective, flat and
  quasi-compact. Mathlib's `flat_and_surjective_SpecMap_iff` reduces flatness
  and surjectivity of `Spec.map` to faithful flatness of the ring map
  `algebraMap ℝ ℂ`. `RingHom.faithfullyFlat_algebraMap_iff` turns that into
  `Module.FaithfullyFlat ℝ ℂ`, which instance search supplies through
  Mathlib's `Module.FaithfullyFlat.of_isIntegral_of_isDomain`: `ℂ` is a
  domain that is flat, integral and faithful over `ℝ`. Quasi-compactness is
  also found by instance search: `complexBaseMap` is a morphism of affine
  schemes, hence an affine morphism, and affine morphisms are quasi-compact
  (`instQuasiCompactOfIsAffineHom`).
- `smooth_complexGroupScheme` gets smoothness of the complex pullback from the
  published lemma `IsSplitTorus.smooth` (Split tori are smooth:
  `Langlands.GroupScheme.Torus.Split`) applied to
  `isSplitTorus_complexGroupScheme`.
- `smooth_groupScheme` descends smoothness along `complexBaseMap`. It applies
  Mathlib's `MorphismProperty.of_pullback_snd_of_descendsAlong` with
  `P = Smooth` and `Q = Surjective ⊓ Flat ⊓ QuasiCompact`. Mathlib's
  `LocalFlatDescent` module provides the required instance that smoothness
  descends along such morphisms. The two remaining goals are
  `complexBaseMap_fpqc` and the smoothness of the pullback, which is
  `smooth_complexGroupScheme`. The second projection of the pullback here is,
  by definition, the structure morphism of `complexGroupScheme`.

## Not split over `ℝ`

`not_isSplitTorus_groupScheme` assumes an isomorphism
`e : groupScheme ≅ splitTorus (Spec ℝ) I` for some finite `I` and composes four
published multiplicative equivalences:

1. `realPointsEquiv.symm : ℂˣ ≃* Points ℝ` (module `Deligne`), where
   `Points ℝ` is the unit group of `QuadraticAlgebra ℝ (-1) 0`;
2. `(affinePointsEquiv (CommAlgCat.of ℝ ℝ)).symm` (module
   `DeligneGroupScheme`), from those units to the points of `groupScheme` on
   the affine test scheme `Spec ℝ`;
3. `GroupScheme.isoPointsEquiv e _` (module `Torus.Split`), transporting points
   along `e`;
4. `GroupScheme.splitTorus.affinePointsEquiv I` (module `Torus.Split`), from
   the `Spec ℝ`-points of `splitTorus (Spec ℝ) I` to `I → ℝˣ`.

The result is a group isomorphism `Φ : ℂˣ ≃* (I → ℝˣ)`. The two
arithmetic lemmas give the contradiction:

- `complex_I_unit_pow`: the unit `i` of `ℂ` satisfies `i ^ 4 = 1` and
  `i ^ 2 ≠ 1`. The second part holds because the real part of `i ^ 2 = -1` is
  `-1`, not `1`.
- `real_units_sq_eq_one_of_pow_four`: if `x : ℝˣ` and `x ^ 4 = 1`, then
  `x ^ 2 = 1`. Here `(x ^ 2) ^ 2 = 1` with `x ^ 2 ≥ 0`, so `x ^ 2 = 1` by
  Mathlib's `pow_eq_one_iff_of_nonneg`.

Every coordinate of `Φ i` has fourth power one, hence square one, so
`Φ (i ^ 2) = 1 = Φ 1`. Injectivity of `Φ` gives `i ^ 2 = 1`, a contradiction.

`nonSplitTorusStatement` is the conjunction of `smooth_groupScheme`,
`isSplitTorus_complexGroupScheme` and `not_isSplitTorus_groupScheme`.

## Provenance

The sources are those of the statement's Markdown: Milne, *Introduction to
Shimura varieties* (Clay Mathematics Proceedings 4, 2005), Section 2, printed
p.282 (source ID `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`), and
Milne, *Algebraic Groups* (2017), printed p.236: Definition 12.14 (split tori)
and, after Definition 12.17, the sentence that tori are the smooth connected
algebraic groups of multiplicative type (source ID
`milne-2017-algebraic-groups`). The sources do not contain this proof. Its
route is internal:

- smoothness by fpqc descent from the split complex form instead of a direct
  computation on the coordinate algebra;
- non-splitting by the order of `i` in the real points instead of the Galois
  action on characters.

The proof does not compute character lattices or a Galois action. Those are
separate results.
