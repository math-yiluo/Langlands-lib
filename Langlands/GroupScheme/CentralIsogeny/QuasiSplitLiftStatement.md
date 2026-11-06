# Statement: quasi-splitness lifts along central isogenies

Author: Worker 1534.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.CentralIsogenyQuasiSplitLiftStatement.{u}`, a
`Prop`-valued `def` with one universe parameter `u`. It is a prerequisite of the
conditional infinite-field Steinberg reduction in
`Rational/QuasiSplitCocycleTorusReductionInfinite.lean`. There it shows that the
simply connected cover of a quasi-split semisimple group is quasi-split, as
Steinberg 1.7 requires.

## Lean statement

```lean
def CentralIsogenyQuasiSplitLiftStatement : Prop :=
  ∀ (K : Type u) [Field K] (G A : GroupScheme (Spec (CommRingCat.of K))) (π : G ⟶ A),
    IsCentralIsogeny π → IsConnectedReductive G → IsQuasiSplit A → IsQuasiSplit G
```

The module imports `CentralIsogeny.Basic` and `Reductive.QuasiSplit`.

## Meaning

- `K` is an arbitrary field, with no perfectness hypothesis. `π : G ⟶ A` is a
  central isogeny of group schemes over `Spec K` (`IsCentralIsogeny`: finite,
  flat, surjective, locally of finite presentation, with central
  scheme-theoretic kernel). The kernel may be nonreduced, for example `μ_p` in
  characteristic `p`.
- `G` is connected reductive (`IsConnectedReductive`, module
  `Reductive/Basic`).
- `IsQuasiSplit` (module `Reductive/QuasiSplit`) asks for connected
  reductivity together with a closed `K`-subgroup `i : B ⟶ G` that is a Borel
  subgroup over `K` and whose base change to `K̄` is a Borel subgroup
  (`IsGeometricBorelSubgroup`).

So the proposition says: if the target of a central isogeny from a connected
reductive group has a `K`-Borel subgroup, so does the source.

## Sources and provenance

Provenance: derived.

- J. S. Milne, *Algebraic Groups* (2017), source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  - 17.67 (printed p.375, PDF p.391): "A connected group variety containing a
    Borel subgroup is said to be quasi-split."
  - Proposition 17.54(a) (printed pp.369–370, PDF pp.385–386): for a quotient
    map `φ : G → G'` of connected group varieties, `B ↦ φ(B)` is a surjective
    map of flag varieties. "If `Ker(φ)` is contained in some Borel subgroup of
    `G`, then `φ_B` is bijective." The proof notes that the kernel "is
    contained in every Borel subgroup, and so `B = φ⁻¹(φ(B))`".
  - 17.84 (printed p.379, PDF p.395) and the text before Remark 18.4 (printed
    p.388, PDF p.404): "the centre of a reductive group is contained in every
    maximal torus".
  - Definition 18.1 (printed p.387, PDF p.403): central isogenies.
- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`, §11
  (printed p.79, PDF p.32). Steinberg applies the simply connected case "to the
  simply connected covering group of a group which is as in 1.8 but not simply
  connected". The hypothesis of 1.8 ("contains a Borel subgroup over `k`")
  must then hold for the cover. This proposition supplies it.

Derived content. The sources give the bijection of Borel subgroups over an
algebraically closed field. The Lean statement is its consequence for
`K`-rational Borel subgroups, with scheme-theoretic kernels. The derivation is
as follows. The kernel of `π` is central, hence contained in the centre of
`G_{K̄}`, hence in every maximal torus and every Borel subgroup of `G_{K̄}`. If
`B ⊆ A` is a geometric Borel subgroup, its preimage `π⁻¹(B)` is a closed
`K`-subgroup of `G`. Over `K̄` it equals `B'·ker π = B'` for the Borel subgroup
`B'` of `G_{K̄}` with `π(B') = B_{K̄}` (Milne 17.54). So `π⁻¹(B)` is smooth and
connected, and is a Borel subgroup over `K` and over `K̄`.

## What is not stated

- The bijection between Borel subgroups of `G` and `A` is not stated, and
  neither is the converse implication.
- Nothing is proved here; the implication is the obligation of a separate
  exact-target proof.
