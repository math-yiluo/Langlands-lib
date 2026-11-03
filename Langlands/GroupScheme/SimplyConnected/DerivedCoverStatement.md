# Statement: existence of simply connected covers of actual reductive derived subgroups

Author: Worker 266.

This module contains one `Prop`-valued definition and no proof.

## The Lean proposition

`Langlands.GroupScheme.SimplyConnectedDerivedCoverExistenceStatement.{u}` is

```lean
∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
  IsConnectedReductive G →
    ∃ (D C : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G) (π : C ⟶ D),
      IsSimplyConnectedDerivedCover d π
```

The universe `u` is arbitrary and `k` is an arbitrary field in it, including
imperfect fields and fields of positive characteristic. `G`, `D` and `C` are
actual group schemes `Langlands.GroupScheme (Spec k) = Grp (Over (Spec k))`
over the same base, and `d`, `π` are actual group-scheme homomorphisms. The only
hypothesis is `IsConnectedReductive G`. The conclusion is an unconditional
existence assertion: the groups `D`, `C` and both maps are existential
witnesses. No derived group, covering group, root datum, splitting,
representability result or cover-existence law is supplied or assumed.

The published predicate `IsSimplyConnectedDerivedCover d π` from
`SimplyConnected/DerivedCover` has three fields.

- `isConnectedReductive : IsConnectedReductive G`. This repeats the
  hypothesis.
- `isDerivedSubgroup : IsDerivedSubgroup d`. The map `d` is a closed
  subgroup inclusion and `SubgroupFunctor.range d = derivedSubgroup G`, an
  equality of subgroup functors on every test scheme over `Spec k`, including
  nonreduced tests. `derivedSubgroup G` is the scheme-theoretic derived
  subgroup from `Derived/Basic`, not the abstract commutator subgroup of
  `G(k)`.
- `isSimplyConnectedCover : IsSimplyConnectedCover π`, from
  `SimplyConnected/Basic`. It requires:
  - `IsSemisimple D`: `D` is connected reductive and its full
    scheme-theoretic centre is represented by a closed subgroup with finite
    structure morphism;
  - `IsSimplyConnected C`: `C` is semisimple and every central isogeny
    `H ⟶ C` from a semisimple `H` over `k` is an isomorphism;
  - `IsCentralIsogeny π`: the underlying scheme morphism of `π` is finite,
    flat, surjective and locally of finite presentation, and the full
    scheme-theoretic kernel inclusion `kernelι π` is central in `C` on every
    test scheme;
  - `HasCentralCoverUniversalProperty π`: for every central isogeny
    `q : H ⟶ D` from a semisimple `H`, there is a unique homomorphism
    `a : C ⟶ H` with `a ≫ q = π`.

The covering map is `π : C ⟶ D`, onto the derived subgroup. The ambient map
is the composite `π ≫ d : C ⟶ G`. The proposition does not require `π ≫ d` to
be surjective, flat or an isogeny onto `G`. A connected reductive group can
have a central torus, while `C` covers only its derived subgroup. The
published lemmas of
`IsSimplyConnectedDerivedCover`, which apply to any witnesses of this
proposition, give the ambient comparisons:

- `range_comp_le_derivedSubgroup`: the range functor of `π ≫ d` is contained
  in `derivedSubgroup G`;
- `comp_eq_one_iff` and `kernel_range_eq`: on every test scheme a point of `C`
  is killed by `π ≫ d` exactly when it is killed by `π`, so the two actual
  kernels have the same range functor in `C`;
- `isCentral_kernel_comp`: the full kernel of `π ≫ d` is central in `C`;
- `kernelIso`, with `kernelIso_hom_comp`, `kernelIso_hom_points` and
  `kernelIso_hom_points_naturality`: the actual isomorphism
  `kernel (π ≫ d) ≅ kernel π`, compatible with the inclusions into `C` and
  natural in the test scheme.

For two covers of the same `D`, `IsSimplyConnectedCover.iso` and
`IsSimplyConnectedCover.iso_unique` give the canonical comparison. This
proposition does not restate them.

## Sources and derived packaging

The proposition combines two source theorems, and its provenance is derived.

- J. S. Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
  Proposition 19.21(c), printed p. 402 (PDF p. 418): for a reductive group
  `G`, "The algebraic group G^der is semisimple".
- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second
  edition (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`. The
  paragraph before Corollary A.4.11, printed p. 500 (PDF p. 526), calls a
  connected semisimple group simply connected if every central isogeny to it
  from a connected semisimple group is an isomorphism. Corollary A.4.11(1),
  printed pp. 500–501 (PDF pp. 526–527), holds over an arbitrary field `k`: a
  connected semisimple `k`-group `G` has a central isogeny `G̃ → G` from a
  simply connected connected semisimple `k`-group, unique up to unique
  isomorphism. The proposition applies this to the derived subgroup `D`.
- Milne Proposition 19.15, printed pp. 400–401 (PDF pp. 416–417), gives the
  same central-isogeny criterion for simply connected semisimple groups and
  calls it the usual definition, citing Conrad et al. 2015, p. 500.
- Milne Proposition 18.8, printed p. 389 (PDF p. 405), is the source of the
  unique-factorization law stored in `HasCentralCoverUniversalProperty`. By
  the registered errata, the factorization `α` lands in the source `G'` of the
  incoming isogeny. The law is an explicit field of the published cover
  predicate. Deducing it from simple connectedness over an arbitrary field is
  not assumed here; task `2be094ba-099b-4960-b5e3-3326c4320317` states that
  law separately.

`SimplyConnected/Basic.md` and `SimplyConnected/DerivedCover.md` describe how
these source conventions match the Library predicates.
`Reductive/Semisimple.md` explains the finite-centre form of semisimplicity
(Milne Proposition 19.10), and `Derived/StructureStatement.md` explains the
derived-subgroup convention (Milne 6.16–6.18). The composite assertion, that
a connected reductive group has an actual derived-subgroup inclusion with an
actual simply connected cover of its source, does not occur verbatim in
these sources.

The retained official errata
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read in full. Its only Chapter 19 correction is to Definition 19.7
(almost-simple groups), which is not used here. It does not correct
Propositions 19.10, 19.15 or 19.21. Its Chapter 18 entry is the
Proposition 18.8 arrow correction described above. No retained project errata
for CGP was found.

## Intended proof route (not formalized)

A proof is expected to combine three separate obligations, none of which is
proved or assumed here.

1. `IsConnectedReductive G` supplies an affine structure morphism, and
   smoothness implies local finite type. The published
   `DerivedSubgroupRepresentabilityStatement` (`Derived/StructureStatement`,
   with its own proof ownership) then gives an actual `d : D ⟶ G` with
   `IsDerivedSubgroup d`.
2. The separate statement that the source of every such inclusion is
   semisimple, Milne Proposition 19.21(c), gives `IsSemisimple D`.
3. A separate statement of existence of simply connected central covers of
   semisimple field groups (CGP Corollary A.4.11(1), task
   `ca621c65-139e-4ee3-a67e-d5357df9b4be`) gives `C` and `π` with
   `IsSimplyConnectedCover π`.

The hypothesis supplies the remaining field `isConnectedReductive`. After this
proposition is accepted, an exact-target proof task will be published or
coordinated.

## What is not stated

The proposition asserts no field-extension compatibility, no uniqueness beyond
the existing comparison of supplied covers, no canonical or chosen cover, and
no claim about rational points or groups that are not connected reductive. It
imposes no surjectivity on `π ≫ d : C ⟶ G`.
