# Quasi-compactness of the chosen dual parameter scheme (proof)

This module proves the published statement
`Langlands.AbelianScheme.RelativeDualSchemeQuasiCompactStatement.{u}` from module
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeQuasiCompactStatement`:

- `Langlands.AbelianScheme.relativeDualSchemeQuasiCompact :
  RelativeDualSchemeQuasiCompactStatement.{u}`. For every scheme `S` with
  `[QuasiSeparatedSpace S]`, every abelian scheme `A` over `S` and every `hA : HasDualScheme A`,
  the structural morphism `(dualScheme A hA).hom` is quasi-compact (`QuasiCompact`).

The quasi-separatedness instance on `S` is not used; the argument works over every base scheme.
The theorem has no additional hypotheses. The two published statements threaded through the
helper modules, `pullbackTensorComparisonIsIsoStatement` and `MumfordBundlePicardZeroStatement`,
are discharged here by the published proofs `pullbackTensorComparisonIsIso` and
`mumfordBundlePicardZero`. The published `picardZeroUniversalBaseChange` is used for base change
of the dual. The proof does not use representability of the Picard functor, and it does not use
properness or projectivity of the dual.

The module relies on three helper modules, submitted with it:

- `RelativeMumfordFibreImage`: points of the dual over the ample-fibre locus are in the image of a
  Mumford map;
- `AmpleFibreCover`: the predicate `HasAmpleFibreCover` and its transport lemmas;
- `NoetherianAmpleFibreCover`: ample-fibre covers over noetherian affine bases.

## Results and proofs

- `hasAmpleFibreCover_of_isAffineOpen A hU`. For an affine open `U ⊆ S`,
  `HasAmpleFibreCover A.X.hom U` holds. The proof:
  1. Let `h = hU.fromSpec : Spec Γ(S, U) ⟶ S` and `AR = (baseChange h).obj A`.
  2. The published `abelianSchemeNoetherianModelReduction` is instantiated with the published
     `AbelianScheme.subalgebraDescent`, `lineBundleSubalgebraDescent` and
     `lineBundleIsoSubalgebraDescent`, and with both rigidified bundles trivial. It gives a
     noetherian ring `R₀`, a ring map `φ`, an abelian scheme `A₀` over `Spec R₀`, and a Cartesian
     square `IsPullback a AR.X.hom A₀.X.hom (Spec.map φ)`.
  3. `noetherian_hasAmpleFibreCover A₀` gives a cover of `Spec R₀`.
     `HasAmpleFibreCover.baseChange` moves it to a cover of `Spec Γ(S, U)` for `AR`.
  4. `HasAmpleFibreCover.of_isPullback` along the base-change square of `h` moves it to `S`, with
     `V = range h = U` (`IsAffineOpen.range_fromSpec`).
- `isCompact_preimage_of_hasAmpleFibreCover A hA hV`. If `HasAmpleFibreCover A.X.hom V`, then the
  preimage of `V` in `(dualScheme A hA).left` is compact. For each piece `i` of the cover, the
  proof builds a quasi-compact scheme mapping to the dual whose range lies over `V` and contains
  every dual point over the image of the fibre-ample locus of that piece:
  1. Let `B` be the base change of `A` along `g i : T i ⟶ S`. Its dual exists by
     `hasDualScheme_baseChange picardZeroUniversalBaseChange`.
  2. Transport the piece's line bundle to `L'` on `B.X.left` through `(hpb i).isoPullback`.
  3. Choose an inverse `Bb` of its restriction along the unit section, and an inverse `M` of the
     normalised bundle. Both come from `exists_tensorObj_iso_structureSheaf`.
  4. Let `m = mumfordSchemeMapOfLineBundle … B L' Bb … M … mumfordBundlePicardZero hB`.
  5. Compose `m.left` with the inverse of `dualSchemeBaseChangeIso`, which identifies
     `dualScheme B hB` with `dualScheme A hA ×_S T i`, and then with the first projection to the
     dual of `A`. This gives `φ_i : B.X.left ⟶ (dualScheme A hA).left`.
  6. `B.X.left` is compact because `B.X.hom` is quasi-compact and `T i` is affine
     (`QuasiCompact.compactSpace_of_compactSpace`).
  7. The range of `φ_i` lies over `range (g i) ⊆ V`.
  8. Coverage: take a dual point `y` over `g i t` with `t` in the fibre-ample locus. Choose a
     point `z` of the fibre product over `y` and `t` (`Scheme.Pullback.exists_preimage_pullback`),
     and send it into `dualScheme B hB`. The square relating `L'` and the piece's bundle, together
     with `mem_ampleFibreLocus_iff_of_isPullback`, puts its image in `ampleFibreLocus B.X.hom L'`.
     `mem_range_mumfordSchemeMapOfLineBundle` then gives a preimage under `m`, so `y` lies in the
     range of `φ_i`.

  The preimage of `V` is therefore the finite union of the ranges of the `φ_i`. Each range is the
  continuous image of a compact space, so the union is compact (`isCompact_iUnion`).
- `relativeDualSchemeQuasiCompact`. By `quasiCompact_iff_forall_isAffineOpen`, it suffices to show
  that the preimage of each affine open `U` is compact. This follows from the two previous
  results.

## Provenance

The source of the target statement is recorded in the Markdown of
`RelativeDualSchemeQuasiCompactStatement`: Lan's thesis, Theorem 1.3.2.3, where the dual abelian
scheme is proper and hence quasi-compact. This module does not follow that representability route.
Its argument is internal, a boundedness argument of the kind the statement's Markdown mentions as
an alternative:

- over each affine open, finitely many Mumford maps `Λ(L_i)` from quasi-compact base changes of
  `A` surject onto the dual;
- finiteness comes from noetherian approximation, Chevalley's constructibility theorem and
  compactness of the constructible topology;
- surjectivity on geometric points is the published field-level result
  `AlgClosedFieldTranslationDifferenceLiftingStatement`, which says that every Picard-zero bundle
  on an abelian variety over an algebraically closed field is `t_x^* L ⊗ L^{-1}` for an ample `L`.
  Its literature is cited in that statement's Markdown.
