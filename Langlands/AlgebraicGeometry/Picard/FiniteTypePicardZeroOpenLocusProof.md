# Geometric Picard-zero openness for actual families over finite-type integer algebras

Authors: Worker 967, Worker 1095.

Module `Langlands.AlgebraicGeometry.Picard.FiniteTypePicardZeroOpenLocusProof`
proves the published statement
`Langlands.AbelianScheme.FiniteTypePicardZeroOpenLocusStatement.{u}` as

```lean
theorem Langlands.AbelianScheme.finiteTypePicardZeroOpenLocus :
    FiniteTypePicardZeroOpenLocusStatement.{u}
```

The statement says: for every commutative finite-type `ℤ`-algebra `R` in
universe `u`, every abelian scheme `A` over `Spec R`, every `P : Over (Spec R)`
and every actual rigidified family `L : RigidifiedFamily A P`, there is an
open `U ⊆ P.left` with `IsPicardZeroOpenLocus A L U`. That is the
all-test criterion of the Library module `Picard/OpenLocus`: for every
`T : Over (Spec R)` and every `h : T ⟶ P`, the class given by the actual
pullback classifier of `L` along `h` is Picard-zero if and only if
`Set.range h.left ⊆ U`.

The proof does not use that `R` is of finite type, or anything else about
`R`. The construction works for an abelian scheme over an arbitrary scheme
`S` and any `P` over `S`.

## Ingredients

All of these are imported by Lean name from the Library.

* **Core criterion.** `Langlands.AbelianScheme.mumfordTrivialLocus G M : B.Opens`
  and `isTranslationInvariant_fibreLineBundle_iff G M K t` (module
  `Langlands.AbelianScheme.MumfordTrivialLocus`, Worker 1095). Here `B` is
  an arbitrary scheme, `G` an abelian scheme over `B` and `M` an arbitrary
  line bundle on `G.X.left`. The open set is the set of points `b` of `B`
  such that the Mumford class of `M` on `G.X ⨯ G.X` pulls back to the
  trivial class on the scheme fibre over `b`. For every
  algebraically closed field `K` in universe `u` and every
  `t : Spec K ⟶ B`, the restriction `fibreLineBundle G M t` is translation
  invariant on `G_t` if and only if `Set.range t ⊆ mumfordTrivialLocus G M`.
* **Comparisons.** `exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion`
  (module `Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison`,
  Worker 967). Its hypothesis is that
  `HasOpenFibreTranslationInvarianceLocus G M` holds for every line bundle
  `M` on every abelian scheme `G` over every base `B`. Its conclusion is
  an open `U ⊆ P.left` such that, for every algebraically closed `K` in
  universe `u` and every `s : Spec K ⟶ P.left`,
  `IsPicardZeroFamily A L_s ↔ Set.range s ⊆ U`. Here `L_s` is the actual
  relative pullback of `L` along `Over.homMk s rfl`.
* **Bridge.** `isPicardZeroOpenLocus_of_geometricPoints` (module
  `Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricOpenLocusBridgeProof`,
  Worker 390). Given the geometric detection statement, an open `U ⊆ P.left`
  with the geometric-point property above satisfies `IsPicardZeroOpenLocus A L U`.
* **Geometric detection.** `picardZeroGeometricDetection : PicardZeroGeometricDetectionStatement`
  (module `Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionProof`).

## Proof

Introduce `R`, its instances, `A`, `P` and `L`.

1. The hypothesis of the comparison theorem is supplied by the core
   criterion: for each `G` and `M`, the open set `mumfordTrivialLocus G M`
   witnesses `HasOpenFibreTranslationInvarianceLocus G M`, and
   `isTranslationInvariant_fibreLineBundle_iff G M K t` is the required
   equivalence at each geometric point `t`. The comparison theorem uses it
   for `G = A_P` with `M = familyLineBundle A L`, and again over each
   geometric point `Spec K`.
2. The comparison theorem therefore gives an open `U ⊆ P.left` with
   `IsPicardZeroFamily A L_s ↔ Set.range s ⊆ U` for every algebraically
   closed geometric point `s`.
3. The bridge, applied to `picardZeroGeometricDetection`, `A`, `L`, `U` and
   that equivalence, gives `IsPicardZeroOpenLocus A L U`. The pair
   `⟨U, _⟩` proves the statement.

No hypothesis beyond those of the statement is added, and no open set,
comparison or representer is assumed.
