# Milne 16.6 from Milne 16.2

This module derives the published statement
`Langlands.GroupScheme.SeparablyTrigonalizableCriterionStatement.{u}`
(Milne, Theorem 16.6) from the published statement
`Langlands.GroupScheme.TrigonalizableCharacterizationStatement.{u}`
(Milne, Proposition 16.2), taken as an explicit hypothesis `hChar`. Only the
third equivalence of 16.2, `IsTrigonalizable G ↔ (d)`, is used:
`(hChar k G).2.2`. Here (d) says that `G` has a normal unipotent closed
subgroup `U` with an fppf quotient `G ⟶ D(Λ)` by `U`, with `Λ` finitely
generated.

All declarations are in the namespace
`Langlands.GroupScheme.SeparableTrigonalization`. Throughout, `k : Type u` is
a field, `G` is a group scheme over `Spec (CommRingCat.of k)` with
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`, and `G_K` means
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G`.

## `exists_separable_isTrigonalizable` ((b) ⇒ (a))

**Statement.** Assume `hChar`. Let `i : U ⟶ G` and `q : G ⟶ M` satisfy
`IsClosedSubgroup i`, `IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal`,
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` and
`IsMultiplicativeType M`. Then there are a field `K : Type u` and
`[Algebra k K]` with `Algebra.IsSeparable k K` and `IsTrigonalizable G_K`.

**Proof.** This is Milne's proof.

1. By `multiplicativeTypeFiniteGaloisSplitting` (Milne 12.19; Milne's proof
   cites 12.18), `M` becomes
   diagonalizable over a finite Galois extension `K` of `k`: there are a
   finitely generated `Λ` and `e : M_K ≅ D(Λ)`. A finite Galois extension is
   separable.
2. Write `B` for base change along `Spec K ⟶ Spec k`. `G_K` is again locally
   of finite type and affine over `K`, and `U` is affine over `k` because `i`
   is a closed immersion.
3. Apply the backward direction of `(hChar K G_K).2.2` to
   `B.map i : U_K ⟶ G_K` and `B.map q ≫ e.hom : G_K ⟶ D(Λ)`:
   - `IsClosedSubgroup (B.map i)` is `IsClosedSubgroup.baseChange`;
   - `IsUnipotent U_K` is `IsUnipotent.baseChange` (Milne 14.9);
   - normality: `range (B.map i) = (range i).baseChange _`
     (`SubgroupFunctor.range_baseChangeHom`), which is normal by
     `IsNormal.baseChange`;
   - the fppf quotient: after the same rewriting, this is
     `IsFppfQuotient.baseChange` followed by `IsFppfQuotient.comp_iso e`.

## `exists_unipotent_multiplicativeType_quotient` ((a) ⇒ (b))

**Statement.** Assume `hChar`. Let `K : Type u` be a field with
`[Algebra k K]`, `[Algebra.IsSeparable k K]` and `IsTrigonalizable G_K`. Then
there are `U`, `M`, `i : U ⟶ G` and `q : G ⟶ M` with `IsClosedSubgroup i`,
`IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal`,
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` and
`IsMultiplicativeType M`.

**Proof.** Milne's proof passes to a finite Galois extension over which `G`
is trigonalizable. Here we use the separable closure `Ω := SeparableClosure k`
instead: it is Galois over `k`, and `K` embeds into it. The Library's Galois
descent of closed subgroups works for any Galois extension, finite or not.

1. **16.2 over `K`.** `G_K` is locally of finite type and affine over `K`.
   The forward direction of `(hChar K G_K).2.2` gives `i' : U' ⟶ G_K`,
   a finitely generated `Λ` and `q' : G_K ⟶ D(Λ)` with `IsClosedSubgroup i'`,
   `IsUnipotent U'`, normal range and
   `IsFppfQuotient (range i') q'`.
2. **Transport to `Ω`.** Choose `f := IsSepClosed.lift : K →ₐ[k] Ω`. This
   makes `Ω` a `K`-algebra with `IsScalarTower k K Ω`. Let `c` be
   `Spec Ω ⟶ Spec K`, `C` base change along `c`, and `B` base change along
   `algebraBaseMap k Ω`. Let `tower := baseChangeFieldTowerIso k K Ω G :
   G_Ω ≅ C.obj G_K` and `d := Diagonalizable.baseChangeIso c Λ :
   C.obj D_K(Λ) ≅ D_Ω(Λ)`. Put
   `i'' := C.map i' ≫ tower.symm.hom : U'_Ω ⟶ G_Ω` and
   `q'' := tower.symm.inv ≫ (C.map q' ≫ d.hom) : G_Ω ⟶ D_Ω(Λ)`.
   - `i''` is a closed subgroup (`IsClosedSubgroup.baseChange`, then
     `IsClosedSubgroup.comp_iso`), and `U'_Ω` is unipotent
     (`IsUnipotent.baseChange`).
   - `range i'' = ((range i').baseChange c).comap tower.symm.inv`, by
     `SubgroupFunctor.range_comp_iso` and `range_baseChangeHom`.
   - With this, `IsFppfQuotient (range i'') q''` follows from
     `IsFppfQuotient.baseChange c`, `IsFppfQuotient.comp_iso d` and
     `IsFppfQuotient.comapIso tower.symm`. Normality of `range i''` follows
     from `IsNormal.baseChange` and `IsNormal.comap`.
3. **Greatest, hence Galois invariant.** `D_Ω(Λ)` is of multiplicative type
   over `Ω` (witnessed by `Ω` itself and `Diagonalizable.baseChangeIso`). So
   `IsUnipotent.isGreatestUnipotentSubgroup` (from
   [`GreatestUnipotent`](GreatestUnipotent.md)) shows that `i''` contains
   every closed unipotent subgroup of `G_Ω`, and
   `IsGreatestUnipotentSubgroup.range_radicalGaloisHom` gives
   `range (radicalGaloisHom i'' σ) = range i''` for every
   `σ : Ω ≃ₐ[k] Ω`.
4. **Galois descent.** `Descent.GaloisInvariantClosedSubgroup.exists_descent`
   (Milne 1.54; uses `IsGalois k Ω`) gives `H₀`, a closed subgroup
   `j₀ : H₀ ⟶ G` and `r : B.obj H₀ ≅ U'_Ω` with `B.map j₀ = r.hom ≫ i''`.
   Hence `(range j₀).baseChange b = range i''`, by `range_baseChangeHom` and
   `SubgroupFunctor.range_iso_comp`.
5. **Unipotent and normal.** `B.obj H₀ ≅ U'_Ω` is unipotent
   (`IsUnipotent.of_iso`), so `H₀` is unipotent by
   `IsUnipotent.of_baseChange` (field reflection of unipotence, Milne 14.9).
   `Spec Ω ⟶ Spec k` is fpqc (`fieldExtension_fpqc`), `j₀` is a
   monomorphism, and `(range j₀).baseChange b = range i''` is normal; so
   `range j₀` is normal by `SubgroupFunctor.isNormal_range_of_baseChange`.
6. **The quotient.** `affineNormalSubgroupQuotient` (Milne 5.14) gives an
   affine `M₀`, locally of finite type, and `q₀ : G ⟶ M₀` with
   `IsFppfQuotient (range j₀) q₀`. Its base change `B.map q₀` is an fppf
   quotient of `G_Ω` by `(range j₀).baseChange b = range i''`
   (`IsFppfQuotient.baseChange`). So `B.map q₀` and `q''` are fppf quotients
   of `G_Ω` by the same subgroup functor. All schemes involved are affine,
   so both maps are affine morphisms, hence quasi-compact.
   `FppfQuotientComparison.iso` then gives `B.obj M₀ ≅ D_Ω(Λ)`. This
   witnesses `IsMultiplicativeType M₀`, with the field `Ω` and the group
   `Λ`.

The output is `(H₀, M₀, j₀, q₀)`.

## `separablyTrigonalizableCriterion_of_characterization`

**Statement.** `TrigonalizableCharacterizationStatement.{u} →
SeparablyTrigonalizableCriterionStatement.{u}`.

**Proof.** Fix `k` and `G`. The forward direction of the equivalence is
`exists_unipotent_multiplicativeType_quotient`, and the backward direction is
`exists_separable_isTrigonalizable`. The second part of the statement (every
closed unipotent subgroup lies in `U`) is
`IsUnipotent.range_le_of_isFppfQuotient` from
[`UnipotentKernelMaximal`](UnipotentKernelMaximal.md). It does not use
`hChar`, nor the unipotence or normality of `U`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Printed
page numbers; the one-based PDF page is the printed page plus 16.

- Theorem 16.6, pp.325–326, and its proof. The proof of (a) ⇒ (b) uses a
  finite Galois extension, Proposition 16.2(d), uniqueness of `G_u` and
  Galois descent (1.54). The proof of (b) ⇒ (a) uses 12.18, 14.9 and 16.2(d).
- Proposition 16.2, p.324: the characterization of trigonalizable groups,
  formalized as `TrigonalizableCharacterizationStatement`.

The implemented route differs from Milne's in one point only: (a) ⇒ (b)
works over the separable closure of `k` rather than a finite Galois
extension. This makes no difference to the result.
