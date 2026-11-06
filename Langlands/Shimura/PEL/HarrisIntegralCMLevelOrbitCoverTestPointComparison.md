# Point comparison in the original Harris orbit-cover test equivalence

This internal deduction proves that the original test correspondence for an
actual finite Harris orbit cover commutes with change of geometric point.
It constructs the equivalence of actual sets of test morphisms by
postcomposition with the cover point isomorphism. This corresponds to
the existing point transport on selected original direct levels. For two
supplied paths, the resulting underlying direct levels agree.

The namespace is
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`. All arithmetic carriers,
schemes and endpoint fields in this file have universe zero.

## Inputs and original constructions

The arithmetic datum `D`, normalized Harris signature charts `C`, named
scalar structures and prerequisite package `P` are those of the imported
Harris constructions. Supply an actual abelian scheme `B/S`, a dual witness
`W`, a morphism `lam : B ⟶ W.dual P`, and an integral order action `a` on
the actual pullback of `B` to `T`. The finite Weil transition statement,
rational profinite-integer/adele comparison and torsion finite-etale
statement remain explicit. No full CM condition or polarization proof for
`lam` is needed for this conditional comparison.

Let `f : T' ⟶ T` be an arbitrary morphism in `Over S`. Both underlying
schemes are quasi-separated, connected and locally noetherian. Supply two
geometric points `t : Spec Ω ⟶ T'.left` and
`u : Spec Ω' ⟶ T'.left` over possibly different algebraically closed
fields, finiteness of every finite-etale fibre at these points and at the
literal base points `t ≫ f.left` and `u ≫ f.left`, and a path

```text
p : fiberFunctor t ht ≅ fiberFunctor u hupt.
```

The base path is exactly
`pT = pathPushforward f.left htf huf p`. The indexed torsion orders are
invertible on both tests, and the corresponding roots-of-unity schemes
are finite and etale on both. The action on the direct restricted family
is literally `(relativeEndRestrict B f).comp a`. No finiteness or etaleness
hypothesis is placed on `f`.

Write `Raw_t(V)` for the original right-orbit quotient of actual Weil frames
at `t ≫ f.left` by the subgroup of `(hodgeLevelFunctor D C).obj V`.
The right action uses the original opposite similitude group convention,
and its commuting monodromy action is the actual Tate monodromy. Let
`R_p` be the original `harrisIntegralCMWeilRawPointEquiv` at `pT`.
For a raw class `q`, the source cover `C_t(q)` is the existing
`harrisIntegralCMFiniteOrbitCover` at the base point `t ≫ f.left`,
with original Harris levels `U,V` and a supplied witness that the original
fixed-level set at `U` is nonempty. The target cover `C_u(R_p(q))` uses
the target nonempty reference level derived from that source witness by
`harrisIntegralCMFullActionLevelPointNonempty`.

Let `I_p(q) : C_t(q) ≅ C_u(R_p(q))` be the previously constructed
`harrisIntegralCMFiniteOrbitCoverPointIso` for `pT`. Let `E_t` and `E_u`
be the original `harrisIntegralCMFiniteOrbitCoverTestLevelEquiv` at the
two test points, with their base-point equations equal to `rfl`. Their
targets are the actual direct fixed levels on the restricted family whose
original raw evaluation belongs to the selected base monodromy orbit.
Let `S_p` be the existing
`harrisIntegralCMTestLevelOrbitPointEquiv` for `p`.

## Equivalence of actual test morphisms

`harrisIntegralCMFiniteOrbitCoverTestPointEquiv` constructs the equivalence

```text
Hom_Over(T)(T', C_t(q)) ≃ Hom_Over(T)(T', C_u(R_p(q))).
```

It applies `Iso.homCongr` to the identity of `Over.mk f.left` and the
image of `I_p(q)` under the original inclusion of finite-etale covers
into `Over T.left`. Its forward map is postcomposition with
`I_p(q).hom.hom`, as proved in
`harrisIntegralCMFiniteOrbitCoverTestPointEquiv_apply`; its inverse is
postcomposition with `I_p(q).inv.hom`. The inverse laws are the laws of
the existing actual scheme isomorphism. This definition only needs the
base-cover assumptions and the test path with its pushed base path.
The direct-family torsion hypotheses and the connectedness, local
Noetherianity and quasi-separatedness of `T'.left` are used by the
test-level square below.

## Actual test-comparison square

`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointMap` proves, for
every original raw class `q` and every actual morphism
`k : Over.mk f.left ⟶ C_t(q).obj`, the subtype equality

```text
S_p(E_t(k)) = E_u(k ≫ I_p(q).hom.hom).
```

All maps in this equation are the original constructions just named.
The cover point isomorphism uses the actual pushed path, and the selected
direct-level equivalence uses the actual test path. The equality is a
conclusion; no point-compatibility square is supplied as a premise.

The private helper `pathPushforward_testEvaluation` proves that evaluating
a test morphism `k` at `t` and applying the pushed path gives its evaluation
at `u`. It applies the existing `pathPushforward_apply_left_of_comp` to
the identity cover of `T'.left`. The component of the test path on its
unique lift has underlying morphism `u`, by the defining equation of an
Over morphism. This identifies the underlying morphisms of the two lifts;
Over-morphism extensionality proves their equality.

For the public square, subtype extensionality and injectivity of the
original `harrisIntegralCMRestrictionRawClass` reduce the claim to raw
evaluation. The published selected-level evaluation equation and the two
original test-equivalence value formulas identify both evaluations. Apply
the private helper to `k ≫ I_p(q).hom.hom`. Associativity identifies its
evaluation at `t` with evaluation of `k` followed by the cover isomorphism.
The existing `harrisIntegralCMFiniteOrbitCoverPointIso_raw` then gives
exactly the remaining equality.

## Independence of the underlying direct level

`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointMap_val_path_independent`
compares any two supplied paths `p,p'` between the same test points. Each
path has its own original pushed base path, transported raw class,
derived target reference level and target chosen cover. For the same
source `q,k`, the theorem proves

```text
(E_u(k ≫ I_p(q).hom.hom)).val =
  (E_u(k ≫ I_p'(q).hom.hom)).val.
```

The two `E_u` expressions use their respective target raw classes and
covers. Their underlying values lie in the same original direct fixed-level
set at `u,V`. Apply `congrArg Subtype.val` to the preceding square for
each path. Rewriting by those equations reduces the claim to the existing
`harrisIntegralCMTestLevelOrbitPointEquiv_val_path_independent` on the
single source selected level `E_t(k)`. The first square omits the unused
`IsCMField F` and `IsScalarTower ℚ F A` assumptions; this corollary retains
them because that imported path-independence theorem retains them.

## Provenance and scope

The file derives this equivalence and its comparison results from actual Harris point,
restriction, cover and test-equivalence constructions and the actual
finite-etale path pushforward. Its generic evaluation helper is private.
It introduces no external literature assertion or new geometric
prerequisite.

The result concerns a supplied family, reference level and selected finite
raw orbit on connected locally noetherian tests along supplied paths.
It does not identify the two dependent target cover choices or prove equality
of their chosen scheme isomorphisms. Canonical cover-choice comparison,
disconnected-test gluing, the full normalized rational-isogeny comparison,
determinant/Lie and Rosati integration, and existence and admissibility of
a smooth projective representing PEL scheme remain separate obligations.
The exact `DivisionCMRepresentabilityStatement` and all imported Lean and
Markdown pairs are preserved; that target remains open.
