# Structure statements on the actual local Weil group

Author: Worker 25. This is a statement contribution: every declaration is a
`Prop`-valued definition, and nothing here is proved. Proofs belong to separate
tasks.

`Langlands.Weil.Local.LocalWeilRepresentationStatements.{u,v}` quantifies
over every prime `p` and every `F : PadicField.{u} p`, with an independent
representation-carrier universe `v`. The group, inertia, geometric degree,
projection to the absolute Galois group, unramified characters and norm are
Worker 53's published constructions in `Langlands.Weil.Local.Assembly`. No
group, comparison map, Frobenius lift, assembly theorem, continuity bridge or
classification witness is an additional input. Geometric Frobenius has degree
`+1`, and the norm is `q^(-degree)` with `q` the residue cardinality of
`F.canonicalTopologicalData`. This is how `localNormCharacter` is constructed;
`LocalAssemblyProperties` states it as a target.

## Declaration and source map

Every declaration below is in the namespace `Langlands.Weil.Local`. Each `For`
target takes the actual field `F`; the complete target quantifies over all
`p` and `F`.

| Declaration | Exact content | Source and generic counterpart |
| --- | --- | --- |
| `LocalWeilContinuityFor` | For every finite-dimensional complex representation `A` of `localWeilGroup F`, with the usual `moduleTopology` on its carrier: `A.IsContinuous` (continuity into the usual endomorphism topology) is equivalent to orbit continuity, to joint continuity, to open kernel on `localInertia F` and to open kernel on the whole group. Open inertia kernel is equivalent to finite inertia image together with closed inertia kernel. | Henniart 1980 §2.1 and §2.5 (opening: a continuous representation is trivial on an open subgroup of inertia); Tate (2.1). This is the actual-group form of `Langlands.Weil.RepresentationContinuity`. Worker 38's `RepresentationContinuityCompatibility` compares the bundled normed-carrier form with the `FiniteRepresentation` predicates used here. |
| `LocalWeilGaloisTypeFor` | `IsLocalGaloisType F A`, which says `A` extends along `localProjection F`, is equivalent to `A.IsContinuous ∧ A.HasFiniteImage`. A continuous finite-image representation has exactly one continuous extension to the absolute Galois group on the same carrier. | Henniart 1980 §2.1 ("de type galoisien si et seulement si son image est finie"); Tate (2.2). Actual-group form of `Langlands.Weil.FiniteImageExtension`. |
| `LocalWeilUnramifiedCorrectionFor` | Every continuous representation has a continuous unramified representation `τ` on the same carrier. `τ` commutes with every operator of `A`, and the product `σ g = A g * τ g` is continuous, has finite image and has Galois type. | Henniart 1980 Corollary 2 of Theorem 2.2 (§2.3), with proof in §2.4–2.6 (a polynomial root of a power of Frobenius); Tate (2.2.1). General clause of `Langlands.Weil.UnramifiedReduction`. The statement is not restricted to irreducibles. |
| `LocalWeilIrreducibleReductionFor` | An irreducible continuous representation is equivalent, by a genuine `FiniteRepresentation.Equiv`, to the twist of a continuous, irreducible, finite-image representation of Galois type by `localUnramifiedCharacter F z` for some `z : ℂˣ`. For such a representation, finite image is equivalent to finite order of its determinant. | Henniart 1980 Corollary 3 (§2.3, proof §2.4); Tate (2.2.1). Irreducible clauses of `UnramifiedReduction`. The determinant criterion is derived: some power of Frobenius acts as a scalar by Schur's lemma. |
| `LocalUnramifiedCharacterClassificationFor` | An algebraic character `χ` of the local Weil group is trivial on inertia if and only if `χ` is continuous and `z = χ(localGeometricFrobenius F)` is the unique unit with `localUnramifiedCharacter F z = χ`. | Henniart 1980 §2.2 ("déterminée par la donnée de l'image de Fr"); derived from surjectivity of `localDegree F`, whose kernel is `localInertia F`. |
| `LocalWeilCharacterNormalizationFor` | Every continuous representation has a unique continuous character equal to its determinant. In rank one there is a unique continuous character `χ` with `A` equivalent to `characterRepresentation χ` and `χ` equal to the determinant. | Actual-group form of `Langlands.Weil.RepresentationCharacterNormalization`. The determinant equality in rank one is derived linear algebra. No correspondence assertion is included. |
| `LocalCharacterInertiaFor` | Every continuous character `localWeilGroup F →ₜ* ℂˣ` has open kernel and finite image on actual inertia. | Rank-one consequence of the continuity family (Tate (2.1): `GL(V)` has no small subgroups). It is the inertia condition that twisting of parameters requires, for example in `openInertiaTwist`. It does not replace the full bridge. |
| `LocalNormFaithfulnessFor` | The kernel of `localNormCharacter F` is `localInertia F`. At every element of nonzero degree, no nonzero integer power of the norm equals one. | Derived from `q ≥ 2` and the formula `q^(-degree)`; Tate (1.4.1), (1.4.6) and 4.1.3. |
| `LocalFrobeniusHypothesesFor` | `Frobenius.NormCompatible` holds for `(localNormCharacter F).toMonoidHom`, `(localDegree F).toMonoidHom` and `q = F.canonicalTopologicalData.residueCardinality`. In addition, `CompactSpace (localDegree F).toMonoidHom.ker` holds. | This states the hypotheses of Worker 1's `FrobeniusStatements` targets and of the `WeilDeligneRepresentation.Blocks` targets in exactly the form those targets take as input. Mathematically it restates the norm formula and compactness clauses of `LocalAssemblyProperties`, together with the proved `residueCardinality_gt_one`. |
| `LocalWeilRepresentationStatements` | The conjunction of all preceding field-specialized families, for every `p` and `F`, with independent universes `u` and `v`. | The complete interface. No conjunct is an assumed construction field. |

## Use with the generic Weil–Deligne targets

The generic Frobenius-semisimplification targets (`WeilDeligneRepresentation.Frobenius`)
and block targets (`WeilDeligneRepresentation.Blocks`) take several inputs: a degree
homomorphism `degree`, the hypotheses `Function.Surjective degree` and
`NormCompatible degree q`, and, for each pair, finite image on `degree.ker`.
The parameter normal form also requires `CompactSpace degree.ker` and a
topological group. At the actual local data these inputs are supplied as follows:

- `Function.Surjective (localDegree F)` is the proved theorem `localDegree_surjective`.
- `NormCompatible` and `CompactSpace` are `LocalFrobeniusHypothesesFor`.
- `localInertia F` is by definition `(localDegree F).toMonoidHom.ker`, so the
  equality holds by `rfl`. The finite-inertia-image clause of
  `LocalWeilContinuityFor` is therefore literally finite image on `degree.ker`.
- The local Weil group has the `IsTopologicalGroup` instance of the pullback
  construction.

Worker 25 checked privately, without submitting the check, that these
facts compile. The check confirmed the `rfl` identification of `localInertia F`
with the degree kernel, the instance, and the derivation of
`LocalFrobeniusHypothesesFor F` from `LocalAssemblyProperties F` and
`residueCardinality_gt_one`. Local restatements of the Frobenius and block
targets would only repeat the generic statements with these inputs filled in,
so this file adds none.

## Original sources

The originals were read by Worker 25, and the locators were re-verified on 2026-10-20.

- `henniart-1980-weil-representations`: G. Henniart, *Représentations du groupe
  de Weil d'un corps local*, Enseign. Math. (2) 26 (1980), 155–172, retained PDF
  SHA-256 `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
  The relevant sections are §2.1–2.6, printed pages 158–160 (PDF 5–7):
  - Galois type is equivalent to finite image.
  - Unramified representations are determined by the image of `Fr`.
  - Theorem 2.2 and Corollaries 1–3: the commuting unramified correction and
    the irreducible unramified twist.
  - The proof in §2.5–2.6 via a polynomial `Q` with `Q(T)^(mn) ≡ T`.
- `tate-1979-number-theoretic-background`: J. Tate, *Number theoretic
  background*, Proc. Sympos. Pure Math. 33, Part II (1979), retained Corvallis
  `Part II.pdf`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`; printed
  page `p` is PDF page `p+9`. The relevant parts are:
  - (1.4.1) and (1.4.6), printed pages 6–7 (PDF 15–16): geometric Frobenius
    normalization and `‖w‖`.
  - (2.1)–(2.2.1), printed pages 9–10 (PDF 18–19): no small subgroups, Galois
    type equals finite image, and the twist of an irreducible representation
    to finite image.
  - 4.1.3, printed page 20 (PDF 29): `‖Φ‖ = q⁻¹`.

Neither source states the whole conjunction verbatim. Each clause is the
actual-group form of a source statement or a short derived consequence, as
recorded in the table.

## Mathematical scope

The carrier of a representation is an actual finite-dimensional complex vector
space. Orbit and joint continuity use its usual `moduleTopology`. Operator
continuity uses the corresponding endomorphism topology from `IsContinuous`.
Rank zero is allowed. Irreducibility is imposed only in the irreducible
reduction and its determinant criterion, and rank one only in the scalar
normalization. Finite inertia image alone is never asserted to imply
continuity; closedness of the inertia kernel is explicit.

The general commuting correction is existential and keeps the original
carrier. The irreducible reduction quantifies a new representation and a
genuine linear equivalence; neither is assumed in a structure. Three different
uniqueness claims appear:

- In the character classification, the unit value `z` is unique.
- The Galois extension is unique as a representation on the original space.
- In rank one, the character is unique as a continuous group homomorphism,
  although the equivalence need not be.

The finite-image factor in the scalar reduction is not asserted to be unique.
The determinant character is quantified even in rank zero. Continuous characters are
unrestricted, so the open inertia condition is a conclusion. No reciprocity map
or local Langlands bijection is supplied or assumed.

## Lean dependency map

All imports are Lean modules of the current Library (commit
`00f9ac4d66cfd40043d36dbe31ea364e1316cde9`); no artifact identity is imported.
The direct imports are `Langlands.Weil.Local.Parameters`,
`Langlands.Weil.Representation.Twist` and
`Langlands.WeilDeligne.FrobeniusStatements`. Their transitive project closure
has 28 modules. The modules whose declarations appear in the statements are:

| Module | Declarations used here | Lean SHA-256 |
| --- | --- | --- |
| `Langlands.Weil.Local.Parameters` | `LocalWeilRepresentation`, `IsLocalGaloisType` | `411478f2fd50ec77e62978dbc2352f5d3511bdb4d9d8cfc99e040c73fca8b551` |
| `Langlands.Weil.Local.Assembly` | `localWeilGroup`, `localProjection`, `localDegree`, `localDegreeInt`, `localInertia`, `localGeometricFrobenius`, `localUnramifiedCharacter`, `localNormCharacter` | `576d8ad3c15763bdf047c2289beea60530c5d95a70963395444fd1efbd49cad8` |
| `Langlands.Weil.Representation.Twist` | `FiniteRepresentation.twist` | `cbeda9cff731f24d07c356c7e24e5e9a20a6e248fc9439bc0888cc909ab862c8` |
| `Langlands.Weil.Representation.Predicates` | `IsContinuous`, `HasOpenInertiaKernel`, `HasFiniteInertiaImage`, `inertiaKernel`, `IsUnramified`, `HasFiniteImage`, `IsIrreducible`, `IsGaloisTypeAlong` | `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148` |
| `Langlands.Weil.Representation.Basic` | `FiniteRepresentation`, `FiniteRepresentation.of`, `FiniteRepresentation.Equiv`, `rank` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Representation.Twist.Definitions` | `characterRepresentation` | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` |
| `Langlands.WeilDeligne.FrobeniusStatements` | `Frobenius.NormCompatible` only | `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa` |
| `Langlands.LocalField.Definitions` | `PadicField` | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` |
| `Langlands.LocalField.Canonical` | `PadicField.canonicalTopologicalData` | `e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48` |
| `Langlands.LocalField.Normalization.Definitions` | `residueCardinality` | `b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b` |
| `Langlands.Weil.Pullback` | `Degree`, and the group and topology of `localWeilGroup` | `1dd3491a90d6849c98bd49a0abd9fa684313ef2b040c9ab11bc49d3967cd6380` |
| `Langlands.Weil.Local.DegreeCharacters` | (unramified characters, through `Assembly`) | `f93ff5bdd74ce036c69453f9d00c879f611ae40608e0c06cbd6b25e5441ebac0` |
| `Langlands.Weil.Local.ResidueCharacters` | (the norm character, through `Assembly`) | `8f47ed222e4b3b933bbce66918b67f14803267a2c211a1756f25d3fe4aac3833` |

The local constructions are Worker 53's (parameter-definition companion task
`503968de-16f8-4f63-ba13-b5e167e11dce`). `FrobeniusStatements` is Worker 1's
statement family; only its predicate `NormCompatible` is used, and none of its
targets is assumed. The generic statements cited in the table
(`RepresentationContinuity`, `UnramifiedReduction`, `FiniteImageExtension`,
`RepresentationCharacterNormalization`) are published in
`Langlands.Weil.Representation.{Continuity,Structure,Operations}`. They are not
imported, because no local statement is defined through them. Mathlib is pinned
at `5ed2965256430c3649e86755f9576b54eca72435`; `moduleTopology`,
`Representation.IsIrreducible` and `LinearMap.det` come from Mathlib.

## Outside this file

Restriction and induction along finite extensions, which use
`extensionWeilMap` and the residue-degree rescaling of the degree, are a
separate local family. Arithmetic factors and the LLC correspondence assertion
belong to their existing tasks.
