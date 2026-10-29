# The ordinary relative three-face cube criterion for abelian schemes

`Langlands.AbelianScheme.RelativeCubeTrivialityStatement.{u}` is a
`Prop`-valued definition that states the ordinary relative three-face cube
criterion for three independent abelian schemes over an arbitrary
quasi-separated base. The file states the criterion. It does not prove it,
and it adds no axiom saying that the criterion holds.

## Exact statement

The proposition quantifies over a universe `u`, over every scheme
`S : Scheme.{u}` with an instance `[QuasiSeparatedSpace S]`, over three
independently chosen abelian schemes `A B C : AbelianScheme S`, and over every
line bundle

```text
D : Langlands.AlgebraicGeometry.Picard.LineBundle (A.X ⨯ (B.X ⨯ C.X)).left.
```

Here `A.X`, `B.X` and `C.X` are the underlying objects in `Over S`. The product
`⨯` is the chosen categorical product in `Over S`, so `.left` of a product is an
actual iterated fibre product over `S`. Write `P = (A.X ⨯ (B.X ⨯ C.X)).left`.
The three faces are the Library maps `CubeFace.first`, `CubeFace.second` and
`CubeFace.third` from
`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement`, applied to
the unit points of the three abelian schemes:

| Lean map | Domain | Coordinates in `A.X ⨯ (B.X ⨯ C.X)` |
| --- | --- | --- |
| `CubeFace.first A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ A.X)` | `B.X ⨯ C.X` | `(0_A, (b, c))` |
| `CubeFace.second A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ B.X)` | `A.X ⨯ C.X` | `(a, (0_B, c))` |
| `CubeFace.third A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ C.X)` | `A.X ⨯ B.X` | `(a, (b, 0_C))` |

In this table `0_A`, `0_B` and `0_C` denote the identity sections. The Library
writes group-object operations multiplicatively. The Lean term
`(1 : Over.mk (𝟙 S) ⟶ A.X)` is the unit of the monoid of morphisms into the
group object `A.X`, opened by `open scoped CategoryTheory.MonObj`. It equals
the unique map to the monoidal unit followed by the unit of `A.X`, so its
underlying scheme map is the unit section `S → A.X.left`. The same holds for
`B` and `C`. A fixed coordinate in the table is the composite of the domain's
unique map to the terminal object `Over.mk (𝟙 S)` with that section. These
are morphisms of schemes over `S`. They are not described by their action on
points.

The statement has three hypotheses and one conclusion, written here with
the face maps abbreviated:

```text
Nonempty ((Scheme.Modules.pullback (first face).left).obj D.obj ≅ structureSheaf (B.X ⨯ C.X).left) →
Nonempty ((Scheme.Modules.pullback (second face).left).obj D.obj ≅ structureSheaf (A.X ⨯ C.X).left) →
Nonempty ((Scheme.Modules.pullback (third face).left).obj D.obj ≅ structureSheaf (A.X ⨯ B.X).left) →
Nonempty (D.obj ≅ structureSheaf P)
```

`Scheme.Modules.pullback` is Mathlib's pullback functor
`AlgebraicGeometry.Scheme.Modules.pullback` on sheaves of modules, applied to
the underlying scheme map `.left` of each face.
`structureSheaf` is `Langlands.Scheme.Modules.structureSheaf`. On a scheme `X`
it is `SheafOfModules.unit X.ringCatSheaf`, the structure sheaf regarded as a
module over itself. Each pullback is compared with the structure sheaf of the
whole face scheme over `S`, not of a fibre.

The Library's `LineBundle X` is the full subcategory of `X.Modules` of module
sheaves satisfying `IsLocallyFreeRankOne`. Every point has an open
neighbourhood `U` on which the restriction is isomorphic to the unit module
sheaf of `U`. So `D.obj` is an actual locally free rank-one sheaf of
`O_P`-modules. All four `Nonempty` assertions say that isomorphisms of module
sheaves exist. The statement chooses no witnesses, and it does not require the
three face isomorphisms to agree where the faces meet. It introduces no Picard
group, class identity or rigidification datum.

## Scope

The only separate base hypothesis is that `S` is quasi-separated. The base
need not be noetherian, reduced or normal. There is no projectivity,
dual-existence or representability hypothesis. The `AbelianScheme S` bundles
already contain commutativity, smoothness, properness and geometrically
connected fibres. The three abelian schemes are independent, and none is
required to be a product of the others. The face hypotheses are global
statements on the full face schemes over `S`, not conditions on geometric
fibres. The conclusion is triviality on the whole triple product. The
statement does not assume a field cube theorem, a relative cube theorem,
seesaw, rigidity or preservation of tensor products by pullback.

## Source and derivation through Moret-Bailly

The first source is Laurent Moret-Bailly, *Pinceaux de variétés abéliennes*,
Astérisque 129 (1985), Chapter I: formula (2.4.1), printed p.18/PDF p.21, and
Proposition 2.6, case (i), printed pp.21–22/PDF pp.24–25. It is registered as
`moret-bailly-1985-pinceaux-asterisque-129`, with file
`literature/Pinceaux de variétés abéliennes.pdf` and SHA-256
`b8d62fdd2e1d85ff1e688e62bd212aede20e044c373a7613ef01ddc52f02022a`.

Proposition 2.6 is about one smooth commutative `S`-group scheme `A` with
connected fibres, over a scheme `S`. In case (i), where `A` is an abelian
scheme, it states that the forgetful functor `CUB(A, G_m) → TORSRIG(A, G_m)`
is an equivalence of categories. Here `TORSRIG(A, G_m)` is the category of
`G_m`-torsors on `A` trivialized at the origin. A `G_m`-torsor is identified
with an invertible sheaf. For a rigidified `G_m`-torsor `L` on `A`, the proof
of case (i) cites Raynaud IV.2.1 to show that `𝒟₃(L)` on `A³` comes from an
invertible sheaf on `S`. Since `L` is rigidified at the origin, `𝒟₃(L)` is
rigidified too, so it is trivial. The
three-independent-factor statement defined here is not a quotation of
Proposition 2.6. It is a consequence, derived informally as follows.

In ordinary mathematics the fibre product `G = A ×_S B ×_S C` is an abelian
scheme, and `D` is a line bundle on `G`. Restricting any one of the given face
isomorphisms to the origin trivializes `e_G*D` over `S`, so `D` can be
rigidified at the origin. Proposition 2.6(i) then gives `D` a cubical
structure, which is a trivialization over `G ×_S G ×_S G` of the seven-term
line bundle of formula (2.4.1):

```text
𝒟₃(D)_(x,y,z) = D_(x+y+z) ⊗ D_(x+y)^(-1) ⊗ D_(x+z)^(-1) ⊗ D_(y+z)^(-1)
                  ⊗ D_x ⊗ D_y ⊗ D_z.
```

Now pull this trivialization back along

```text
A ×_S B ×_S C → G ×_S G ×_S G,   (a,b,c) ↦ ((a,0,0),(0,b,0),(0,0,c)).
```

The term `D_(x+y+z)` becomes `D` itself. The three pair-sum terms become the
pullbacks of `D` restricted to `(a,b,0)`, `(a,0,c)` and `(0,b,c)`. These are
trivial by the third, second and first face hypotheses, so their inverses are
trivial too. Each single-coordinate term, at `(a,0,0)`, `(0,b,0)` or
`(0,0,c)`, factors through one of the same faces and is trivial as well. The
pulled-back cubical trivialization therefore gives an isomorphism between `D`
and the structure sheaf. The argument only uses that the face isomorphisms
exist.

This is mathematical provenance and an informal derivation. The product
abelian-scheme structure on `G` is used only in this explanation, and no
product construction is needed to state the proposition. This unit does not
build that structure in Lean, implement the cubical identity, or prove any
step of the derivation. The formal proof is a separate obligation.

## Direct provenance through Raynaud

Moret-Bailly's proof cites Michel Raynaud, *Faisceaux amples sur les schémas
en groupes et les espaces homogènes*, Lecture Notes in Mathematics 119 (1970),
corrected second printing (1986), Theorem IV.2.1. That theorem is also direct
provenance for independent factors. The complete 223-page volume is
registered as
`provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`,
with file
`literature/Raynaud - Faisceaux amples sur les schemas en groupes et les espaces homogenes, LNM 119 (1970).pdf`
and SHA-256
`29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`. The
locations used are:

- Theorem IV.2.1 and its proof, printed pp.60–61/PDF pp.64–65;
- the rigidification and its specialization to given sections, IV.1.1–1.2,
  printed pp.56–58/PDF pp.60–62;
- property (P), Definition II.3.1 and Remark II.3.2 b), printed p.30/PDF p.34;
- the correspondence-functor input, III.4.1–4.6, printed pp.49–55/PDF pp.53–59.

Theorem IV.2.1 takes three `S`-schemes `X¹`, `X²` and `X³` with three
hypotheses. (a) Every open and closed part of `X³ ×_S X³` that contains the
diagonal is the whole space; geometrically connected fibres of `X³` suffice.
(b) For `i = 1, 2`, `X^i` is flat, quasi-compact and quasi-separated over `S`,
and `f^i_*(O_{X^i}) = O_S` universally. (c) The unit section of
`Corr_S(X¹, X²)` is represented by an open and closed immersion. Under (b),
(c) holds when `X¹` and `X²` both satisfy (P). The conclusion is that every
invertible sheaf on `X¹ ×_S X² ×_S X³` satisfies the theorem of the cube in
the sense of IV.1.1.3.

Mathematically, `X¹ = A`, `X² = B` and `X³ = C` meet these hypotheses over any
base. A smooth morphism is flat and locally of finite presentation. A proper
morphism is quasi-compact and separated, so the structure morphisms are flat
and of finite presentation. Property (P) holds by taking the scheme itself as
the proper, flat, finitely presented compactification in II.3.1. The open
immersion is then the identity and the boundary is empty. Smooth proper
morphisms with geometrically connected fibres satisfy `f_*O = O_S`
universally. The third factor has geometrically connected fibres. So the
first alternative of IV.2.1 applies with no noetherian or reducedness
hypothesis on `S`.

By IV.1.2, the theorem of the cube for `D` implies that its cubical
rigidification `c(D, e₁, e₂, e₃)` along the three unit sections is trivial.
By IV.1.1.2 this rigidification is the alternating tensor product of the
pullbacks of `D` along the coordinate projectors `p_I = s_I ∘ π_I`, for
`I ⊂ {1,2,3}`. The term for `I = {1,2,3}` is `D`. For a proper subset `I`,
including `I = ∅`, the projector `p_I` factors through one of the three
faces, so that term is trivial under the face hypotheses. Hence the
rigidification is isomorphic to `D`, and `D` is trivial. Only isomorphism
classes are used, so the three given face isomorphisms need not agree on
their overlaps.

Raynaud's proof uses hypothesis (c) on the correspondence functor
`Corr_S(X¹, X²)`. It also uses the descent of an open and closed subscheme
along a faithfully flat, quasi-compact, submersive projection (EGA IV
2.3.12), and the triviality of suitably rigidified invertible sheaves (III.2.2
and III.2.3). Hypothesis (c) comes from Corollary III.4.6. Its proof reduces
to a noetherian base by limit arguments (II.3.3 and III.1.5) and then applies
Proposition III.4.5. That proposition uses formal unramifiedness (III.4.1),
infinitesimal neighbourhoods, coherent cohomology and cohomological flatness.
All of this is source material, and none of it is formalized in this unit.
Neither the Raynaud specialization nor the Moret-Bailly derivation is claimed
here as a Lean theorem.

No source-specific errata for either work were found in the project's
public notes or literature folders. The Raynaud file is the corrected second
printing.

## Formal status and the field boundary

This is a statement definition, not a proof. The file imports
`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement` only for
the `CubeFace` maps. It imports `Langlands.AbelianScheme.Basic` for
`AbelianScheme`. Neither import supplies a proof of this proposition.

`FieldCubeTrivialityStatement` quantifies only over spectra of fields. Even a
proof of it would not establish the present assertion over an arbitrary
quasi-separated base, and in particular not over a nonreduced base. This unit
does not use the inference that a line bundle trivial on every geometric
fibre is pulled back from the base. Over a nonreduced base that inference is
false in general. Bridging from fibres to the relative statement is
separate geometric proof work.

The consumer is
`Langlands.AbelianScheme.rigidifiedClasses_eq_of_ordinaryCubeTriviality` in
`Langlands.AlgebraicGeometry.Picard.RelativeCubeDualComparison`. Its
`triviality` hypothesis has the same body as this proposition for one fixed
`S`, `A`, `B` and `C`, without the quasi-separatedness instance. That
hypothesis can be supplied from a proof of this statement once the base is
quasi-separated. Stating the criterion does not complete the parent theorem.
