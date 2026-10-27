# Relative cube detection for rigidified families on abelian schemes

`Langlands.AbelianScheme.RelativeRigidifiedCubeStatement` is a
`Prop`-valued definition in the module
`Langlands.AlgebraicGeometry.Picard.RelativeRigidifiedCubeStatement`.
It states a relative theorem-of-the-cube detection principle for the
Library's rigidified relative line-bundle classes. This module states the
principle only. It does not prove it, and no Library result currently
proves it without extra premises.

## Exact statement

The statement quantifies, in every universe `u`, over:

- a scheme `S : Scheme.{u}` with `QuasiSeparatedSpace S`;
- actual abelian schemes `A B C : AbelianScheme S`;
- two classes `q r : RigidifiedClasses A (B.X ⊗ C.X)`.

`AbelianScheme S` is the Library structure: a commutative group object
`X` in `Over S` whose structure morphism is smooth, proper and
geometrically connected. Its unit is the monoid unit of the group object.

Put `T = B.X ⊗ C.X`, the chosen cartesian monoidal product in `Over S`.
This is the chosen fibre product `B ×_S C`. The two axes are

| Name | Lean map | Domain | Coordinates in `B ×_S C` |
| --- | --- | --- | --- |
| `iB` | `CartesianMonoidalCategory.lift (𝟙 B.X) (1 : B.X ⟶ C.X)` | `B.X` | `(b, e_C)`, that is `(id, e_C)` |
| `iC` | `CartesianMonoidalCategory.lift (1 : C.X ⟶ B.X) (𝟙 C.X)` | `C.X` | `(e_B, c)`, that is `(e_B, id)` |

Here `1 : B.X ⟶ C.X` is the unit of the monoid of morphisms into the
group object `C.X`. By Mathlib's `MonObj.Hom.one_def` it is
`toUnit B.X ≫ η[C.X]`: the unique map to the terminal object
`𝟙_ (Over S) = Over.mk (𝟙 S)`, followed by the unit point of `C`. So it is
the structure morphism of `B` followed by the unit section `e_C`.
Likewise `1 : C.X ⟶ B.X` is the structure morphism of `C` followed by
`e_B`. `CartesianMonoidalCategory.lift` is the actual categorical pairing
into the chosen product.

The statement asserts the following. If

`classesPullback A.X.hom (unitSection A) (unitSection_comp A) iB q =
  classesPullback A.X.hom (unitSection A) (unitSection_comp A) iB r`

and

`classesPullback A.X.hom (unitSection A) (unitSection_comp A) iC q =
  classesPullback A.X.hom (unitSection A) (unitSection_comp A) iC r`,

then `q = r`. Here `classesPullback` is
`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.classesPullback`.
The first equality holds in `RigidifiedClasses A B.X` and the second in
`RigidifiedClasses A C.X`. The Lean source writes both axes inline,
exactly as above.

## The actual quotient and pullback

`RigidifiedClasses A U` is the published abbreviation
`RigidifiedLineBundle.Classes A.X.hom (unitSection A) (unitSection_comp A) U`.
It is
`Quotient (isIsomorphicSetoid (RigidifiedLineBundle.relative A.X.hom (unitSection A) (unitSection_comp A) U))`.

An object of `RigidifiedLineBundle.relative … U` is a sheaf of modules on
`U ×_S A` that is locally free of rank one. Here `U ×_S A` is
`(relativeSpace A.X.hom).obj U`, the chosen pullback of `A.X.hom` along
`U.hom`, with the parameter factor first. The object also carries a
rigidification. This is an isomorphism `O_U ≅ s_U^* L` along the section
`s_U = (id, U.hom ≫ unitSection A)`, that is, along the unit of `A`.

Two objects have the same class exactly when some module isomorphism
between them is compatible with the two rigidifications. Thus `q = r`
asserts that a rigidification-compatible isomorphism exists between
representing families over the whole of `T`. An isomorphism of the
underlying line bundles alone is not enough. The statement uses no
replacement quotient, no Picard group or group law on classes, and no
pointwise or fibrewise condition.

`classesPullback h` is `Quotient.map` of the object function of the actual
functor `RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
(unitSection_comp A) h`. For `h : V ⟶ U`, this functor pulls a family back
along `(relativeSpace A.X.hom).map h`, the base change of `h` to the
relative spaces. It transports the rigidification along the compatible
section square. `classesPullback` is defined unconditionally. The
statement does not use the presheaf `classPresheaf`, whose functor laws
need the explicit coherence proposition.

## Scope and absent premises

- The base `S` is any quasi-separated scheme. It need not be noetherian,
  reduced, connected or affine. The quasi-separated hypothesis matches
  Lan's convention (see below). The original relative source allows an
  arbitrary base, so this hypothesis only narrows the scope.
- The three abelian schemes `A`, `B`, `C` are arbitrary and independent.
  They need not be projective or polarized, and they need not be equal.
- The classes `q` and `r` are arbitrary. They need not be Picard-zero,
  algebraically trivial, translation-invariant or symmetric.
- The conclusion concerns the full families on `T ×_S A`, which is the
  threefold product `B ×_S C ×_S A` up to the chosen-product identifications.
  It is not a statement about fibres, reduced subschemes or field-valued
  points.
- The statement has no premises beyond `S`, its quasi-separatedness, and
  `A`, `B`, `C`. In particular, it does not assume
  `pullbackTensorComparisonIsIsoStatement`, the coherence proposition
  for rigidified pullbacks, representability of a Picard functor,
  `HasDualScheme` or another dual-existence input, Picard-zero
  membership, a rigidity lemma, a seesaw principle, the square theorem,
  or any field or relative cube criterion.

## Cube interpretation

Informally, let `D` be the "difference" of representatives of `q` and
`r`. It is a rigidified line bundle on the relative space over `T`,
identified with `A ×_S B ×_S C`. The rigidification of the family along
the unit of `A` makes `D` trivial on the face `{e_A} × B × C`, compatibly
with that rigidification. The hypothesis along `iB` gives triviality on
the face `A × B × {e_C}`. The hypothesis along `iC` gives triviality on the
face `A × {e_B} × C`. Detection of `q = r` is therefore the
compatible-isomorphism-class form of the three-face cube criterion: the
rigidification accounts for one face, and the two axis restrictions
account for the other two.

The Lean statement is phrased as equality detection for two classes,
not as triviality of a single class. This avoids the tensor products and
inverses of rigidified classes. The Library's group structure on these
classes needs `pullbackTensorComparisonIsIsoStatement`, which is not a
premise here.

## Original sources and derived provenance

The exact quotient formulation above is derived for the Library. No cited
source states it verbatim. The following original passages were read.

1. Laurent Moret-Bailly, *Pinceaux de variétés abéliennes*, Astérisque
   129 (1985), Numdam digitization. It is registered as
   `moret-bailly-1985-pinceaux-asterisque-129`, SHA-256
   `b8d62fdd2e1d85ff1e688e62bd212aede20e044c373a7613ef01ddc52f02022a`.
   - Introduction, printed p.5/PDF p.8, states the convention that every
     invertible sheaf on a group scheme is rigidified along the unit
     section.
   - Chapter I, (2.4.1), printed p.18/PDF p.21, defines for a rigidified
     torsor `L` on a commutative group `A` the sheaf
     `Θ₃(L)_{x,y,z} = L_{x+y+z} ⊗ L_{x+y}⁻¹ ⊗ L_{x+z}⁻¹ ⊗ L_{y+z}⁻¹ ⊗ L_x ⊗ L_y ⊗ L_z`.
     Definition 2.4.5, printed p.19/PDF p.22, defines cubical structures.
   - Chapter I, 2.6, printed pp.21–22/PDF pp.24–25, takes `S` to be an
     arbitrary scheme and `G = G_m` on the big fppf site. It identifies
     `G_m`-torsors with invertible sheaves. Proposition 2.6, case (i),
     takes `A` to be an `S`-abelian scheme and states that the forgetful
     functor from cubical `G_m`-torsors to `G_m`-torsors rigidified at the
     origin is an equivalence. Its proof invokes the theorem of the cube in
     the form: for a rigidified `L` on `A`, `Θ₃(L)` on `A³` comes from an
     invertible sheaf on `S`. Because `Θ₃(L)` inherits the rigidification,
     it is then trivial, with a unique trivialization compatible with the
     rigidification. The proof cites M. Raynaud, *Faisceaux amples sur les
     schémas en groupes et les espaces homogènes*, Lecture Notes in Math.
     119, IV.2.1. That book was not available and was not consulted, so
     the relative theorem is cited here through Moret-Bailly's use of it.
     Case (i), for abelian schemes, places no hypothesis on `S`. Case (ii)
     concerns other smooth groups and assumes `S` normal.
2. J. S. Milne, *Abelian Varieties*, author's corrected version of
   January 2, 2022 of the 1986 *Arithmetic Geometry* chapter. It is
   registered as `milne-abelian-varieties-1986-author-2022`, SHA-256
   `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
   Theorem 6.1, printed/PDF p.8, is the three-face form over a field.
   For complete varieties `U`, `V`, `W` with rational base points, an
   invertible sheaf on `U × V × W` is trivial if its restrictions to the
   three faces through the base points are trivial. The registered errata
   page `milne-abelian-varieties-1986-errata-2026-10-25` lists no change
   to Theorem 6.1. Over a field, this is the shape of the present
   statement with three different factors.
3. Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
   varieties*, thesis revised March 14, 2021. It is registered as
   `lan-2008-pel-thesis-revision-2021`, SHA-256
   `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
   This source is behind the consumer target
   `MumfordBundleParameterAdditivityStatement`. Construction 1.3.2.7,
   printed p.75/PDF p.103, forms `D₂(L)` and its classifying morphism
   `λ_L`, using Corollary 1.3.1.6, printed pp.70–71/PDF pp.98–99. The
   proof of Proposition 1.3.2.14, printed p.76/PDF p.104, refers to the
   theorem of the cube only informally. Lan states no relative cube
   theorem in these passages, and none is attributed to Lan here. The
   convention on PDF p.26 takes schemes to be quasi-separated, which is
   why the base hypothesis is retained. The author's errata
   `lan-2008-pel-thesis-errata-2021`, SHA-256
   `18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
   PDF pp.1 and 8–9, were checked. They contain no correction to
   Construction 1.3.2.7 or Corollary 1.3.1.6.

Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, Chapter 6, was also
consulted. Its §1 rigidity results assume locally noetherian schemes and
do not state the cube theorem, so it is not a source for this statement.

The following derivation explains why the statement is the expected
relative consequence. It is not a formal proof. Let `X = A ×_S B ×_S C`,
an abelian scheme over `S`. Let `D` be the rigidified difference of
representatives of `q` and `r`, transported to `X`. Pull Moret-Bailly's
`Θ₃(D)` back along `X → X³`, `(a,b,c) ↦ ((a,0,0),(0,b,0),(0,0,c))`. The
result is

`D ⊗ D_{ab0}⁻¹ ⊗ D_{a0c}⁻¹ ⊗ D_{0bc}⁻¹ ⊗ D_{a00} ⊗ D_{0b0} ⊗ D_{00c}`,

where `D_{ab0}` is the pullback along `(a,b,c) ↦ (a,b,0)`, and so on. The
two axis hypotheses make `D_{ab0}` and `D_{a0c}` trivial, and hence also
`D_{a00}`. The rigidification makes `D_{0bc}`, `D_{0b0}` and `D_{00c}`
trivial. So `D` comes from an invertible sheaf on `S`, and restriction
to the unit section shows that this sheaf is trivial. A trivialization of
`D` can then be corrected by a unit on `T` so that it respects the
rigidification along `e_A`. That gives `q = r`.

A Lean proof must supply what this sketch uses: rigidified tensor
products and inverses, or another way to form the difference;
identification of the Library's relative spaces with the iterated fibre
products; the relative cube theorem itself over a non-noetherian base;
and the rigidification bookkeeping. None of these is an input to the
statement.

## Relation to existing Library results

The Library lemma
`Langlands.AbelianScheme.rigidifiedClasses_eq_of_ordinaryCubeTriviality`
in `RelativeCubeDualComparison` has the same conclusion. It uses the same
two axis maps and the same hypotheses `hB` and `hC`. It also takes two
further premises: `pullbackTensorComparisonIsIsoStatement` and an ordinary
three-face cube criterion for line bundles on `A.X ⨯ (B.X ⨯ C.X)`.
Given those two premises for every quasi-separated `S` and every `A`,
`B`, `C`, that lemma implies the present statement. The present statement
does not assume either premise. `FieldCubeTrivialityStatement` covers only
spectra of fields and does not give the relative criterion over
nonreduced bases. `MumfordParameterCubeReduction` reduces the Mumford
parameter-additivity target to an ordinary self-product cube criterion,
which is a different and explicit premise.

This file is a statement. The theorem `RelativeRigidifiedCubeStatement`
remains unproved here, and its proof is a separate obligation.
