# Statement: split and quasi-split special fibres over a henselian DVR

Worker 75.

`Langlands.GroupScheme.HenselianDiscreteSpecialFibreSplitStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It uses:

- `IsReductive` from [`Reductive.Basic`](Basic.md): a group scheme over a base `S` that
  is smooth and affine over `S`, and whose geometric fibres are connected reductive
  groups.
- `IsQuasiSplit` from [`Reductive.QuasiSplit`](QuasiSplit.md): for a group over a field,
  `IsConnectedReductive` together with a field-defined subgroup `i : B ⟶ G` with
  `IsGeometricBorelSubgroup i`, that is, a Borel subgroup over the field whose base
  change to an algebraic closure is again a Borel subgroup.
- `IsSplitTorus` from [`Torus.Split`](../Torus/Split.md): a group scheme isomorphic to
  `splitTorus S I`, a finite product of copies of `𝔾_m` over `S`.
- `IsMaximalTorus` from [`Torus.Maximal`](../Torus/Maximal.md): for a homomorphism
  `i : T ⟶ G` of group schemes over a field, `T` is a torus, `i` is a closed subgroup,
  and `i` does not factor through a strictly larger closed torus of `G`.
- `GroupScheme.baseChange f` from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md): the pullback of
  group schemes along a morphism of base schemes `f`.
- Mathlib's `IsDiscreteValuationRing`, `HenselianLocalRing`, `IsFractionRing` and
  `IsLocalRing.ResidueField`.

## Statement

Let `R : Type u` be a domain that is a discrete valuation ring and a henselian local
ring, `K : Type u` a fraction field of `R` (`IsFractionRing R K`), and `G` a group scheme
over `Spec R` with `IsReductive G`. Write `G₀` for the base change of `G` along
`Spec.algebraMap R (IsLocalRing.ResidueField R)` (the special fibre) and `G_K` for the
base change of `G` along `Spec.algebraMap R K` (the generic fibre). Then:

1. **Quasi-split.** If `IsQuasiSplit G₀`, then `IsQuasiSplit G_K`.
2. **Split.** If there are a commutative group scheme `T` over the residue field and
   `i : T ⟶ G₀` with `IsSplitTorus T` and `IsMaximalTorus i`, then there are a
   commutative group scheme `T'` over `K` and `i' : T' ⟶ G_K` with `IsSplitTorus T'` and
   `IsMaximalTorus i'`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Exercise 5.5.3, p.182: "Let R be Dedekind with fraction field K, and G a connected
  reductive K-group. A reductive R-group scheme is quasi-split if it has a Borel
  subgroup over the base (see Definition 5.2.10). […] (ii) Assume R is a henselian
  (e.g., complete) discrete valuation ring and that G = 𝒢_K for a reductive R-group 𝒢.
  Using Bor_{𝒢/R}, prove that if the special fiber 𝒢_0 is split (resp. quasi-split)
  then so is G over K. What if R is not assumed to be henselian?" The omitted passage
  is part (i).
- Definition 5.1.1, p.136: a reductive group `G` over a non-empty scheme `S` is split if
  it has a maximal torus `T ≃ D_S(M)` for a finite free `ℤ`-module `M` such that the
  nontrivial weights on `𝔤` arise from `M`, each root space is free of rank 1, and each
  coroot arises from `M^∨`. Conrad notes that the conditions on weights and coroots are
  automatic when `S` is connected, and the text before the definition notes that root
  spaces over a field are free of rank 1.
- Definition 5.2.10, p.157: "A reductive group G → S is quasi-split over S if it admits
  a Borel subgroup scheme over S."

Conrad leaves the exercise to the reader; the notes contain no proof of it. The hint
is to lift a Borel subgroup (or a split maximal torus) of `𝒢_0` to `𝒢` using the smooth
scheme `Bor_{𝒢/R}` (or `Tor_{𝒢/R}`) and the henselian property of `R`, and then pass to
the generic fibre. This is explanation only.

## Derivation from the source

- **The data.** Conrad's `G` over `K` is given as `𝒢_K` for a reductive `R`-group `𝒢`.
  The statement quantifies over `𝒢` (named `G` in Lean) and concludes about its generic
  fibre `G_K`, the actual base change along `Spec K → Spec R`. The special fibre `𝒢_0`
  is the base change along `Spec κ → Spec R` for the residue field `κ` of `R`.
- **Henselian discrete valuation ring.** This is `IsDiscreteValuationRing R` with
  `HenselianLocalRing R`; `IsDomain R` is required by Mathlib's
  `IsDiscreteValuationRing`. Complete discrete valuation rings are included.
- **Quasi-split over a field.** By Definition 5.2.10 over the spectrum of a field, this
  is having a Borel subgroup over that field. Over a field that need not be
  algebraically closed, a Borel subgroup is one that becomes a Borel subgroup over an
  algebraic closure, which is `IsGeometricBorelSubgroup`. `IsQuasiSplit` packages this
  with `IsConnectedReductive`, which holds for both fibres of a reductive group scheme.
- **Split over a field.** The spectrum of a field is connected, so conditions (1) and (3)
  of Definition 5.1.1 hold automatically, and condition (2) holds because the root spaces
  are vector spaces of dimension 1 over the field. Split therefore means having a
  maximal torus that is a split torus. The statement encodes this as `IsSplitTorus T`
  together with `IsMaximalTorus i`. `IsMaximalTorus` asks for maximality among tori
  over the given field. A maximal torus over a field remains maximal over every
  extension field (Conrad, Remark A.1.2, p.267), so this agrees with the geometric
  notion of maximal torus used in Definition 5.1.1.

## Scope

The proposition does not state:

- the question "What if R is not assumed to be henselian?";
- parts (i) and (iii) of Exercise 5.5.3, which are separate statements;
- the intermediate claims that `𝒢` itself is split or quasi-split over `R`.

## Relation to the Library

- `HenselianFiniteResidueQuasiSplitStatement` in
  [`RelativeLevi.HenselianQuasiSplitStatement`](../RelativeLevi/HenselianQuasiSplitStatement.md)
  states that a reductive group over a henselian local ring with finite residue field is
  quasi-split over that ring, a related lifting statement.
- `StrictHenselianSplitMaximalTorusStatement` in
  [`Torus.StrictHenselianMaximalStatement`](../Torus/StrictHenselianMaximalStatement.md)
  gives split maximal tori over strictly henselian local rings, again by a lifting
  argument from the special fibre.
- `HenselianDiscreteQuasiSplitStatement` in
  [`Rational.HenselianDiscreteQuasiSplitStatement`](../Rational/HenselianDiscreteQuasiSplitStatement.md)
  concerns arbitrary connected reductive groups over henselian discretely valued fields
  with algebraically closed residue field, and does not assume a reductive model.

This module proves none of these relations.
