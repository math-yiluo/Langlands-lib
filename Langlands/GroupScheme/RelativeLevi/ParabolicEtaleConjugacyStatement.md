# Statement: parabolic subgroups conjugate at a point are conjugate étale-locally

Worker 75.

`Langlands.GroupScheme.RelativeParabolicEtaleLocalConjugacyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md), for
`IsRelativeParabolicSubgroup` and `RelativeLevi.residueFiberHom`,
[`InnerAutomorphism`](../InnerAutomorphism.md), for `GroupScheme.innerIso`, and
Mathlib's `AlgebraicGeometry.Morphisms.Etale`, for `Etale`.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- group schemes `G P Q : GroupScheme S`;
- homomorphisms `i : P ⟶ G` and `j : Q ⟶ G`;
- a point `s : S`.

It has four hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and
   affine over `S`, and its geometric fibres are connected reductive groups.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth
   and affine over `S`, `i` is a monomorphism of `S`-schemes, and every residue fibre
   of `i` satisfies the field predicate `IsParabolicSubgroup`.
3. `IsRelativeParabolicSubgroup j`, the same for `j`.
4. **Conjugacy at `s`.** Write `G_s` for the base change of `G` along
   `S.fromSpecResidueField s : Spec κ(s) ⟶ S`, and `i_s`, `j_s` for
   `RelativeLevi.residueFiberHom i s` and `RelativeLevi.residueFiberHom j s`. There is
   a point `g : Over.mk (𝟙 (Spec κ(s))) ⟶ G_s.X`, that is `g ∈ G(κ(s))`, such that

       SubgroupFunctor.range (i_s ≫ (G_s.innerIso g).hom) = SubgroupFunctor.range j_s.

   `G_s.innerIso g` is conjugation by `g`, so the left side is the subgroup functor
   `T ↦ g P_s(T) g⁻¹` of `G_s`. The hypothesis says `g P_s g⁻¹ = Q_s`, with equality of
   images tested on every scheme over `Spec κ(s)`.

The conclusion is: there exist a scheme `U : Scheme.{u}` and a morphism `f : U ⟶ S`
such that

- `f` is étale (`Etale f`);
- some point `x` of `U` satisfies `f.base x = s`;
- for the base change `G_U = (GroupScheme.baseChange f).obj G`, there is a point
  `g : Over.mk (𝟙 U) ⟶ G_U.X`, that is `g ∈ G(U)`, such that

      SubgroupFunctor.range ((GroupScheme.baseChange f).map i ≫ (G_U.innerIso g).hom)
        = SubgroupFunctor.range ((GroupScheme.baseChange f).map j),

  that is, `g P_U g⁻¹ = Q_U` on every scheme over `U`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Corollary 5.2.7(1), p.155: "Let G → S be a reductive group, s ∈ S a point, and P, Q ⊂
  G parabolic subgroups. If P_s is conjugate to Q_s for some s ∈ S then there exists an
  étale neighborhood U of (S, s) such that P_U is G(U)-conjugate to Q_U."
- Proof of Corollary 5.2.7(1), p.155: "By hypothesis there exists g ∈ G(s) such that
  gP_s g⁻¹ = Q_s."
- Definition 5.2.1, p.151 (parabolic subgroups), and Definition 3.1.1, p.81 (reductive
  group schemes).

## Derivation from the source

The proposition is the first assertion of Corollary 5.2.7(1), with its terms translated
as follows.

- **"P_s is conjugate to Q_s".** The proof makes this precise as `gP_s g⁻¹ = Q_s` for a
  point `g ∈ G(s)` of the fibre over `κ(s)`. Hypothesis 4 states exactly this.
- **"Étale neighborhood U of (S, s)".** This is encoded as an étale morphism
  `f : U ⟶ S` whose image contains `s`. The proof passes to étale neighbourhoods that
  split maximal tori, which in general requires a finite separable extension of the
  residue field. The source's étale neighbourhoods therefore need not have trivial
  residue field extension at the point over `s`, and the encoding does not require one.
  Shrinking `U` to an affine open neighbourhood of `x` does not change the statement,
  so `U` is allowed to be any scheme.
- **"P_U is G(U)-conjugate to Q_U".** There is `g ∈ G(U)` with `gP_U g⁻¹ = Q_U`.
  Subgroups are compared through their images as subgroup functors
  (`SubgroupFunctor.range`), the convention used throughout the relative Levi
  statements of the Library. Because `i` and `j` are monomorphisms, this is equality of
  the subgroups `P_U` and `Q_U` of `G_U`.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected. No maximal torus, splitting or cocharacter
over `S` is assumed.

## Not stated

- The second sentence of Corollary 5.2.7(1), "if `P` and `Q` are conjugate over all
  geometric points of `S` then they are conjugate étale-locally on `S`", is not
  stated. It concerns conjugacy over geometric points, whereas hypothesis 4 asks for
  conjugacy over `κ(s)`.
- Corollary 5.2.7(2), on containment of Lie algebras, is not stated.
