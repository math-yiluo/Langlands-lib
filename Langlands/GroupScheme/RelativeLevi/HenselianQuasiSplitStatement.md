# Statement: reductive groups over henselian local rings with finite residue field

Worker 75.

`Langlands.GroupScheme.HenselianFiniteResidueQuasiSplitStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`RelativeLevi.Borel`](Borel.md), for `IsRelativeQuasiSplit`;
- [`Reductive.FibrewiseRootDatum`](../Reductive/FibrewiseRootDatum.md), for
  `IsFibrewiseRootDatumOf`. Through its imports this also supplies
  `splitTorus.exponentWeightSpace`
  ([`Torus.RelativeAdjointWeights`](../Torus/RelativeAdjointWeights.md));
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`;
- Mathlib's `RingTheory.Henselian`, for `HenselianLocalRing`, and
  `RingTheory.Etale.Basic`, for `Algebra.Etale`.

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u` with instances `HenselianLocalRing R` and
  `Finite (IsLocalRing.ResidueField R)`. `HenselianLocalRing R` is Mathlib's class of
  local rings satisfying Hensel's lemma: a monic polynomial with a simple root modulo the
  maximal ideal has a root in `R` lifting it. The second instance says that the residue
  field of `R` is finite;
- every group scheme `G : GroupScheme (Spec R)` with a proof `hG : IsReductive G`
  ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine over `Spec R`,
  and its geometric fibres are connected reductive groups. The field `hG.isAffineHom`
  supplies the instance `IsAffineHom G.X.hom` used below. It is not an extra
  hypothesis.

The conclusion is a conjunction of two parts.

1. `IsRelativeQuasiSplit G` ([`RelativeLevi.Borel`](Borel.md)): `G` is reductive and has
   a Borel subgroup `i : B ⟶ G` over `Spec R` in the sense of `IsRelativeBorelSubgroup`.
2. There exist a commutative ring `R' : Type u` with `IsLocalRing R'` and an `R`-algebra
   structure on `R'` such that `R'` is étale (`Algebra.Etale R R'`) and finite
   (`Module.Finite R R'`) over `R`, and `G_{R'}` is split in the encoding of the published
   [`Reductive.EtaleLocalSplitStatement`](../Reductive/EtaleLocalSplitStatement.md).
   Write `G_{R'}` for `(GroupScheme.baseChange (Spec.algebraMap R R')).obj G`. Its
   structure morphism is the pullback of `G.X.hom`, so it is affine; the statement
   installs this instance with `inferInstanceAs`, and it is not an extra hypothesis
   either. The split data are a finite type `I : Type u`, a homomorphism
   `i : splitTorus (Spec R') I ⟶ G_{R'}` from the coordinate split torus `𝔾_m^I`, a type
   `J : Type u` and a Mathlib root datum `P : RootDatum J (I → ℤ) (I → ℤ)`, such that:
   1. `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed
      immersion;
   2. `IsFibrewiseMaximalTorus i`, with source the commutative group scheme
      `splitTorus.commGroupScheme (Spec R') I`: on every residue-field fibre of
      `Spec R'` the torus is a maximal torus (`IsMaximalTorus`);
   3. `IsFibrewiseRootDatumOf I G_{R'} i P`: `J` is finite, `P` is reduced, and for every
      field `k : Type u` with an `R'`-algebra structure the realization of `P` on the
      character and cocharacter lattices of `𝔾_m^I` over `k` is the root datum of the
      base change of `i` to `k`;
   4. for every `α : J` there is an `R'`-linear isomorphism
      `splitTorus.exponentWeightSpace I G_{R'} i (P.root α) ≃ₗ[R'] R'`: the root space of
      `Lie(G_{R'})` with root `P.root α` is free of rank one over `R'`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Corollary 5.2.14, p.159: "Let G be a reductive group over a henselian local ring R with
  finite residue field. Then G is quasi-split and it becomes split over a finite étale
  extension of R."
- Proof of Corollary 5.2.14, p.159: "By [Bo91, 16.6] (or Exercise 6.5.6), the special
  fiber G_0 over the finite residue field k admits a Borel subgroup B_0. [...] Hence, B_0
  lifts to a Borel subgroup of G. [...] any k′-point must lift to an R′-point, where
  R → R′ is the local finite étale extension inducing the residual extension k′/k.
  Hence, Tor_{G/R}(R′) ≠ ∅, so G_{R′} contains an R′-torus that lifts the k′-split T′_0
  and hence is R′-split too (due to the henselian property of R′)."
- Definition 5.2.10, p.157: "A reductive group G → S is quasi-split over S if it admits a
  Borel subgroup scheme over S."
- Definition 5.1.1, p.136: a reductive `G` over a non-empty `S` is split if there is a
  maximal torus `T` with an isomorphism `T ≃ D_S(M)` for a finite free `ℤ`-module `M`
  such that (1) the nontrivial weights of `T` on `g` arise from elements of `M`, (2) each
  root space `g_a` is free of rank 1 over `O_S`, and (3) each coroot arises from an
  element of `M^∨`. The text after it: "conditions (1) and (3) are automatic when S is
  connected".

## Derivation from the source

The proposition is Corollary 5.2.14, with its terms translated as follows.

- **"Henselian local ring R with finite residue field".** This is the pair of instances
  `HenselianLocalRing R` and `Finite (IsLocalRing.ResidueField R)`. A reductive group
  over `R` is a group scheme over `Spec R` with `IsReductive`.
- **"G is quasi-split".** This is `IsRelativeQuasiSplit G`, the Library's transcription
  of Definition 5.2.10. Its first field repeats `IsReductive G`, which is already a
  hypothesis. Its module [`RelativeLevi.Borel`](Borel.md) explains why the fibres of a
  Borel subgroup are required to be Borel subgroups after base change to an algebraic
  closure. The proof in the source obtains `B_0` from [Bo91, 16.6], a Borel subgroup
  of `G_0` defined over the finite field `k`, which is a Borel subgroup in this sense.
- **"A finite étale extension of R".** This is an `R`-algebra `R'` with
  `Algebra.Etale R R'` and `Module.Finite R R'`. The statement also requires
  `IsLocalRing R'`, as in the proof, which uses "the local finite étale extension
  R → R′ inducing the residual extension k′/k". Requiring a local ring loses nothing:
  a finite algebra over a henselian local ring is a finite product of local rings, each
  of which is again finite étale over `R` when `R'` is, and splitness in the sense of
  Definition 5.1.1 is stable under base change to a factor (see the derivation in
  [`Reductive.EtaleLocalSplitStatement`](../Reductive/EtaleLocalSplitStatement.md)). A
  local ring is nonzero, so `R'` is a genuine extension and `Spec R'` is non-empty, as
  Definition 5.1.1 requires. Because `R'` is finite over `R`, its maximal ideal lies
  over the maximal ideal of `R`, so `R → R'` is a local homomorphism; the statement does
  not need to require this separately.
- **"It becomes split".** `G_{R'}` is split in the sense of Definition 5.1.1, encoded
  exactly as in [`Reductive.EtaleLocalSplitStatement`](../Reductive/EtaleLocalSplitStatement.md),
  whose derivation section explains each of the conditions 2.1–2.4 above: a basis of
  `M` puts the split torus in coordinates, conditions 2.1 and 2.2 encode the maximal
  torus, condition 2.3 encodes Definition 5.1.1(1) and (3) together with the root datum
  of Proposition 5.1.6, and condition 2.4 is Definition 5.1.1(2). The proof in the
  source produces an `R'`-split maximal torus. Since `Spec R'` is connected, conditions
  (1) and (3) of Definition 5.1.1 are then automatic, and since `R'` is local, every
  root space, a finitely generated projective `R'`-module of rank one, is free.

## Scope

All objects are in universe `u`, including `R'`, `I`, `J` and the fields in
`IsFibrewiseRootDatumOf`. The ring `R` need not be Noetherian, a domain or complete.
The two parts of the conclusion are independent: the Borel subgroup of part 1 is not
required to contain the split torus of part 2, and part 2 does not say that
`G_{R'}` is quasi-split with a Borel subgroup containing that torus.

## Not stated

- The remark after Corollary 5.2.14 (on valuation rings of non-archimedean local fields
  and Steinberg's theorem) is not stated.
- The existence of a Borel subgroup of a connected reductive group over a finite field,
  [Bo91, 16.6], used in the proof, is not stated here.

This module proves none of these assertions.
