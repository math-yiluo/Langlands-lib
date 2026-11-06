# Supercuspidal coefficient norms on the full central quotient

Authors: Worker 1678 and Worker 1721. Module
`Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. The module defines the
proposition
`SupercuspidalUnitaryCoefficientCompactSupportStatement.{u,v} : Prop`.
It does not assume or prove it.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.2.1, printed pp.137–139 / PDF pp.143–145, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The definition in VI.2.1 calls a smooth representation `(π, V)` of `G`
supercuspidal if `r_P^G(V) = 0` for every proper parabolic subgroup `P = MN` of
`G`. The theorem in VI.2.1 says that, for a smooth representation `(π, V)` of
`G`, the following are equivalent: (a) `(π, V)` is supercuspidal; (b) the matrix
coefficients of `(π, V)` have compact support modulo the center `Z(G)`; (c) the
restriction of `(π, V)` to `⁰G` is compact. This module states one consequence
of the implication (a) ⇒ (b), whose proof is on printed pp.138–139. In the proof
of (b) ⇒ (c), "support compact modulo `Z(G)`" means that the image in `G/Z(G)`
of the support of the coefficient is compact. By V.2.1 (printed p.104 / PDF
p.110), Renard's `Z(G)` is the group of `F`-points of the center of the
algebraic group.

## Statement

The binders are the same as in the published
`SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u,v}` (module
`MaximalLeviReducibilityUnitaryInputs`), up to its final two lines. The statement
quantifies over:

- a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local
  field of any characteristic;
- a group scheme `H` over `Spec k` with `hH : IsConnectedReductive H`;
- the instance `hH.isAffineHom` and the canonical topology
  `RationalPointFamily.pointTopology` on `rationalPoints H`, with the hypotheses
  `[LocallyCompactSpace (rationalPoints H)]` and
  `[NonarchimedeanGroup (rationalPoints H)]` for that topology;
- a smooth complex representation `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H)`.
  The carrier universe `v` is independent of the field universe `u`.

It assumes `ρ.IsIrreducible` and the supercuspidality hypothesis below. Then, for
every `c : UnitaryCentralCharacter ρ.representation`, every
`ℓ : SmoothDual ρ.representation` and every vector `v : ρ`, it concludes

`HasCompactSupport (c.coefficientNorm ℓ.1 v)`.

### Supercuspidality

The hypothesis says: for all group schemes `P' M' U'` over `Spec k`, every
`p' : P' ⟶ H` with `IsParabolicSubgroup p'`, every rational Levi `l' : M' ⟶ P'`
with `IsRationalLeviSubgroup l'`, every `r' : U' ⟶ P'` with
`LeviSubgroup.IsGeometricUnipotentRadical r'`, and every
`hmul' : IsIso (subgroupMultiplication l' r')`, if `¬ IsIso p'` then the
published normalized Jacquet module
`(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ` is a subsingleton, that is,
zero. This is Renard's definition with every proper actual rational parabolic,
its rational Levi and its matching unipotent radical. The condition `¬ IsIso p'`
expresses that the parabolic is proper. Renard's `r_P^G` is the normalized
Jacquet functor; the normalization twists by a character and does not change
whether the module vanishes.

### The conclusion

`UnitaryCentralCharacter` (module `MatrixCoefficient.ModuloCenter`) is a datum:
a character of the abstract center `Subgroup.center (rationalPoints H)` with
values in `ℂˣ`, with open kernel and absolute value one, through which the
center acts by scalars. `SmoothDual ρ.representation` is the space of smooth
vectors of the algebraic dual, Renard's `Ṽ`; `ℓ.1` is the underlying linear
functional.

`c.coefficientNorm ℓ.1 v` is the function
`rationalPoints H ⧸ Subgroup.center (rationalPoints H) → ℝ` sending the class of
`g` to `‖ℓ (ρ g v)‖`, the absolute value of the matrix coefficient. It is well
defined because the center acts by scalars of absolute value one
(`UnitaryCentralCharacter.norm_matrixCoefficient_mul_center`), and it does not
depend on `c` (`UnitaryCentralCharacter.coefficientNorm_eq`). The quotient
carries the quotient topology of `RationalPointFamily.pointTopology`.
`HasCompactSupport` asks that the closure of the set where this function is
nonzero be compact.

## Relation to the source

The statement is implied by Renard's (a) ⇒ (b), and it specializes that
theorem:

- **Irreducibility.** Renard's theorem holds for every smooth representation.
  The statement adds `ρ.IsIrreducible`, which is the hypothesis of the
  consumer `SupercuspidalUnitaryCentralCharacterUnitarizableStatement`.
- **Unitary central character.** The conclusion is quantified over
  `UnitaryCentralCharacter` data. If no such datum exists, the conclusion holds
  vacuously. Renard's theorem needs no central character.
- **Norm on the central quotient.** Renard states compactness of the support
  modulo `Z(G)`. The statement uses the norm of the coefficient descended to the
  quotient by the full abstract center of the rational point group. This is a
  derived formulation, not Renard's wording. It follows from (b) as follows. A
  coefficient of a smooth vector against a smooth functional is locally
  constant, so the set `S = {g | ℓ (ρ g v) ≠ 0}` is open and closed in `G`. It
  is stable under the abstract center, because the center acts by scalars of
  absolute value one. Its image in the quotient by the abstract center is
  therefore open and closed, and it is the set where `c.coefficientNorm ℓ.1 v`
  is nonzero; so this image is its own closure. The abstract center contains
  Renard's `Z(G)` (the `F`-points of the center commute with all of `G`). So
  this image is the image, under the continuous map
  `G/Z(G) → G ⧸ Subgroup.center G`, of the image of `S` in `G/Z(G)`, which is
  compact by (b). Hence it is compact.

So the Lean statement claims no more than Renard's theorem. The comparison
above is part of the proof obligation of this statement; it is not proved here.

## What is not assumed

No structural theorem, chosen root datum, standard parabolic, special maximal
compact subgroup, Cartan decomposition, Iwahori decomposition, admissibility,
finite dimension, finite length or other representation-theoretic premise
appears in the statement. Supercuspidality is tested against every proper actual
rational parabolic, not only standard ones. The local-compactness and
nonarchimedean-group instances of the rational point group are hypotheses, as in
the consumer statement.

## Renard's proof and the proof obligation

Renard proves (a) ⇒ (b) by contraposition. If a coefficient `φ_{v,λ}` does not
have compact support modulo the center, the Cartan decomposition (V.5.1) gives
elements `t_n` of the positive cone and a simple root `α` with
`|α(t_n)|_F → 0` (VI.2.1.1) such that the support meets `K₀ f t_n K₀` for every
`n`. Choosing a compact open subgroup `K` with an Iwahori decomposition along the
maximal standard parabolic `P_α`, he shows that `v₁ = π(f k₂) v` is not in
`V(N)`, so the Jacquet module of `V` along `P_α` is nonzero.

A proof of this proposition at its stated scope must supply the structural inputs
(Cartan decomposition, Iwahori decompositions, comparison of actual parabolics
with standard ones) and the comparisons with the represented-parabolic interface
above. The published theorem
`Langlands.Aubert.General.rationalCuspidalCompactRestriction` concerns
Renard's condition (c): compact coefficients after restriction to the common
norm kernel. It assumes cuspidality only along the standard parabolics of a
chosen maximal split torus and generic cocharacter, together with chosen
apartment, special compact subgroup and Cartan-covering premises. It does not
by itself discharge this statement.
