# Structural premises of Proposition II.4.5 at the joint special compact subgroup

Author: Worker 762, task `79ac4c17-fe39-4c1c-bb7f-f0d531569c87` (Task 7438, revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises`,
namespace `Langlands.HarishChandraSchwartz`.

## Purpose

The published statement `RationalConstantTermEstimateStatement` (module `RationalConstantTerm`,
Waldspurger's Proposition II.4.5 on actual rational points) takes as premises a compact open
subgroup `K0` of `G(F)` with

- Renard's simultaneous standard basis `SimultaneousStandardBasisAt i ν K0`,
- the finite Cartan covering of `G(F)`, `Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0`,
- the finite Cartan covering of the standard Levi, `StandardLeviCartanCovering F i ν J K0`,

and a compact open `K` with the Iwasawa factorizations `G(F) = P₀(F) K` and
`M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`. This module proves that all of these premises hold with
`K = K0` for one compact open `K0`, assuming the published proposition
`JointSpecialCompactBasisExistenceStatement` (module `BruhatTits.SpecialCompact.JointBasisStatement`).
It proves no part of that proposition: the joint statement is an explicit hypothesis of the
final theorem.

All results are theorems. None introduces a new definition or proposition.

## Setting

`F` is a nonarchimedean local field (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`) in universe `u`. `G` is a group scheme over `Spec F` with
`[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, `S` a commutative group scheme over
`Spec F`, `i : S.toGrp ⟶ G` and `ν : cocharacterLattice S`. `P₀(F) = standardParabolicPoints i ν ∅`,
`M_J(F) = standardLeviPoints i ν J`, and `Δ = simpleRelativeRoots i ν`. `IsIwasawaPair P K` is the
Library's predicate "every `g` is `p k` with `p ∈ P`, `k ∈ K`" (module `Spherical`).

## Results

### `standardLeviCartanCovering_of_compatibility`

Hypotheses: `D : KPApartmentData i (localFieldOrder F)`, `x : D.Apartment`, a group scheme `Z`
with `j : Z ⟶ G` and `s : S.toGrp ⟶ Z`, `h : Function.Bijective (restrictionEvaluation s)`,
`[Mono i.hom.hom.left]`, `hrep : (torusCentralizer i).IsRepresentedBy j`, `hsj : s ≫ j = i`,
`hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j`, and `hJ : J ⊆ Δ`.

Conclusion: `StandardLeviCartanCovering F i ν J (D.specialCompactSubgroup x)`, that is, a finite
set `F₀` of torus-centralizer points such that every `m ∈ M_J(F)` is `k₁ f a k₂` with
`k₁, k₂ ∈ K0 ∩ M_J(F)` (`K0 = D.specialCompactSubgroup x`), `f ∈ F₀` and
`a ∈ CocharacterUniformizer.CAplus F S J`.

Proof. The compatibility clause at `J` gives a closed `jM : Z ⟶ M_J` with
`jM ≫ Standard.leviHom i ν J = j`, the Levi coverage and classification `hc` for the compact
`D.specialCompactLeviSubgroup ν J x` (the preimage of `K0` in the Levi scheme), and the Levi
lattice conclusions. Their finite positive product cover gives a finite set `Fcover ⊆ Z(F)` such
that every dominant valuation class is the valuation of some `c f` with `f ∈ Fcover` and
`c` in the positive cocharacter-uniformizer set `C0Plus` for the Levi positive roots. `F₀` is the
image of `Fcover` in `centralizerPoints i` under `j`. For `m ∈ M_J(F)` choose its preimage `m'`
in the Levi scheme. Coverage gives a dominant `z ∈ Z(F)` with `m'` in the double coset of `jM(z)`.
The cover gives `t = c f` with the same valuation as `z`, so `t z⁻¹` lies in the kernel of the
valuation `Z(F)^1`. By classification `jM(t)` and `jM(z)` give the same double coset, so
`m' = k₁ jM(c f) k₂`. Here `c = s(a)` with `a = uniformizerSection S (ofAdd χ)` for a cocharacter
`χ` that is nonnegative on the Levi positive roots, which contain `J`
(`mem_positiveRelativeRoots_leviTorusHom`). Hence `|α(a)|_F = q^{-⟨α, χ⟩} ≤ 1` for `α ∈ J`
(`characterNorm_latticeSection`), so `a ∈ C_A^+(J)`. Mapping to `G(F)` gives
`m = k₁ i(a) j(f) k₂`. Since `j(f)` centralizes the torus, `i(a)` and `j(f)` commute, so
`m = k₁ j(f) i(a) k₂`.

The argument is the ambient one of the Library's `rationalPositiveCartanCover`
(module `RationalPositiveCartanCoverProof`), carried out in `M_J`.

### `isIwasawaPair_standardLevi_of_leviProducts`

Hypotheses: `hG : IsConnectedReductive G`, `hi : IsMaximalSplitTorus i`,
`hν : IsGenericCocharacter i ν`, `hJ : J ⊆ Δ`, a subgroup `K` of `G(F)`, and
`hP : BruhatTits.Iwasawa.ParabolicPointProductFamily (Standard.leviTorusHom i ν J) ν
(leviSchemeCompact K i ν J)`, the actual parabolic product family of the Levi scheme at the
preimage `K ∩ M_J(F)`.

Conclusion: `IsIwasawaPair (P₀(F).subgroupOf M_J(F)) (K.subgroupOf M_J(F))`, i.e.
`M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`.

Proof. The product family at the empty index gives the factorization of the Levi scheme's points
by its minimal standard parabolic and `leviSchemeCompact K i ν J`
(`isIwasawaPair_of_pointProductEqualities`). It is transported to `M_J(F)` by the equivalence
`leviSchemePointsEquiv i ν J`. The Levi scheme's minimal parabolic corresponds to
`P₀(F) ∩ M_J(F)` (`mem_standardParabolicPoints_leviTorusHom_iff`, which uses `hG`, `hi`, `hν`,
`hJ`), and `leviSchemeCompact K i ν J` corresponds to `K ∩ M_J(F)` (`mem_leviSchemeCompact_iff`).

### `exists_constantTermPremises_of_joint`

Hypotheses: `hJoint : JointSpecialCompactBasisExistenceStatement.{u}`,
`hG : IsConnectedReductive G`, `hi : IsMaximalSplitTorus i`, `hν : IsGenericCocharacter i ν`.

Conclusion: there is a subgroup `K0` of `G(F)` with

- `IsOpen K0` and `IsCompact K0`;
- `IsIwasawaPair P₀(F) K0`, i.e. `G(F) = P₀(F) K0`;
- `SimultaneousStandardBasisAt i ν K0`;
- `Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0`;
- for every `J ⊆ Δ`: `StandardLeviCartanCovering F i ν J K0` and
  `IsIwasawaPair (P₀(F).subgroupOf M_J(F)) (K0.subgroupOf M_J(F))`.

Proof. Apply `hJoint` to `F, G, S, i, ν` and take `K0 = D.specialCompactSubgroup x` at its
witness `D, x, Z, j, s, h`. Compactness and openness come from the `IsCompactOpenMaximal` part of
the special compact properties. `G(F) = P₀(F) K0` comes from the ambient parabolic product family
at the empty index. The simultaneous basis is the basis conjunct. The ambient Cartan covering is
the published `rationalPositiveCartanCover` applied to the represented centralizer and the
Cartan comparison conjunct. The Levi Cartan covering and the Levi Iwasawa factorization are the
two results above, applied to the standard-Levi compatibility conjunct and the Levi parabolic
product conjunct. `D.specialCompactLeviSubgroup ν J x` and `leviSchemeCompact K0 i ν J` are the
same preimage by definition.

## Provenance

The module is derived. Its results are consequences of published Library statements, and it adds
no mathematical assumption beyond the hypothesis `JointSpecialCompactBasisExistenceStatement`.

- D. Renard, *Représentations des groupes réductifs p-adiques* (French version dated 9 July
  2026; literature id `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), Théorème V.5.1, printed
  p. 122 (PDF p. 128): a maximal compact open `K₀` with "(1) `G = K₀P_∅ = P_∅K₀`", "(4)
  (Décomposition de Cartan) `G = ⋃_{a ∈ C^+_∅, f ∈ F_∅} K₀ a f K₀`" and "(5) Pour tout parabolique
  standard `P = MN` le sous-groupe compact maximal `K₀ ∩ M` de `M` vérifie les propriétés (1) à (4)
  pour le parabolique minimal `P_∅ ∩ M` de `M`." The two Levi results are the covering part of
  (4) and property (1) for `K₀ ∩ M_J`, as provided by (5). The Library states these properties
  for the special compact subgroup in `JointSpecialCompactBasisExistenceStatement`.
- J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
  J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`, SHA256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`), Proposition II.4.5 and its
  proof, printed pp. 262–263 (PDF pp. 28–29). The proof begins "On a l'égalité
  `M = (K ∩ M)M̄₀^{M+}(K ∩ M)`". The final theorem supplies the premises under which the Library
  states this proposition (`RationalConstantTermEstimateStatement`).
