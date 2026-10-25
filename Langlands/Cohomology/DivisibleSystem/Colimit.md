# Colimits of `ℓ`-divisible systems

Author: Worker 61. Built on the base module
`Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem`, its fields
`tower`, `inclusion`, `powSMul_eq_zero`, `inclusion_comp`, `shortExact`,
`torsion_exact`, `flat`; morphisms `Hom` with fields `tower` and `comm`;
`hom_ext`, `forget`, `map`, `powSMul`, `shortComplex_exact_congr`). From
Mathlib it uses `HasExactColimitsOfShape` (CategoryTheory/Abelian/
GrothendieckAxioms/Basic), the functor `colim : (J ⥤ C) ⥤ C` with its
instances (additive: Algebra/Category/Grp/AB; preserving colimits as a left
adjoint: `colim_preservesColimits`), `ShortComplex.mapHomologyIso` and
`Functor.isZero_iff`.

Everything is in the namespace `Langlands.Cohomology`; the declarations of
the second section are in `Langlands.Cohomology.DivisibleSystem`.

Notation: `C` is an abelian category, `J` a category, `f ≫ g` is `f`
followed by `g`. An `ℓ`-divisible system `T` (Harris 1999, (2.1); base
module) has objects `T m` for `m : ℕ` (the functor `tower : ℕᵒᵖ ⥤ C`, whose
maps are Harris's `j : T m ⟶ T m'` for `m' ≤ m`), maps
`i = inclusion h : T m' ⟶ T m` for `m' < m`, `ℓ ^ m` killing `T m`, short
exact sequences `0 ⟶ T m' ⟶ T m ⟶ T (m - m') ⟶ 0` (`shortExact`), exactness
of `T m' ⟶ T m ⟶ T m` with second map `ℓ ^ m'` (`torsion_exact`), and
exactness of `T (a + b) ⟶ T (a + b) ⟶ T (a + b)` given by `ℓ ^ a` and
`ℓ ^ b` (`flat`).

## Exactness in functor categories

- `shortComplex_exact_of_evaluation`: a short complex `S` in `J ⥤ C` is
  exact if `S` evaluated at every `j` is exact. Proof: exactness is the
  vanishing of the homology; evaluation at `j` preserves homology
  (`ShortComplex.mapHomologyIso`), and a functor is zero if all its values
  are zero.
- `shortComplex_shortExact_of_evaluation`: the same for short exactness; the
  monomorphism and epimorphism conditions hold objectwise
  (`NatTrans.mono_of_mono_app`, `NatTrans.epi_of_epi_app`).
- `powSMul_app ℓ m F j`: `ℓ ^ m` on a functor `F`, evaluated at `j`, is
  `ℓ ^ m` on `F j`.

## Colimits

Let `D : J ⥤ DivisibleSystem C ℓ` be a diagram.

- `diagramSystem D`: the `ℓ`-divisible system in the functor category
  `J ⥤ C` whose level `m` is the functor `j ↦ (D j) m` (`tower` is
  `(D ⋙ forget C ℓ).flip`), with `i` given objectwise by the maps `i` of the
  `D j` (natural by the field `comm` of the morphisms `D f`). Its five
  conditions hold because they hold for each `D j`, by the two lemmas above
  and `powSMul_app`.

The rest assumes `[HasColimitsOfShape J C] [HasExactColimitsOfShape J C]`:
colimits of shape `J` exist in `C` and `colim : (J ⥤ C) ⥤ C` preserves
finite limits. It preserves finite colimits as a left adjoint and is
additive, so the base module's `map` applies.

- `colimitSystem D`: the `ℓ`-divisible system `(diagramSystem D).map colim`.
  Its level `m` is the colimit over `J` of the objects `(D j) m`. Its maps
  `j` and `i` are those induced on colimits (`colim.map`, that is
  `colimMap`). Exactness of `colim` gives the exactness conditions.
- `colimitSystemι D j : D j ⟶ colimitSystem D`: at each level, the
  coprojection `colimit.ι` (compatible with `j` and `i` by
  `colimit.ι_map`).
- `colimitSystemCocone D`: the cocone over `D` with vertex `colimitSystem D`
  and these coprojections (`colimit.w`).
- `levelCocone D c m`: for a cocone `c` over `D`, the cocone over
  `j ↦ (D j) m` with vertex `c.pt m` and components the level-`m`
  components of `c`.
- `colimitSystemDesc D c : colimitSystem D ⟶ c.pt`: at each level, the
  morphism `colimit.desc` induced by `levelCocone D c m`. Its compatibility
  with `j` and `i` is checked on each coprojection (`colimit.hom_ext`).
- `isColimitColimitSystemCocone D`: `colimitSystemCocone D` is a colimit
  cocone in `DivisibleSystem C ℓ`, with `colimitSystemDesc` as descending
  morphism. Factorization and uniqueness hold levelwise by those of the
  colimits in `C`.
- The instance `HasColimitsOfShape J (DivisibleSystem C ℓ)` built from
  these.

For filtered `J`, `HasExactColimitsOfShape J C` is AB5 for colimits of
shape `J`. Mathlib provides it for module categories `ModuleCat.{u} R` with
`R : Type u` and for abelian groups.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.306: "Taking the
direct limit as H shrinks to the identity, we obtain an ℓ-divisible system
of complexes C_m^• of projective Z/ℓ^mZ[S(ẽ)]-modules and a natural
S(ẽ)-equivariant quasi-isomorphism (2.6) ...". Harris treats the direct
limit of `ℓ`-divisible systems as an `ℓ`-divisible system without comment.
This module supplies the general construction behind that step: colimits of
`ℓ`-divisible systems, computed levelwise, when colimits of the given shape
are exact. The construction and all proofs are ours.

## Scope

The module constructs colimits of `ℓ`-divisible systems in a general
abelian category with exact colimits of the given shape. It does not
specialize them to Harris's systems `C_m^{•,H}` (no diagram over subgroups
`H`, no exact-colimit instance for representations), does not construct
`C_m^•`, (2.6), (2.7) or Lemma 2.8, does not treat homology of colimits of
complexes, and does not address projectivity.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the base module named above, pinned to Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
