# Lemma S: Galois twisting of norm-one points (proofs of S1 and S2)

Proves the two statements of module `AdelicGaloisTwistSubgroup`, the inputs of
`galoisBorelTwisting_of` (module `AdelicGaloisBorelTwistingProof`). Notation: `G_L` is the base
change of `G` to the Galois extension `L/F`, `σ ∈ Gal(L/F)`, `galoisTwist F L G σ` is the
Galois twist of the upper adelic points `G_L(𝔸_L)`, and `normOneSubgroup` is the norm-one
subgroup `H(𝔸_L)^1` of an `L`-group `H`.

## Inputs

- D1 `twistPoint_comp_radicalGaloisHom` (module `AdelicGaloisTwistDescent`): for a subgroup
  morphism `j : H → G_L` and `p ∈ H(𝔸_L)`, `twistPoint p ≫ radicalGaloisHom j σ =
  galoisTwist σ (p ≫ j)`, where `radicalGaloisHom j σ : H^σ → G_L` is the canonical Galois
  translate of `j` (Library module `Rational/UnipotentRadicalGalois`).
- Lemma C `twistPoint_mem_normOneSubgroup` (module `AdelicGaloisTwistNormOneProof`):
  `twistPoint` carries `H(𝔸_L)^1` into `H^σ(𝔸_L)^1`.
- Library: `map_normOneSubgroup_le` (homomorphisms preserve norm-one points),
  `IsClosedSubgroup.baseChange`, `IsClosedSubgroup.comp_iso`,
  `IsClosedSubgroup.sourceIsoOfRangeEq(_hom_comp)`, `GroupScheme.comp_innerIso_hom`,
  `rational_basePointEquiv`; from `AdelicGaloisBorelTwistingProof`:
  `rationalSection_eq_rational_basePointEquiv`.

## S1: `galoisTwistNormOne : GaloisTwistNormOneStatement.{u}`

For `x ∈ G_L(𝔸_L)^1`, D1 with `j = 𝟙` (`twistPoint_comp_radicalGaloisHom_id`) gives
`galoisTwist σ x = twistPoint x ≫ radicalGaloisHom 𝟙 σ`. Lemma C makes `twistPoint x`
norm-one, and the homomorphism `radicalGaloisHom 𝟙 σ` preserves norm-one points
(`mem_normOneSubgroup_of_comp_eq`).

## S2: `galoisTwistSubgroup : GaloisTwistSubgroupStatement.{u}`

Let `f : P → G_L` and `g : Q → G_L` be closed subgroups and `m` a rational point of `G_L`
with `range (radicalGaloisHom f σ) = range (g ≫ Int(m))`.

1. `radicalGaloisHom f σ` is closed: it is the base change of `f` followed by an isomorphism
   (`isClosedSubgroup_radicalGaloisHom`); `g ≫ Int(m)` is closed by `comp_iso`.
2. Equal ranges of closed subgroups give an isomorphism `e = twistSourceIso : P^σ ≅ Q` with
   `e ≫ g ≫ Int(m) = radicalGaloisHom f σ` (`twistSourceIso_hom_comp`).
3. For `p ∈ P(𝔸_L)^1` put `q = twistPoint p ≫ e`; it is norm-one by Lemma C and
   `map_normOneSubgroup_le`.
4. By D1 and step 2, `galoisTwist σ (f p) = (q ≫ g) ≫ Int(m)`, and `comp_innerIso_hom`
   evaluates `Int(m)` on adelic points as conjugation by the constant point of `m`, which
   is `rationalSection m` (`eq_rational_conj_of_comp_eq`, `galoisTwist_comp_eq_conj`).

## Kernel-checking remark

`G_L` occurs in two definitionally equal forms, `AffineWeil.unitBaseChange F L G` and
`(GroupScheme.baseChange (algebraBaseMap F L)).obj G`. Proofs that mixed both forms inside one
large term hit a kernel deterministic timeout. Steps 1–4 are therefore stated entirely in the
second form. The switch to the first form happens only in small lemmas about abstract points
and morphisms (`mem_normOneSubgroup_unitBaseChange`,
`galoisTwist_map_eq_rationalSection_conj`).
