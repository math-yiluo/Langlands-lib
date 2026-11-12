# Proof of the reduction of the joint special-compact existence target

`Langlands.BruhatTits.SpecialCompact.jointBasisReduction` proves
exactly `Langlands.BruhatTits.SpecialCompact.JointBasisReductionStatement.{u}`
at arbitrary universe `u`. Assume the existence of a valid assignment and the
six conditional statements. Then
`JointSpecialCompactBasisExistenceStatement.{u}` holds, with every clause
satisfied at one common `D`, `x`, `Z`, `j`, `s` and `h`. The proof combines the
seven premises using equality transport and the published inclusion of the
relative roots of a represented subgroup into the ambient relative roots.

## Helper lemmas

- `isGenericCocharacter_leviTorusHom`: if `ν` is generic for `i : S → G`, then
  it is generic for `Standard.leviTorusHom i ν J : S → M_J`. Every relative root
  of the Levi is an ambient relative root. This uses
  `relativeRoots_subset_of_factor` with the representation
  `Standard.isRepresentedBy_leviHom` and `Standard.leviTorusHom_comp`.
- `parabolicPointProductFamily_of_heq`: if `S' = S` and `HEq i' i`, then the
  parabolic point products for every generic cocharacter of `i'` give them for
  every generic cocharacter of `i`, with the same subgroup `K`. The proof
  substitutes the equality of tori and then uses `eq_of_heq`.
- `joint_of_valuationBuildingData`: let `V` be building data (a
  `ValuationBuildingData G`) with a special vertex. Suppose that at every
  generic cocharacter and special vertex of `V`, four facts hold: the compact,
  Levi-inheritance and basis conclusions; the ambient Iwasawa products; the two
  Renard Cartan clauses for `V.centralizer`; and the Levi Iwasawa products for
  `V.apartment.specialCompactLeviSubgroup`. If moreover `V.S = S` and
  `HEq V.i i`, then the full conjunction of the target holds for `i`. The
  witnesses are `D := V.apartment`, the given vertex `x`, and
  `Z, j, s, h := V.centralizer.Z, .j, .s, .bijective`, with the closedness,
  representability and factorization fields of `V.centralizer`. The proof
  destructures `V`, substitutes `V.S = S` and `V.i = i`, and assembles the
  conjuncts.

## Main proof

Take the valid assignment `𝔅₀` and the premises `hT`, `hSV`, `hBasis`, `hIw`,
`hCartan` and `hLM`. Fix `F`, `G`, `hG`, `S`, `i`, `hi` and `ν`.

1. `hT 𝔅₀ h𝔅₀ F G hG S i hi` gives a valid `𝔅` whose data for `G` have torus `S`
   and inclusion `i`. `KPBuildingAssignment.IsValid.isAvailableFor` gives
   `𝔅.IsAvailableFor F G hG`.
2. Apply `joint_of_valuationBuildingData` to
   `(𝔅.datum F G hG).base.toValuationBuildingData`:
   - the special vertex comes from `hSV`;
   - the compact properties, Levi inheritance and simultaneous basis come from
     `hBasis` (which needs validity);
   - the ambient Iwasawa products for `specialCompactSubgroup x` are the third
     component of the first clause of `hIw`;
   - both Renard Cartan clauses come from `hCartan`.
3. For the Levi Iwasawa products, fix a generic `ν`, a special vertex `x` and
   `J`. `hLM` gives `hM`, an assignment `𝔅M` available for `M_J`, the
   equalities of its torus with `S` and of its inclusion with
   `Standard.leviTorusHom`, and a special vertex `xM` whose special compact
   subgroup equals `specialCompactLeviSubgroup ν J x`. Rewrite with that
   equality. Then apply `hIw` to `𝔅M` and `M_J` at `xM`, and transfer the products
   from the torus of `𝔅M` to `Standard.leviTorusHom` with
   `parabolicPointProductFamily_of_heq`. Genericity of `ν` for the Levi comes
   from `isGenericCocharacter_leviTorusHom`.

All conjuncts are thus proved at the common `D`, `x`, `Z`, `j`, `s` and `h`.

## Scope

The theorem proves the implication from exactly the seven premises in the
published statement. It does not discharge those premises. Its conclusion
covers every field, connected reductive group, maximal split torus and generic
cocharacter quantified by `JointSpecialCompactBasisExistenceStatement`, with
no additional characteristic, splitness or rank restriction.

## Provenance

This is an internal reduction between Library statements, rather than an
additional theorem attributed to the original literature. The sources and
mathematical scope of the seven premises are recorded in their respective
paired Markdown files and in `JointBasisReductionStatement.md`.

The implementation is adapted from Worker 4169's shared draft revision 1 of
Task 4169 (`8c39faa0-2a70-4fc4-a027-914987aba924`). Worker 102 checked the
published interfaces, prepared this proof unit and expanded the explanation;
Worker 4169 is credited as coauthor.
