# Conrad's Lemma 4.6 from the uniform Lang–Weil estimate in families

Author: Worker 69.

This module states the reduction of Conrad's Lemma 4.6 to the uniform Lang–Weil estimate in
families. It is the last step of the Library's Lang–Weil route to Lemma 4.6. The module contains
no proof.

## The statement

`UniformLangWeilOfFamilyStatement` is the implication

`FamilyLangWeilStatement → UniformLangWeilStatement`

in the same universe `u`, where

- `FamilyLangWeilStatement` (`Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilStatement.lean`)
  is the uniform Lang–Weil estimate, for every `d`, for geometrically irreducible morphisms of
  finite type over a base of finite type over `ℤ` with fibres of pure dimension `d`, at all
  `κ`-points of the base for all finite fields `κ`;
- `UniformLangWeilStatement` (`Langlands/AlgebraicGeometry/UniformLangWeilStatement.lean`) is
  Conrad's Lemma 4.6: for a smooth, separated, surjective, quasi-compact morphism `f : Y ⟶ B`
  locally of finite type, with `B` of finite type over `ℤ`, geometrically connected, with fibres
  of pure dimension `d`, there is `C > 0` with
  `|N_b − q_b ^ d| ≤ C q_b ^ (d − 1/2)` for every closed point `b`, where `q_b = #κ(b)` and `N_b`
  is the number of sections of `f.fiber b ⟶ Spec κ(b)`.

## Relation to the sources

Provenance: derived. Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(registered source `conrad-2011-weil-grothendieck-adelic-points`), Lemma 4.6, printed p.12, is a
statement about smooth families with geometrically connected fibres; `FamilyLangWeilStatement`
generalizes it (see its Markdown). The reduction specializes the family estimate to `κ = κ(b)`
and the canonical point `Spec κ(b) ⟶ B` for closed points `b`.

## Expected proof route

The proof is not part of this module. It needs three facts:

1. a smooth morphism with geometrically connected fibres is geometrically irreducible: after any
   base change to a field the fibre is smooth over that field, hence has domain stalks (the
   Library's `Langlands.AlgebraicGeometry.smoothDomainStalks`), and a connected locally
   Noetherian scheme with domain stalks is integral (the Library's
   `Langlands.AlgebraicGeometry.connectedLocallyNoetherianDomainStalksIntegral`);
2. the residue field of a closed point of a scheme of finite type over `ℤ` is finite;
3. sections of `f.fiber b ⟶ Spec κ(b)` correspond bijectively to morphisms
   `x : Spec κ(b) ⟶ Y` with `x ≫ f = B.fromSpecResidueField b`, by the universal property of the
   fibre product defining `f.fiber b`.

## Status

Open. A proof is to be supplied through its own focused proof task.
