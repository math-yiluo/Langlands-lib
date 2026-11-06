# The unitary-central-character reduction of Renard VII.1.3

Author: Worker 1507. Module `Langlands.Representation.Exponents.MaximalLeviReducibilityReductionStatements`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The module contains one definition, two small theorems about it, and two derived statements (`Prop`-valued definitions). Neither statement is proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.1.3, proof of the Theorem, first paragraph (printed p.224 / PDF p.230). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`. The proof begins:

> On peut supposer que `π` est de caractère central unitaire. En effet, si tel n'est pas le cas, un argument de la démonstration du théorème VI.8.5 nous dit qu'il existe un caractère non ramifié `χ` de `G` tel que le caractère central de `πχ = π ⊗ χ` soit unitaire. D'après l'isomorphisme de Mackey III.2.11, on a `πχ = i_P^G(ρ) ⊗ χ ≃ i_P^G(ρ ⊗ χ|_M)`. La représentation `π` est donc réductible si et seulement si `πχ` l'est, et la conclusion sur `ρ` se déduit de celle sur `ρ ⊗ χ|_M`.

Here `π = i_P^G ρ`. The two statements below separate this sentence into the theorem with a unitary central character and the existence of the twist. The Mackey isomorphism and the transfer of hypotheses and conclusion are not stated here.

## Restriction of characters

- `leviRestrictedCharacter p l χ : rationalPoints M →* ℂˣ` is the restriction `χ|_M` of a character `χ : rationalPoints G →* ℂˣ` along the point map of `l ≫ p`, that is `m ↦ χ (rationalPoints.map (l ≫ p) m)`. The theorem `leviRestrictedCharacter_apply` records this formula (`rfl`).
- `isOpen_ker_leviRestrictedCharacter p l hp hl χ`: for a continuous character `χ : rationalPoints G →ₜ* ℂˣ`, where `rationalPoints G` carries its canonical topology `RationalPointFamily.pointTopology` and is a nonarchimedean group, the kernel of `leviRestrictedCharacter p l χ.toMonoidHom` is open in `rationalPoints M` with its canonical topology `leviPointTopology l hl`.

  Proof: the point map of `l ≫ p` is `Subtype.val ∘ leviPointsEquiv p l hp hl`, which is continuous. So the restricted character is continuous. `M(F)` is a nonarchimedean group by `leviPoints_nonarchimedeanGroup`, and a continuous complex character of a nonarchimedean group has an open kernel by the published `isOpen_ker_of_continuous_complex_character`.

The open kernel is the datum `SmoothRep.twist` needs. The topology on `rationalPoints G` in this section is the named local instance `maximalLeviRestrictionAmbientPointTopology`, defined as `RationalPointFamily.pointTopology`. It is the same topology the statements install.

## `MaximalLeviSupercuspidalReducibilityUnitaryStatement`

This is the text of the published `MaximalLeviSupercuspidalReducibilityStatement`, binder for binder, with one extra premise placed after the reducibility premise:

`Nonempty (UnitaryCentralCharacter ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation)`.

`UnitaryCentralCharacter` is the published structure of `Representation/MatrixCoefficient/ModuloCenter`: a character of the full center `Subgroup.center (rationalPoints G)`, with open kernel and all values of norm `1`, by which every central element acts on the induced representation as a scalar. So the statement is Renard's Theorem under the proof's assumption "`π` est de caractère central unitaire", with `π = i_P^G ρ`. Everything else (the field, the group, the maximal proper parabolic, irreducibility and supercuspidality of `ρ`, reducibility of `i_P^G ρ`, and the conclusion with `g`, `φ`, `ψ` and `T`) is as in the target. See `MaximalLeviSupercuspidalReducibilityStatement.md` for those parts.

## `MaximalLeviUnitaryCentralTwistStatement`

It quantifies over the same field, group, actual rational parabolic `p : P ⟶ G`, rational Levi `l`, matching radical `r` and `hmul` as the target, with the same topologies and instances on `rationalPoints G` and `rationalPoints M`. It drops properness and maximality of `P`. For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` that is irreducible and supercuspidal (the target's Jacquet-vanishing premise, verbatim), it asserts that there is an element `χ` of the published unramified-character group

`Plancherel.unramifiedCharacters (fun χ : rationalCharacters G => (Plancherel.rationalNormCharacters G χ).toMul)`

of `G(F)` such that the induction `(leviInductionFunctor p l r hp hr hl hmul).obj (ρ.twist χ_M _)` has a `UnitaryCentralCharacter`. Here `χ_M = leviRestrictedCharacter p l χ`, and the open-kernel proof is `isOpen_ker_leviRestrictedCharacter`.

This is the sentence "il existe un caractère non ramifié `χ` de `G` tel que le caractère central de `π ⊗ χ` soit unitaire", stated for `i_P^G(ρ ⊗ χ|_M)`, which by Mackey III.2.11 is isomorphic to `π ⊗ χ`. Stating it for the induction of the twisted `ρ` puts the twist on `M`, where the target's conclusion lives.

Why it holds (the argument of VI.8.5, for orientation only): `Z(G(F))` lies in the image of `M(F)` and acts on the irreducible `ρ` by a character `ω` (Schur's lemma), and on `i_P^G ρ` by the same `ω`, since the modulus of `P` is trivial on `Z(G(F))`. The positive character `|ω|` is trivial on compact subgroups, and `Z(G(F))/A_G(F)` is compact. So `|ω|` is determined by its restriction to `A_G(F)`, which is the restriction of `|χ|^{-1}` for an unramified positive character `χ` of `G(F)`. Then `ω χ` is unitary.

## Faithfulness notes

- **Placement of the extra premise.** The unitary statement adds a hypothesis to the target. It is not the target, and it is not used to change the target. The target follows from the two statements together with the Mackey isomorphism and the transfer of irreducibility, supercuspidality, reducibility and the conclusion across the twist. A separate module will prove that implication.
- **Central character of `π` versus `ρ`.** The source speaks of the central character of `π`. The statements use the center of `G(F)` acting on the induced representation, as in the source. They do not use the center of `M(F)`.
- **Unramified characters of `G`.** Renard's unramified characters of `G` are the characters trivial on `⁰G`. The published group `Plancherel.unramifiedCharacters` consists of continuous characters of `G(F)` trivial on the common kernel of the normalized absolute values of all rational characters of `G`, which is `⁰G`.
- **Weaker hypotheses in the twist statement.** Properness and maximality of `P` play no role in the twist argument and are omitted, so the statement is stronger. It keeps irreducibility and supercuspidality of `ρ`, which the reduction has available.

## Provenance

Both statements are derived from the first paragraph of the proof of Renard VII.1.3, quoted above. They split the target into a unitary case and a twist-existence input for the represented-parabolic interface. `leviRestrictedCharacter` is the restriction `χ|_M` of that paragraph. All other objects are the published ones used by `MaximalLeviSupercuspidalReducibilityStatement`.
