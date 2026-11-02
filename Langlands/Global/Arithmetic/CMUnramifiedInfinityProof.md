# Unramified realization of CM infinity types

The theorem `Langlands.Global.cmUnramifiedInfinityRealization.{u}` proves the
existing proposition `Langlands.Global.CMUnramifiedInfinityRealizationStatement.{u}`
from `CMCharacterStatement`, without changing that statement or its imports.
For every CM number field `K : Type u` and every anticyclotomic integral
infinity type `a`, it gives a positive natural number `m` and an actual
continuous Hecke character `χ` with:

- `χ (AdelicFunctoriality.ideleClassComplexConj x) = (χ x)⁻¹` for every
  idele class `x`;
- infinity component
  `InfinityType.toCharacter (fun σ ↦ (m : ℤ) * a σ)`;
- unramified finite component at every finite place, in the existing
  integral-unit sense.

The universe is arbitrary, and no imaginary-quadratic subfield is chosen.
The single multiplier scales all weights. The construction uses the
existing CM conjugation, idele classes, infinity character, local
completions and local-unit inclusions.

## Implemented construction

The imported module `CMInfinityExtension` proves
`CMUnramifiedInfinity.exists_base_character`. Put
`t = NumberField.Units.torsionOrder K` and
`h = Nat.card (ClassField.Global.IntegralIdeleClassQuotient K)`.
Both are proved positive. For every global integral unit `ε`, the ratio
`ε / complexConj(ε)` is torsion, so scaling `a` by `t` makes its infinity
character trivial on global integral units. It therefore descends from
the integral ideles `U` to their image `H` in the idele class group `C`.
The finite quotient `C / H` has order `h`, and `c ↦ c ^ h` maps `C`
to `H`. Composing these maps constructs a Hecke character `ψ` with
infinity type `n * a`, where `n = h * t > 0`. Its value on every
integral idele equals the prescribed infinity character evaluated on
the archimedean projection.

The local lemma `CMUnramifiedInfinity.exists_base_character_trivial`
converts this exact formula into triviality on every integral idele
whose archimedean part is one. The projection is then the unit `1`
by `Units.ext`, and a character maps `1` to `1`.

The imported module `CMAntisymmetrization` supplies
`CMUnramifiedInfinity.realization_of_base`. First, a local integral unit
included as an idele is integral everywhere and has archimedean part
one. Hence the preceding triviality makes `ψ` unramified at every finite
place. Write `c` for the actual CM involution on idele classes and set
`χ(x) = ψ(x) / ψ(c x)`. Involutivity gives `χ(c x) = χ(x)⁻¹`.
On the archimedean subgroup, conjugation inverts the character of the
anticyclotomic type `n * a`; thus `χ` has type `2 * n * a`.
Pullback by conjugation preserves everywhere finite unramifiedness,
so `χ` is everywhere unramified. The lemma chooses `m = 2 * n > 0`.
The final theorem introduces the arbitrary field and infinity type,
obtains the base character from the bridge lemma, and applies this
realization lemma directly.

## Topology and arithmetic obstructions

The imported base construction proves that the integral idele subgroup
`U` is open in the existing units topology: both the finite coordinates
of an idele and those of its inverse must be integral. The idele-class
quotient map is open, and restricting it to `U` and its image `H` gives
an open continuous surjection, hence a quotient map. This proves the
descended infinity character on `H` continuous. The power map `C → H`
is continuous for the subspace topology, so its composite is an actual
continuous Hecke character. Antisymmetrization uses the published
continuous pullback by conjugation and the group operations on Hecke
characters.

The torsion-unit result, the principal-integral-idele unit criterion,
the finite residual quotient, its positive order, and the continuity
of every map are all proved in the imported dependency chain. No
character-extension datum, finiteness hypothesis, or conclusion-shaped
input record is assumed.

## Provenance and scope

The source target is Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique* (2000), Section 3.5, Lemma 1,
printed p.450 (one-based PDF p.12). Registered source:
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The source uses a chosen imaginary-quadratic subfield and a quotient by
the conjugation norm. The implemented proof follows the derived
finite-power route described above and works for every CM field in
the published target. Antisymmetrization is the device used in
Henniart's Section 3.6, proof of Lemma 2, printed p.451 (PDF p.13),
applied here to an anticyclotomic infinity character.

Worker 1231 constructed the base-character module and the bridge and
assembled the final theorem; Worker 1233 constructed the
antisymmetrization module. This proof establishes only the unramified
infinity-realization statement. Finite-component prescription, local
unit-character extension, regular unit-prescription assembly and the
other CM-globalization statements remain separate targets.
