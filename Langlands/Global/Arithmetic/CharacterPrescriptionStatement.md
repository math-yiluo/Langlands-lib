# Finite-order character prescription and ramified isolation

Author: Worker 35. This statement contribution belongs to task
`369ca096-d0b6-4e25-8a06-66af3ef95878`, revision 2. It uses the accepted
and currently published definition artifact
`0e6d30b8-1a28-49a0-988e-84729eb9f351`, version 1, by Worker 2:
`Langlands.Global.Adelic` and `Langlands.Global.HeckeCharacter`.
These are dependencies, not assertions of the existence theorems below.
Compilation and proposition inspection do not establish mathematical truth
or independent semantic acceptance.

## Objects and scope

All declarations are in `Langlands.Global`. The number field `K : Type u`
has an arbitrary carrier universe. Its finite places are the actual nonzero
prime ideals of its ring of integers. The local fields are Mathlib's adic
completions; the full idele group and its idele-class quotient use their actual
topologies. A Hecke character is a continuous multiplicative map from this
quotient to the units of the complex numbers.

The prescribed local maps are continuous complex characters of the actual
local multiplicative groups. Archimedean prescription is a continuous
character of the entire archimedean idele factor. In particular, the
prescription `1` means trivial at every infinite place. No global
class-field theorem or local Langlands correspondence is assumed in order
to state these propositions.

## Grunwald--Wang prescription

`FiniteOrderCharacterPrescriptionStatement` says that if a positive integer
`n` kills each of finitely many prescribed finite local characters and the
prescribed archimedean character, there is a Hecke character killed by
`2 * n` with exactly those components.

The factor two is intentional. Artin--Tate, Chapter X, Section 2, Theorem 5,
gives global period either the least common multiple of the local periods
or twice that multiple. The exceptional case requires an additional
compatibility condition to obtain the smaller period. We impose no such
condition and retain the unconditional larger bound. Our given `n` is a
common multiple, not necessarily the least common multiple. Including all
infinite places in the finite set of prescribed places yields the
archimedean clause. A character of the finite product of archimedean
multiplicative groups is determined by its component characters.

This is the input cited in Henniart (1986), Proposition 3.4. The reference
to “Theorem 3.3” in that paper's Section 4.3 is read with the actual
character-existence proposition in Section 3.4. Henniart (2000), Section
3.6, uses the same finite-order prescription step before forming a
conjugate-self-dual quotient. The present proposition does not itself
assert that quotient construction.

## Deeply ramified characters and isolation

`NontrivialOnPrincipalUnits v η r` unfolds to an element `a` of the units
of the local valuation integer ring such that `a - 1` lies in the `r`th
power of its maximal ideal and the actual image of `a` under `η` is not
one. The map to the multiplicative group of the local field is
`Units.map` of the valuation-subring inclusion. It is not an arbitrary
identification of unit groups.

At depth zero this tests all integral units, since the zeroth ideal power
is the whole ring. At positive depth it tests the usual principal-unit
group `1 + m^r`. With the standard convention that the conductor exponent
is the first level on which a character is trivial, the predicate says
that exponent is strictly greater than `r`. The Lean target uses the
explicit filtration and does not depend on an unimplemented numeric
conductor function.

`LocalCharactersArbitrarilyRamifiedStatement` asks for a finite-order
continuous character nontrivial at any specified depth. This is the local
existence input used in Henniart (1986), Section 4.3, when choosing the
characters with sufficiently large conductor. Its elementary construction
uses the finite quotients of the integral units: separate a nontrivial
element in a sufficiently deep finite quotient by a complex character,
then extend over the uniformizer factor. More precisely, at positive depth
`r`, the quotient `U^r / U^(r+1)` is the nonzero additive residue field.
Choose a nontrivial character on this subgroup of the finite abelian group
`U^0 / U^(r+1)` and extend it to that finite group. Inflating and assigning
the value one to a uniformizer gives the required continuous local
character. At depth zero use the positive-depth construction at depth one.
Serre, Chapter IV, Section 2, Proposition 6, supplies the unit-filtration
quotients and their topology. The finite-group character extension is
elementary character theory; this paragraph describes a derived input,
not a claim that Serre states this exact character theorem. The finite
order may grow with the requested depth.

`RamifiedTwistIsolationStatement` combines these two inputs. For disjoint
finite sets `S` and `T`, it prescribes arbitrary finite-order characters
on `S`, is trivial at infinity, and is nontrivial on each requested
principal-unit level on `T`. A common multiple of the finitely many
selected local orders allows the Grunwald--Wang prescription theorem to
be applied to their union. The output is finite order; its order is not
bounded independently of the requested depths.

The application isolating one place takes `S` to be that singleton and
prescribes the trivial character there. This reproduces the character
choice in Henniart (1986), Section 4.3, printed p.159. The local
degeneration/stability formulas of Section 4.2 and the comparison of
global functional equations remain distinct theorem obligations.

`CharacterPrescriptionStatement` is the conjunction of the three
existence statements. All five declarations are definitions returning
`Prop`. None supplies a proof of an existence assertion.

## Originals and dependency boundary

- Artin and Tate, *Class Field Theory*, AMS Chelsea edition (2009),
  Chapter X, Sections 1--2, printed pp.73--80, especially Theorem 5
  on p.80 (PDF p.89). Source `artin-tate-2009-class-field-theory`,
  SHA256 `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
  This is the retained typeset edition of the original account; its page
  numbering differs from the older p.103 citation in Henniart.
  The theorem and its order condition were also visually inspected.
- Henniart, “On the Local Langlands Conjecture for GL(n): The Cyclic
  Case” (1986), Proposition 3.4, printed pp.156--157 (PDF pp.13--14);
  Sections 4.2--4.3, printed pp.158--159 (PDF pp.15--16).
  Source `henniart-1986-cyclic`,
  SHA256 `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`.
- Henniart, “Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique” (2000), Section 3.6, printed pp.450--451
  (PDF pp.12--13), for the finite-order character prescription used
  before the self-dual construction. Source `henniart-2000-simple-proof`,
  SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Serre, *Local Fields*, English translation (1979), Chapter IV,
  Section 2, definition of the unit filtration and Proposition 6,
  printed p.66 (PDF p.73), read in context pp.65--68. Source
  `serre-1979-local-fields`,
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The accepted definition artifact supplies the actual objects and maps, with
their intrinsic algebraic and continuity proofs. Its publication was verified
as current at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, with effective snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`.
The exact imported Lean files have SHA256
`b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e`
(`Adelic.lean`) and
`68525fbd6a536afefdb696f83491c0ddd60d506390cf7dcb9682c7688c3de18f`
(`HeckeCharacter.lean`). Their paired Markdown hashes are, respectively,
`117b848792dbdbd67225466f0c51c312951803134cdc97dfc895d3f58f9b8c53` and
`9af1f28dc3858237fecf97b389a0c581433870404b40274bcb7b37f68323c94f`.
The development copies match all four published hashes.

No CM infinity type, auxiliary general-position condition, automorphic
representation, or local factor is represented by a free predicate in
this file. Those additional required families remain open.

Native development compilation of these exact `Adelic` and
`HeckeCharacter` sources followed by this module succeeded with no diagnostics
in the pinned Lean 4.34.0 environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. All five complete elaborated
definitions were printed and inspected with their universe parameters.
The three quantified targets and their conjunction return `Prop`; the
filtration predicate has only the stated number-field, place, character and
depth arguments. No hidden field, degree, prime or order restriction appeared.
The submission fingerprint is obtained from inspection of the conjunction's
full target. Independent semantic review and current Library publication of
this new statement remain separate requirements. No theorem proof is
provided or assumed by this contribution.
