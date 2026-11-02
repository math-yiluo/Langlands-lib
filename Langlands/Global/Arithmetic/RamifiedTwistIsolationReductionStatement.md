# Ramified twist isolation from two arithmetic inputs

Author: Worker 84. This is a derived statement for the H1–H2 arithmetic
interface of the global automorphic and Henniart-input program
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

The proposition
`Langlands.Global.RamifiedTwistIsolationOfInputsStatement.{u}` is exactly

```text
FiniteOrderCharacterPrescriptionStatement.{u} →
LocalCharactersArbitrarilyRamifiedStatement.{u} →
RamifiedTwistIsolationStatement.{u}.
```

All three propositions are imported unchanged from
`Langlands.Global.Arithmetic.CharacterPrescriptionStatement`.
The number field has an arbitrary carrier universe `u`. Its local fields,
valuation integer rings, maximal ideals, Hecke characters and component maps
are the existing actual arithmetic objects.

The first premise prescribes finitely many local characters killed by a
common positive integer `n`, together with a character of the whole infinite
idele factor killed by `n`. Its conclusion supplies a Hecke character killed
by `2 * n`. The second premise supplies, at each finite place and natural
depth, a finite-order continuous local character nontrivial on the actual
principal units at that depth. Neither premise is proved by this definition.

The conclusion preserves every clause of the existing isolation target.
For disjoint finite sets `S` and `T`, arbitrary finite-order local characters
on `S`, and an independently specified depth at each place of `T`, it asks
for a finite-order Hecke character with the exact prescribed components on
`S`, trivial character on the whole infinite idele factor, and nontriviality
on each requested principal-unit level on `T`. At depth zero the imported
predicate tests integral units; at positive depth `r` it tests elements
`a` with `a - 1` in the `r`th power of the actual maximal ideal. All finite
sets, including empty sets, are retained. No common bound on the output
orders as the depths vary is asserted.

The elementary reduction chooses a local character at each place of `T`,
combines these with the given characters on `S`, chooses a common positive
multiple of their finitely many periods, and applies the first premise to
`S ∪ T` with trivial infinity character. Disjointness makes the prescription
unambiguous. Exact local component equality transfers the chosen
principal-unit witnesses. A separate proof task must establish this
implication; this file only defines its proposition.

## Source correspondence and boundary

The original motivation is Henniart, “On the local Langlands conjecture for
GL(n): the cyclic case” (1986), Proposition 3.4 on printed pp.156–157
(one-based PDF pp.13–14) and Section 4.3 on printed pp.158–159 (PDF pp.15–16).
Registered source `henniart-1986-cyclic`, SHA-256
`096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`,
retained original
`/home/taskhub/central-library/Henniart--On the Local Langlands Conjecture for GL(n) The Cyclic Case--1986.pdf`.
Worker 84 read these original pages and visually checked p.159.

Proposition 3.4 gives unrestricted finite-order global prescription with
the doubled period bound. Section 4.3 chooses finite-order local characters
with sufficiently large conductor and then a global character trivial at
infinity; the second choice is also trivial at the place to be isolated.
The reference there to Theorem 3.3 is read with the character-existence
proposition numbered 3.4. The Lean implication expresses the arithmetic
assembly as a derived finite-set statement. Its local existence hypothesis
and explicit maximal-ideal-depth predicate are inherited from the imported
Library target, rather than attributed to a new theorem in the source.
The singleton trivial prescription gives the character used to isolate one
place. The implication also permits several prescribed places and different
depths at the other places.

This statement supplies no local stability formula, functional equation,
gamma-factor comparison or separation of L and epsilon factors. Those are
separate consumers. It also supplies neither the unconditional
Grunwald–Wang theorem nor the local finite-order character existence premise.
Compilation and proposition inspection are development checks; independent
semantic acceptance and publication remain separate.
