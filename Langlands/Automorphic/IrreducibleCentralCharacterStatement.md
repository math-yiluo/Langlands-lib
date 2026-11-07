# Central characters of irreducible operator realizations

Author: Worker 116, for task `34b81620-20d7-4059-9b08-6bedd1c1c029`.

`Langlands.Automorphic.OperatorRealization.IrreducibleCentralCharacterStatement`
is a proposition definition: every irreducible actual operator realization of
`GL_n` over a number field has exactly one central character. The module
`Langlands.Automorphic.IrreducibleCentralCharacterStatement` imports only
`Langlands.Automorphic.OperatorRealization`. It supplies no proof.

## Statement

```lean
def IrreducibleCentralCharacterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (S : OperatorRealization F n),
    S.IsIrreducible → ∃! χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ, S.HasCentralCharacter χ
```

The statement quantifies over every number field `F` in an arbitrary universe
`u`, every natural rank `n`, including `n = 0`, and every actual operator
realization `S`. If `S` is irreducible, then exactly one continuous character
`χ` of the idele class group `C_F = 𝔸_F^× / F^×` satisfies
`S.HasCentralCharacter χ`. The character is a conclusion, not a hypothesis.
It takes values in `ℂˣ` and need not be unitary. No compactness instance on
`AdeleQuotient F`, cuspidality or unitarity is assumed.

## Objects

All objects are the published ones; nothing is redefined here.

- **Operator realizations.** `OperatorRealization F n` is the published
  abbreviation for `Subrepresentation (stableAutomorphicAction F n)`
  ([OperatorRealization](OperatorRealization.md)). Its ambient space is the
  stable core `StableAutomorphicFunctions F n` of the actual automorphic
  forms ([OperatorCore](OperatorCore.md)). These are smooth functions on
  `GL_n(𝔸_F)` that are left invariant under `GL_n(F)` and have finite level.
  They are finite under the standard compact subgroup at the infinite places
  (real orthogonal and complex unitary groups), annihilated by a
  finite-codimensional ideal of the center of the enveloping algebra, and of
  polynomial growth ([Forms](Forms.md)). The acting algebra is generated
  inside the actual endomorphisms by three operator families: finite-adelic
  right translations, right translations by the standard infinite compact
  subgroup, and the genuine differential action of the complexified
  enveloping algebra.
- **Irreducibility.** `S.IsIrreducible` is `S.representation.IsIrreducible`,
  Mathlib's `Representation.IsIrreducible`, which is
  `IsSimpleOrder (Subrepresentation _)`. It refers to the three operator
  families together. In particular `S` is nonzero.
- **Central character.** `S.HasCentralCharacter χ` is the published
  condition: the realization lies in
  `centralCharacterAutomorphicSubrepresentation F n χ`. By the published
  `OperatorRealization.centralCharacter_evaluate`, every form `f` of `S`
  satisfies `f(z x) = χ(z) f(x)` for every idele `z`, embedded as a scalar
  matrix by `AdelicGL.scalar`, and every `x ∈ GL_n(𝔸_F)`. Here `χ(z)` means
  `centralIdeleCharacter F χ z`, that is, `χ` composed with the quotient map
  from the ideles to `C_F`.
- **Characters.** `IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ` consists of the
  continuous homomorphisms from the idele class group with its quotient
  topology. This is the same type as the published `HeckeCharacter F`.
  Uniqueness means equality of these continuous homomorphisms on all of
  `C_F`.

For `n = 0` the scalar embedding has trivial target. A nonzero form then
forces `χ = 1`, so the trivial character is the unique central character.

## Source correspondence and provenance

Provenance: derived.

Borel and Jacquet, *Automorphic forms and automorphic representations*, Proc.
Sympos. Pure Math. 33, part 1 (1979), registered as
`borel-jacquet-1979-automorphic`. The retained volume file has SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`; one-based
PDF page = printed page − 5. The original pages were read directly.

- §4.3(i), printed p.195 (PDF p.190): the space of automorphic forms of a
  fixed type `(ξ, J, K_∞)` is finite dimensional.
- §4.3(iv), printed p.195: every automorphic form is `C(G(𝔸))`-finite, where
  `C(G(𝔸))` is the center of `G(𝔸)`. §4.3(3) on the same page writes the
  central-character condition `f(z x) = χ(z) f(x)` for a character `χ` of
  `Z(𝔸)/Z(F)`.
- §4.5, printed p.196 (PDF p.191): automorphic forms generate admissible
  modules.
- §4.6, printed p.196: an irreducible automorphic representation is
  admissible. The text then discusses the cuspidal automorphic
  representations "in which `Z(𝔸)` has character `χ`".

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), registered as
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`. In §2.2,
printed p.444 (PDF p.6), Henniart writes `det S = ω_Π ∘ τ_F`, where `ω_Π` is
"le caractère central de Π". This presupposes that each automorphic
representation `Π` of `GL_n(𝔸_F)` has a central character.

Neither source states this proposition as a numbered result. It is the
standard consequence of admissibility and Schur's lemma, specialized here to
the Library's actual operator realizations. The intended proof route is:

1. An irreducible `S` is generated by any nonzero form `f`. Every form in `S`
   is annihilated by the finite-codimensional ideal `J` of the enveloping
   center that annihilates `f`, because the center commutes with all three
   operator families. Finite level and compact finiteness are preserved too.
   So `S` lies in a countable union of the finite-dimensional spaces of
   §4.3(i) and has countable dimension. Dixmier's form of Schur's lemma then
   makes every operator commuting with the three families a scalar.
2. A finite central idele, an element of the center of the real Lie algebra,
   and the scalar `-1` at a real place all commute with the three families.
   Each therefore acts on `S` by a scalar. On the identity component at the
   infinite places, the scalar action of the Lie-algebra center integrates,
   by uniqueness of solutions of a linear ordinary differential equation, to
   a continuous exponential character.
3. Together these give a homomorphism `𝔸_F^× → ℂˣ` with `f(z x) = χ(z) f(x)`.
   It is trivial on `F^×` because the forms are left `GL_n(F)`-invariant and
   `S ≠ 0`. It is continuous: trivial on an open subgroup of the finite
   ideles by finite level, and continuous at the infinite places by step 2.
   So it descends to `C_F`.
4. Uniqueness: two central characters agree at every idele, because some
   form of the nonzero realization `S` takes a nonzero value.

This route is guidance for a later proof, not part of the statement.

## Use and boundary

The proposition is the first step of the intended proof of the published
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement`
(module `Langlands.Automorphic.AssociatedCentralCharacterStatement`). There
the actual cuspidal realization `T` must have a central character before the
determinant of the associated Weil representation can be compared with it.
This module does not prove that comparison, unitarity of the central
character, or any statement about cuspidal realizations specifically.
