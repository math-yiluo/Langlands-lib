# The smooth contragredient of supercuspidal objects and classes

Author: Worker 23.

This module restricts the bundled smooth contragredient of
`Category/Contragredient` to the actual supercuspidal objects
`GeneralLinear.SupercuspidalRep` and their isomorphism classes
`GeneralLinear.SupercuspidalClass` (module `Classification/Supercuspidal`).
Every construction takes two explicit hypotheses:

- `hG : CompactOpenCofinal (GeneralLinear n F)`: compact open subgroups are
  cofinal among open subgroups. With it, the published irreducible admissible
  theory gives irreducibility of the contragredient.
- `hsc : SupercuspidalContragredientClosed`: the smooth contragredient
  preserves the supercuspidal condition.

The module does not prove `hsc`. For p-adic fields it derives `hsc` from the
published proposition target
`GeneralLinear.SupercuspidalContragredientStatement`. The resulting p-adic maps
therefore take a proof of that statement as an argument.

## Generic layer (namespace `Langlands.GeneralLinear`)

`F` is a field with a topology, and `GL_n(F) = GeneralLinear n F` is assumed to
be a topological group. Carriers of supercuspidal objects are in a fixed
universe `uV`. Over `ℂ` the smooth contragredient keeps carriers in `uV`.

- `ker_determinant_le_ker_inv`: if a character `χ` of `GL_n(F)` is trivial on
  the determinant kernel, so is `χ⁻¹`. This holds over any field and needs no
  topology.
- `SupercuspidalContragredientClosed` is the `Prop`

      ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
        IsSupercuspidal A.representation →
          IsSupercuspidal (smoothContragredient A.representation).

  It is a hypothesis, not a claim. It is the forward half of part 1 of
  `SupercuspidalContragredientStatement`, restricted to smooth carriers in
  `Type uV` and to one field, topology and rank.
- `SupercuspidalRep.contragredient hG hsc A` has underlying object
  `A.obj.contragredient` (`contragredient_obj`). It is irreducible by
  `IrreducibleAdmissibleRep.contragredient`, which is
  Casselman's Corollary 2.1.13 in its published form. It is supercuspidal by
  `hsc`.
- `SupercuspidalRep.contragredientFunctor hG hsc` is the contravariant functor
  from the opposite of the full supercuspidal subcategory to itself. It is the
  lift of `SmoothRep.contragredientFunctor`, and `contragredientIso` is its
  action on isomorphisms.
- `SupercuspidalRep.bidualIso hG hsc A : A ≅ contragredient hG hsc
  (contragredient hG hsc A)` is the canonical evaluation isomorphism
  `SmoothRep.bidualIso`, which applies because supercuspidal objects are
  admissible.
- `SupercuspidalRep.contragredientTwistIso hG hsc χ hχ hdet A` identifies the
  contragredient of the twist by a character `χ` of the determinant with the
  twist of the contragredient by `χ⁻¹`. It is `SmoothRep.contragredientTwistIso`
  on underlying objects. The twist is the published `SupercuspidalRep.twist`
  of `Classification/SupercuspidalTwist`.
- `SupercuspidalClass.contragredient hG hsc` is the induced map on classes.
  `contragredient_isoClass` computes it on a representative. The following
  facts are proved about it:
  - `toSmoothDualClass_contragredient`: forgetting supercuspidality turns it
    into the published `SmoothDualClass.contragredient hG`.
  - `contragredient_isoClass_eq_isoClass_iff`: the class of `B` is the
    contragredient of the class of `A` exactly when there is an actual
    equivariant linear equivalence
    `(smoothContragredient A.obj.representation).Equiv B.obj.representation`.
    The proof transfers the published `SmoothDualClass` criterion along the
    injective map `toSmoothDualClass`.
  - `contragredient_contragredient`, `contragredient_involutive` and
    `contragredient_bijective`: the map is an involution, by `bidualIso`, and
    hence a bijection.
  - `contragredient_twist`: dualizing the twist by `χ` gives the twist of the
    dual by `χ⁻¹`, with `isOpen_ker_inv` and `ker_determinant_le_ker_inv`
    supplying the hypotheses for `χ⁻¹`.

## p-adic layer (namespace `Langlands.PadicField`)

Here `F : PadicField p`, `T : F.TopologicalData` and `n` are arbitrary, with
the topology `T.topology` and the topological-group structure
`T.generalLinearTopologicalGroup n`. The argument
`h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}` is a proof of
the published proposition target.

- `TopologicalData.supercuspidalContragredientClosed T h n` derives the
  closure hypothesis from part 1 of the statement, applied to the carrier and
  action of each smooth object.
- `TopologicalData.supercuspidalClassContragredient T h n` is
  `SupercuspidalClass.contragredient` with cofinality from the published
  `GeneralLinear.compactOpen_cofinal F T n` and closure from the previous item.
  `supercuspidalClassContragredient_involutive` records that it is an
  involution.
- `PadicField.SupercuspidalClass.contragredient h` is that map on the
  canonical class space `PadicField.SupercuspidalClass F n hn`, for the
  canonical topological realization. `SupercuspidalClass.contragredient_involutive`
  records that it is an involution.

Once a proof `hproof` of `SupercuspidalContragredientStatement` is published,
the unconditional map is `PadicField.SupercuspidalClass.contragredient hproof`.

## Sources

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995 (registered source
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`; PDF page =
printed page):

- Proposition 2.1.10 and Corollary 2.1.13, p. 22: for admissible `π`, the
  contragredient is admissible, its contragredient is isomorphic to `π`, and
  "The admissible representation π is irreducible if and only if π̃ is." These
  are used through the published module `Category/Contragredient`.
- §5.1, p. 46: "An admissible representation (π, V) is said to be absolutely
  cuspidal (or, by Harish-Chandra in [20], super-cuspidal) if for any proper
  parabolic subgroup P = MN in G, V = V(N) and hence V_N = 0." This is the
  published predicate `IsSupercuspidal`, with block parabolics of `GL_n` and
  all conjugates of their unipotent radicals.
- Theorem 5.3.1, p. 48: "Let (π, V) be an admissible representation of G. The
  following are equivalent: (a) (π, V) is absolutely cuspidal; (b) (π̃, Ṽ) is
  absolutely cuspidal; …". Its implication (a) ⇒ (b) is the content of
  `SupercuspidalContragredientClosed`. This module takes it as a hypothesis.

The text layer renders the tilde accents detached from their letters. The
quotations restore them.

| Source | Lean |
| --- | --- |
| Theorem 5.3.1 (a) ⇒ (b) | hypothesis `SupercuspidalContragredientClosed` |
| `π̃` of a supercuspidal object | `SupercuspidalRep.contragredient` |
| Corollary 2.1.13 | irreducibility in `SupercuspidalRep.contragredient` |
| Proposition 2.1.10, `π̃̃ ≅ π` | `SupercuspidalRep.bidualIso`, `SupercuspidalClass.contragredient_contragredient` |
| `π̃` on supercuspidal classes | `SupercuspidalClass.contragredient`, `PadicField.SupercuspidalClass.contragredient` |

## Provenance and scope

The constructions are derived. They restrict published constructions and
follow the Casselman statements quoted above. The twist identity
`(π ⊗ χ)~ ≅ π̃ ⊗ χ⁻¹` is not stated by Casselman. It is the published
`SmoothRep.contragredientTwistIso`.

The closure of supercuspidality under the contragredient is assumed, not
proved. The reverse implication (b) ⇒ (a) of Theorem 5.3.1 is neither used
nor formalized here.
