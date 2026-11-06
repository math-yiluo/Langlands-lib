# Proof of the integral Brauer character-lattice equality

Author: Worker 84, who wrote the proof and this explanation.

This file proves the conjunct `IntegralBrauerCharacterLatticeStatement G` of the Library proposition
`Langlands.FiniteRep.FiniteBrauerTheoryStatement` (module `Langlands.Representation.Finite.BrauerStatement`).
The target is unchanged and keeps its hypotheses: `G` is a group in universe `uG` with a `Fintype` instance.

| Theorem in `Langlands.FiniteRep.BrauerLattice` | Proves |
| --- | --- |
| `characterLattice` (implicit `G`) | `IntegralBrauerCharacterLatticeStatement G` |

The statement says that `inducedCharacterLattice (k := ℂ) (G := G)`, the `ℤ`-span of the characters
`inducedCharacter d` of the actual inductions `induce d.1 (classOf (oneDimensional d.2))` of all rank-one
data `d : MonomialDatum ℂ G` (a subgroup with a unit-valued character), equals
`virtualCharacters (k := ℂ) (G := G)`, the image of the virtual representation group under the character
map. It is an equality over `ℤ`. The other six conjuncts, and `FiniteBrauerTheoryStatement` itself, are not
proved here. The proof adds no hypotheses or axioms; the declaration check of `characterLattice` reports only
`propext`, `Classical.choice` and `Quot.sound`.

This is Brauer's induction theorem in the form used by Henniart (*Une preuve simple des conjectures de Langlands
pour GL(n) sur un corps p-adique*, 2000, §3.7, p.451): virtual characters are integer combinations of
characters induced from one-dimensional characters of subgroups. It is Theorem 20 of Jean-Pierre Serre, *Linear
Representations of Finite Groups*, GTM 42, Springer, 1977, §10.5 (literature ID `serre-1977-linear-representations`):
each character is an integer combination of monomial characters. Serre proves it through elementary subgroups. The
ported Anthropic proof instead combines Solomon's theorem for hyperelementary subgroups with the monomial expansion
of characters of hyperelementary groups; see the Markdown of the ported modules.

## Imports and sources

- `Langlands.Representation.Finite.BrauerStatement`, the target module. Through it the proof uses the public
  modules `Langlands.Representation.Finite.Virtual` (`MonomialDatum`, `inducedCharacter`,
  `inducedCharacterLattice`, `virtualCharacters`, `mem_virtualCharacters_iff`, `inducedCharacterLattice_le`,
  `oneDimensional`, `character_oneDimensional`) and `Langlands.Representation.Finite.Induction` (`induceRep`).
- `Langlands.Representation.Finite.InducedCharacterProof` (Worker 84), for
  `Langlands.FiniteRep.InducedCharacter.inducedCharacterFormula`, the proof of
  `FiniteInducedCharacterFormulaStatement`: the character of the actual induction `induceRep S V` at `g` is
  `(Nat.card S)⁻¹ * ∑ x : G, [x⁻¹ g x ∈ S] V.character (x⁻¹ g x)`.
- `Langlands.AnthropicFLT.Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter`, the
  port of the Anthropic FLT theorem `BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter` (ported in
  the same contribution; see that module's Markdown for source, licence and changes). For a finite group `K : Type`
  and `ρ : K →* GL (Fin n) ℂ` it gives subgroups `H i`, unit characters `ψ i : H i →* ℂˣ` and integers `a i` with
  `trace (ρ g) = ∑ i, (a i : ℂ) * ((Nat.card (H i))⁻¹ * ∑ y : K, [y⁻¹ g y ∈ H i] ψ i (y⁻¹ g y))`.

The external theorem concerns a group in universe `0`, matrix representations, and a normalized conjugation sum.
The target concerns groups in an arbitrary universe, `FDRep` representation classes, and characters of actual
induced representations. This file bridges those three differences.

## Matrix model

`matrixModel ρ`, for `ρ : Representation ℂ G V` with `V` finite-dimensional (any universes), is the group hom
`G →* GL (Fin (finrank ℂ V)) ℂ` obtained by composing `ρ.asGroupHom` with `Units.map` of the algebra isomorphism
`LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)`. `matrixModel_trace` says that the matrix trace of
`matrixModel ρ g` is `ρ.character g` (Mathlib's `LinearMap.trace_eq_matrix_trace`).

## Transport along a group isomorphism

Let `e : G ≃* K` be an isomorphism of finite groups (independent universes).

- `card_comap e H`: the pullback `H.comap e` of a subgroup `H` of `K` has the same cardinality as `H`
  (`Subgroup.comap_equiv_eq_map_symm`, `Subgroup.card_map_of_injective`).
- `pullbackDatum e H ψ` is the rank-one datum of `G` given by the subgroup `H.comap e` and the unit character
  `ψ ∘ (e restricted to H.comap e → H)` (`MonoidHom.subgroupComap`).
- `inducedCharacter_pullbackDatum e H ψ g`: the character of the induction of `pullbackDatum e H ψ` at `g` equals
  `(Nat.card H)⁻¹ * ∑ y : K, [y⁻¹ (e g) y ∈ H] ψ (y⁻¹ (e g) y)`. Proof: unfold `inducedCharacter` to the character of
  `induceRep (H.comap e) (oneDimensional _)`, rewrite with `inducedCharacterFormula` and `card_comap`, and reindex the
  sum over `G` by `e` (`Fintype.sum_equiv`). Since `e (x⁻¹ g x) = (e x)⁻¹ (e g) (e x)`, membership conditions agree,
  and on members the values agree by `character_oneDimensional`.

## The lattice

- `character_mem_inducedCharacterLattice V`: for every `V : FDRep ℂ G`, the character `V.character` lies in
  `inducedCharacterLattice`. Mathlib's `Finite.exists_type_univ_nonempty_mulEquiv` gives a finite group `K : Type` and
  `e : G ≃* K`. Apply the external theorem to `(matrixModel V.ρ).comp e.symm`, obtaining `H i`, `ψ i` and `a i`.
  Evaluating at `e g` and using `matrixModel_trace` gives `V.character g` on the left. By
  `inducedCharacter_pullbackDatum`, the `i`-th summand on the right is `a i • inducedCharacter (pullbackDatum e (H i) (ψ i)) g`.
  Hence `V.character = ∑ i, a i • inducedCharacter (pullbackDatum e (H i) (ψ i))`, a finite `ℤ`-combination of
  generators of the lattice.
- `characterLattice`: the inclusion `inducedCharacterLattice ≤ virtualCharacters` is the Library's
  `inducedCharacterLattice_le`. Conversely, by `mem_virtualCharacters_iff`, a virtual character is
  `character a - character b` for representation classes `a`, `b`. Choosing representatives `V`, `W` of the classes
  (quotient induction), the character of each is in the lattice by the previous step, and the lattice is closed under
  subtraction.

## Declarations

All in namespace `Langlands.FiniteRep.BrauerLattice`.

- def `matrixModel`; theorem `matrixModel_trace`
- theorem `card_comap`; def `pullbackDatum`; theorem `inducedCharacter_pullbackDatum`
- theorem `character_mem_inducedCharacterLattice`
- theorem `characterLattice : IntegralBrauerCharacterLatticeStatement G`
