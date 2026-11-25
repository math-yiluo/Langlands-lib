# The Artin and Swan exponents of a representation of the local Weil group

This module defines the Artin and Swan exponents of a finite-dimensional complex representation
of the local Weil group of a p-adic field as natural numbers, and proves that every finite inertia
presentation computes them, that continuous representations have presentations, that they depend
only on the equivalence class, and Deligne's decomposition `a = dim V − dim V^I + sw`.

## Definitions

Name space `Langlands.Weil.Local`; `F : PadicField.{uF} p`,
`A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)`.

```lean
def artinExponent (F : PadicField.{uF} p) (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) : ℕ :=
  if h : Nonempty (FiniteInertiaPresentation F A) then
    ⌊(Classical.choice h).artinConductor
      (Ramification.HerbrandBridge.weilInertiaRestriction_surjective F _)⌋₊
  else 0

def swanExponent (F : PadicField.{uF} p) (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) : ℕ :=
  -- the same with `swanConductor`
```

A finite inertia presentation (`Ramification.Padic.FiniteInertiaPresentation F A`) is a finite
Galois subextension `L` of the algebraic closure of `F` such that the kernel of the restriction
of Weil inertia to the inertia group `I(L/F)` acts trivially on `A`; its Artin and Swan
expressions are those of the descended representation of `I(L/F)`. The restriction is surjective
for every `L` (`HerbrandBridge.weilInertiaRestriction_surjective`), so the definition needs only
the presentation. The choice of presentation does not matter (`artinExponent_eq`). For a
representation without presentation (not continuous on inertia) the exponents are `0`; the
theorems below are about representations that have one.

## Theorems

Variables `{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
{A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}`.

```lean
theorem artinExponent_eq (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    (artinExponent F A : ℚ) = P.artinConductor hP
theorem swanExponent_eq (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    (swanExponent F A : ℚ) = P.swanConductor hP
theorem artinExponent_eq_zero_of_isEmpty (h : IsEmpty (FiniteInertiaPresentation F A)) :
    artinExponent F A = 0
theorem swanExponent_eq_zero_of_isEmpty (h : IsEmpty (FiniteInertiaPresentation F A)) :
    swanExponent F A = 0
theorem exists_presentation_of_isContinuous (hA : A.IsContinuous) :
    ∃ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
      P.artinConductor hP = artinExponent F A ∧ P.swanConductor hP = swanExponent F A
def presentationOfEquiv {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) (P : FiniteInertiaPresentation F A) :
    FiniteInertiaPresentation F B
theorem artinExponent_eq_of_equiv {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) : artinExponent F A = artinExponent F B
theorem swanExponent_eq_of_equiv {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) : swanExponent F A = swanExponent F B
theorem fixedVectors_presentation (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    fixedVectors (P.representation hP) ⊤ =
      Representation.invariants (localInertiaRepresentation F A)
theorem artinExponent_eq_add_swanExponent (h : Nonempty (FiniteInertiaPresentation F A)) :
    artinExponent F A =
      (A.rank - finrank ℂ (Representation.invariants (localInertiaRepresentation F A))) +
        swanExponent F A
```

## Proofs

- `artinExponent_eq`: for the chosen presentation `Q`, the Artin expression is a natural number
  `a` (`Ramification.Padic.exists_nat_artinConductorOfQuotient`, `ArtinExponent`; the expression
  of a presentation is by definition an `artinConductorOfQuotient`), so the floor is `a`; and `Q`
  and `P` give the same expression (`Ramification.Padic.finiteInertiaConductorIndependence`,
  `InertiaPresentationProof`). Swan the same.
- `exists_presentation_of_isContinuous`: `HerbrandBridge.continuousWeilFiniteInertiaPresentation`
  gives a presentation; then `artinExponent_eq`, `swanExponent_eq`.
- `presentationOfEquiv`: the same field `L`; the kernel condition transports along the
  restricted equivalence (`Ramification.Padic.kernel_le_of_equiv`,
  `localInertiaRepresentationEquiv`).
- `artinExponent_eq_of_equiv`: if `A` has a presentation `P`, then `presentationOfEquiv e P`
  presents `B` and both give the same expression (`finiteInertiaConductorEquivalence`); if not,
  neither has one (transport along `e.symm`) and both exponents are `0`.
- `fixedVectors_presentation`: an element of `I(L/F)` is the restriction of some `w` in Weil
  inertia (surjectivity), and it acts as `A w`.
- `artinExponent_eq_add_swanExponent`: the Library's
  `Ramification.Padic.inertiaArtinConductor_eq_tame_add_swan` for the descended representation,
  whose tame term is `dim A − dim A^{I(L/F)}`, which is `dim A − dim A^I` by the previous lemma.

## Literature

Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular
Functions of One Variable II*, Lecture Notes in Mathematics 349, Springer, 1973, 501–597, §4.5,
printed pp. 537–538: for a representation `V` of the Weil group trivial on an open normal subgroup
`J` of inertia `I`, the conductors are defined on the finite quotient `I/J` by formula (4.5.4),
`a(V) = dim Hom_{I/J}(A_{I/J}, V) = sw(V) + dim V − dim V^I`, and are independent of `J` by
(4.5.2). The Library's presentation is such a finite quotient (`J` the inertia of `L`), its
independence of the presentation is `finiteInertiaConductorIndependence`, and the Library's
`artinExponent_eq_add_swanExponent` is (4.5.4). Deligne defines the conductors through the
Artin and Swan representations; the Library uses Serre's weighted sum (*Local Fields*, VI §2,
Corollary 1′, printed pp. 100–101), which is the same number by Serre's Corollary 1′. Deligne's
(4.5.4) is stated for a representation trivial on an open normal subgroup `J` of `I`, that is, one
with a presentation; the Library's value `0` for a representation without presentation has no
counterpart there.
