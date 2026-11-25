# The principal ideal theorem

Module `Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library; it states the
principal ideal theorem of the NYLL library (the copy under `Nyll/`) in Mathlib's vocabulary, with
NYLL's types hidden behind an existential.

Every number field `K` has a finite extension `H` that is unramified at every finite place of `K`
and in which every ideal of `𝓞 K` becomes principal. "Unramified" is Mathlib's
`Algebra.IsUnramifiedIn (𝓞 H) v.asIdeal`: every prime of `𝓞 H` above `v` is unramified over
`𝓞 K`. This is the notion used by the Library's `Langlands.Galois.IsUnramifiedOutside`.
"Becomes principal" means that the extended ideal `I.map (algebraMap (𝓞 K) (𝓞 H))` is principal.
The field `H` is in universe `0`, whatever the universe of `K`.

## Main declarations

```lean
theorem exists_unramified_extension_forall_isPrincipal (K : Type u) [Field K] [NumberField K] :
    ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : FiniteDimensional K H),
      (∀ v : HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 H) v.asIdeal) ∧
        ∀ I : Ideal (𝓞 K), (I.map (algebraMap (𝓞 K) (𝓞 H))).IsPrincipal
```

Complete type:

```lean
Langlands.ClassFieldTheory.Global.Artin.exists_unramified_extension_forall_isPrincipal : ∀ (K : Type u_1)
  [inst : Field K] [NumberField K],
  ∃ H x,
    ∃ (_ : NumberField H),
      ∃ x_2,
        ∃ (_ : FiniteDimensional K H),
          (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
              Algebra.IsUnramifiedIn (NumberField.RingOfIntegers H) v.asIdeal) ∧
            ∀ (I : Ideal (NumberField.RingOfIntegers K)),
              Submodule.IsPrincipal
                (Ideal.map (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers H)) I)
```

(`x : Field H` and `x_2 : Algebra K H` are the bound instances; the algebra structure on the rings
of integers is the one induced by `x_2`.)

## Proof

`H` is NYLL's `smallHilbertClassField K`, the Hilbert class field of `K`. It is the class field of
NYLL's small Hilbert norm subgroup of the idèle class group. It has degree the class number of `K`
(`smallHilbertClassField_finrank_over_original_eq_classNumber`), and its `K`-algebra structure
is `smallHilbertClassFieldAlgebraOverOriginal`. That structure comes with the instances
`FiniteDimensional K H` and `IsGalois K H`.

- *Unramified.* NYLL's `smallHilbertClassField_isUnramifiedAtFinitePlaces K` states
  `IsUnramifiedAtFinitePlaces K (smallHilbertClassField K)`: every height-one prime `P` of `𝓞 H`
  satisfies `Algebra.IsUnramifiedAt (𝓞 K) P`. A prime of `𝓞 H` lying over a finite place `v` of
  `K` is nonzero (`Ideal.ne_bot_of_liesOver_of_ne_bot`), hence a height-one prime, and so
  `Algebra.IsUnramifiedIn (𝓞 H) v.asIdeal`.
- *Principal.* NYLL's `allIdealsBecomePrincipalInSmallHilbertClassField K`. It holds because the
  extension of ideal classes `ClassGroup (𝓞 K) → ClassGroup (𝓞 H)` is trivial
  (`smallHilbertClassFieldClassGroupExtension_eq_one`). Through the reciprocity isomorphisms, that
  map is the map induced on idèle class quotients by extension of idèles. It is trivial because
  every extended idèle class lies in the norm group from the Hilbert class field of `H`. That comes
  from the vanishing of the transfer `G/G' → G'/G''` for a finitely generated group `G` with `G'`
  of finite index (`GroupTheory.Transfer.Witt.commutatorTransfer_eq_one_of_finite_abelianization`,
  Witt's proof). In an abstract class formation, it takes the form
  `intermediateNormQuotientInclusion_commutator_eq_zero`: the inclusion of the base into the field
  cut out by the commutator subgroup vanishes on the norm quotients.

The two theorems of NYLL are stated for the same `K`-algebra structure: both use the term
`smallHilbertClassFieldAlgebraOverOriginal K`. So they combine with no comparison of instances.

## Declarations used

From the NYLL copy:

- `GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField`
  (`Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldRealization.lean`);
- `smallHilbertClassFieldAlgebraOverOriginal`, `smallHilbertClassFieldFiniteDimensionalOverOriginal`
  (`…/GlobalClassFields/SmallHilbertClassFieldOverOriginalBase.lean`); the instances `Field` and
  `NumberField` on `smallHilbertClassField K` are those of NYLL's construction (a finite
  subextension of a class field, `ordinaryNormClassFieldExtensionNumberField`,
  `…/GlobalClassFields/OrdinaryNormClassField.lean`);
- `smallHilbertClassField_isUnramifiedAtFinitePlaces`
  (`…/GlobalClassFields/HilbertClassFieldUnramifiedMaximality.lean`), with
  `IsUnramifiedAtFinitePlaces` (root name space,
  `Nyll/ClassFieldTheory/AlgebraicNumberTheory/NumberField/FiniteUnramifiedTower.lean`);
- `GlobalClassFieldTheory.IdealClassFieldTheory.allIdealsBecomePrincipalInSmallHilbertClassField`
  (`Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertPrincipalization.lean`).

From Mathlib: `Algebra.IsUnramifiedIn`, `Algebra.IsUnramifiedAt`, `Ideal.ne_bot_of_liesOver_of_ne_bot`.

## Importing this file

This file imports the two modules of NYLL named above, which bring in 930 modules of the copy.
A file that imports it inherits their global instances: 689 of them besides the automatically
generated `SizeOf` instances. Most are about NYLL's own constructions (its fields, idèle groups and
local fields). Thirty-seven apply to types that do not come from NYLL, for example
`Algebra ℚ (SeparableClosure ℚ)` (`GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra`),
`MulSemiringAction (Field.absoluteGaloisGroup K) (AlgebraicClosure K)`, `T2Space Gal(Ω/k)` for
algebraic `Ω / k`, and `Finite (Abelianization G)` when the commutator subgroup has finite index.
The file also brings in 1,983 lemmas of the default `simp` set from NYLL. The file itself declares
no instance and no `simp` lemma.

## Sources

- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322 (Springer 1999): chapter VI, §7,
  (7.5) Theorem, p. 410. In the Hilbert class field every ideal of `K` becomes principal; the
  proof reduces this, by Artin reciprocity, to the vanishing of the transfer, (7.6) Theorem, p. 410
  (proof due to Witt). Neukirch's Hilbert class field is the maximal unramified abelian extension
  in which the infinite places split completely. NYLL's field is abelian over `K`, unramified at
  every place with the infinite places split completely
  (`smallHilbertClassField_isEverywhereUnramified`), and of degree the class number.
- E. Artin, J. Tate, *Class Field Theory* (AMS Chelsea 2009): chapter VIII, §2, Theorems 7 and 8
  and the remark following them, p. 58 (the Hilbert class field and the second step of its tower,
  to which the principal ideal theorem applies); chapter XIII, §4, Theorem (Principal Ideal
  Theorem), p. 140 (the transfer `U/U^c → U^c/(U^c)^c` is zero when `U^c` is of finite index and
  finitely generated).
