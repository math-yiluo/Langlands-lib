# Proof of the finite abelian class field statement

Module `Langlands.Global.Arithmetic.ClassFieldProof`, name space `Langlands.Global`. It proves
the published `FiniteAbelianClassFieldStatement` of
[`ClassFieldStatement`](ClassFieldStatement.lean) and each of its five clauses, from the bridge
modules `Langlands/ClassFieldTheory/Global/Artin/` onto the NYLL library (the copy under
`Nyll/`).

## Main declarations

```lean
theorem finiteAbelianArtinReciprocity : FiniteAbelianArtinReciprocityStatement.{u, v}

theorem openIdeleClassSubgroupFiniteIndex : OpenIdeleClassSubgroupFiniteIndexStatement.{u}

theorem finiteAbelianClassFieldExistence : FiniteAbelianClassFieldExistenceStatement.{u}

theorem finiteAbelianClassFieldKernelRigidity :
    FiniteAbelianClassFieldKernelRigidityStatement.{u}

theorem isOpen_ker_of_hasFiniteOrder {K : Type u} [Field K] [NumberField K]
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder) :
    IsOpen (χ.toMonoidHom.ker : Set (IdeleClasses K))

theorem exists_injective_comp_arithmeticFiniteArtin {K : Type u} [Field K] [NumberField K]
    (χ : HeckeCharacter K) (H : OpenSubgroup (IdeleClasses K))
    (hH : H.toSubgroup = χ.toMonoidHom.ker) :
    letI := NumberField.of_module_finite K (classField K H)
    letI : TopologicalSpace (classField K H ≃ₐ[K] classField K H) := ⊥
    ∃ θ : (classField K H ≃ₐ[K] classField K H) →ₜ* ℂˣ,
      Function.Injective θ ∧ ∀ x, θ (arithmeticFiniteArtinBot K (classField K H) x) = χ x

theorem finiteOrderHeckeArtinRealization : FiniteOrderHeckeArtinRealizationStatement.{u}

theorem finiteAbelianClassField : FiniteAbelianClassFieldStatement.{u, v}
```

The five propositions are those of `ClassFieldStatement`: Artin reciprocity with uniqueness for
finite abelian `L / K` (`K : Type u`, `L : Type v`), finiteness of the index of open subgroups of
`IdeleClasses K`, existence of a finite abelian subfield of `AlgebraicClosure K` with prescribed
kernel, rigidity of that subfield, and realization of Hecke characters of finite order through
faithful characters of finite abelian Galois groups. The Galois groups carry the discrete
topology `⊥` and the normalization is the arithmetic one (`HasArithmeticArtinNormalization`).

Lean reports that `Langlands.Global.finiteAbelianClassField` depends on `propext`,
`Classical.choice` and `Quot.sound` only.

## Proofs

- *Reciprocity.* `FiniteDimensional K L` follows from the two `NumberField` instances and
  `IsAbelianGalois K L` from `IsGalois K L` and the commutativity hypothesis. The map is
  `arithmeticFiniteArtinBot K L`, surjective (`arithmeticFiniteArtin_surjective`) and normalized
  (`arithmeticFiniteArtin_hasArithmeticArtinNormalization`); any continuous normalized map equals
  it (`eq_of_hasArithmeticArtinNormalization`, which uses only the Library).
- *Finite index.* `openSubgroup_finiteIndex`.
- *Existence.* The field is `classField K H`, finite and abelian over `K`, with the map
  `arithmeticFiniteArtinBot K (classField K H)`, whose kernel is `H`
  (`arithmeticFiniteArtin_classField_ker`).
- *Rigidity.* By uniqueness the two given maps are the arithmetic Artin maps of `L` and `E`; equal
  kernels give `L = E` (`eq_of_arithmeticFiniteArtin_ker_eq`).
- *Hecke characters.* If `χ ^ n = 1` with `n > 0`, every value of `χ` is an `n`-th root of unity.
  The set of `n`-th roots of unity other than `1` is finite, hence closed in `ℂˣ`, so the kernel
  of `χ` is the preimage of an open set (`isOpen_ker_of_hasFiniteOrder`). Let `H` be the kernel
  as an open subgroup. The arithmetic Artin map `ρ` of `classField K H` is surjective with kernel
  `H`, so `χ` factors as `θ ∘ ρ` (`MonoidHom.liftOfRightInverse`); `θ` is injective because the
  kernels agree, and continuous because the Galois group is discrete
  (`exists_injective_comp_arithmeticFiniteArtin`).

## Declarations used

- From the bridge modules (`Langlands/ClassFieldTheory/Global/Artin/`): `arithmeticFiniteArtin`,
  `arithmeticFiniteArtinBot`, `arithmeticFiniteArtin_surjective` (`FiniteArtin`);
  `arithmeticFiniteArtin_hasArithmeticArtinNormalization` (`FiniteArtinNormalization`);
  `eq_of_hasArithmeticArtinNormalization` (`ArtinUniqueness`); `openSubgroup_finiteIndex`
  (`OpenSubgroupFiniteIndex`); `classField`, `arithmeticFiniteArtin_classField_ker`,
  `eq_of_arithmeticFiniteArtin_ker_eq` (`ClassField`).
- From the Library: the statements of `ClassFieldStatement`; `HeckeCharacter`,
  `HeckeCharacter.HasFiniteOrder` (`Langlands/Global/HeckeCharacter.lean`).
- From Mathlib: `Module.Finite.of_restrictScalars_finite`, `IsMulCommutative.of_comm`,
  `mul_comm'`, `rootsOfUnity`, `mem_rootsOfUnity`, `Set.Finite.isClosed`,
  `MonoidHom.liftOfRightInverse`, `MonoidHom.liftOfRightInverse_comp_apply`,
  `injective_iff_map_eq_one`, `continuous_of_discreteTopology`.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, (5.5), (5.6) and (6.1); Milne, *Class Field
Theory*, Chapter V, Theorems 5.3 and 5.5 and Corollary 5.6; Artin–Tate, *Class Field Theory*.
