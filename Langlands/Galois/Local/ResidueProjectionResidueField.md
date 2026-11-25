# The residue projection of a separable closure: the residue field

`Langlands.Galois.Local.ResidueProjectionResidueField` proves two clauses of
`ResidueProjectionProperties K Ω` (`Galois/Local/ResidueProjectionStatement.lean`) about
the residue field of a separable closure: the seventh (it is an algebraic closure of the
residue field `𝓀[K]`) and the eighth (the comparison with `AlgebraicClosure 𝓀[K]` is
compatible with reduction of elements of `𝒪[K]`). The objects are those of
`Galois/Local/AbsoluteDefinitions.lean`, namespace `Langlands.LocalGalois.SepClosed`.

## Setting

Both theorems take, as the statement does,

```lean
(K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
(Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
```

in independent universes. Local instances with names specific to this module install
`Algebra.IsAlgebraic K Ω` and the local norm of `K` (`localNormedField K`, with its
ultrametric and completeness certificates), as in `ResidueProjectionIntegers.md`.

`IsSepClosed Ω` is not an instance: it is Mathlib's theorem `IsSepClosure.sep_closed K`,
and declaring it as an instance makes instance search look for `IsSepClosure ?k L` for
every field `L` with `?k` unknown, which exhausts the search on unrelated goals. A statement
that needs it begins, as the statement file does, with
`haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`; this is inlined, so the elaborated
statement contains the proof term `IsSepClosure.sep_closed K`, exactly as the clause of the
target does.

Write `B = closureIntegers K Ω` for the integers of `Ω`, `k_B` for its residue field,
`k_A` for the residue field of `baseIntegers K` (the unit ball of the local norm of `K`),
and `localResidueEquiv K : k_A ≃+* 𝓀[K]`. `residueAlgebra K Ω` makes `k_B` a `𝓀[K]`-algebra
through `localResidueEquiv K` and the canonical map `k_A → k_B`;
`residueClosureEquiv K Ω : k_B ≃+* AlgebraicClosure 𝓀[K]` is the comparison chosen in
`AbsoluteDefinitions`.

## Statements

**`SepClosed.residueAlgebra_isAlgClosure`.** With `residueAlgebra K Ω`, the residue field of
the integers of `Ω` is an algebraic closure of `𝓀[K]`:

```lean
theorem Langlands.LocalGalois.SepClosed.residueAlgebra_isAlgClosure
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    letI := residueAlgebra K Ω
    IsAlgClosure 𝓀[K] (ResidueField (closureIntegers K Ω))
```

**`SepClosed.residueClosureEquiv_residue_integerMap`.** For `a ∈ 𝒪[K]`, the comparison sends
the residue of the image of `a` in `B` (under `integerMap K Ω`) to the image in
`AlgebraicClosure 𝓀[K]` of the residue of `a`:

```lean
theorem Langlands.LocalGalois.SepClosed.residueClosureEquiv_residue_integerMap
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (a : 𝒪[K]) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    residueClosureEquiv K Ω (residue _ (integerMap K Ω a)) =
      algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (residue 𝒪[K] a)
```

## Proofs

*Algebraic closure.* The Library's `residue_isAlgClosure K Ω` (`AbsoluteDefinitions`)
already proves `IsAlgClosure k_A k_B` for the canonical algebra: the residue field of a
valuation subring of a separably closed field is separably closed
(`residue_isSepClosed`, by lifting a separable irreducible residue polynomial to a monic
separable polynomial, finding a root in `Ω` and using that the valuation ring is
integrally closed); `k_B` is algebraic over the finite, hence perfect, field `k_A`, so it
is perfect, and a perfect separably closed field is algebraically closed. The clause asks for the other algebra structure,
over `𝓀[K]`. Algebraic closedness of `k_B` does not depend on the algebra and is taken
from `residue_isAlgClosure`; integrality of `k_B` over `𝓀[K]` is transported from
`AlgebraicClosure 𝓀[K]` through the `𝓀[K]`-algebra isomorphism
`residueClosureAlgEquiv K Ω` (`isIntegral_algEquiv`).

*Compatibility.* By definition of `integerMap` and `residueAlgebra`, the residue of
`integerMap K Ω a` is the image under `k_A → k_B` of `(localResidueEquiv K).symm` of the
residue of `a` (this holds by `rfl`). The Library's `residueClosureEquiv_base` says that
`residueClosureEquiv K Ω` sends the image of `y ∈ k_A` to the image of
`localResidueEquiv K y`; with `RingEquiv.apply_symm_apply` this is the claim.

## Declarations, in order

1. `rpResidueFieldIsAlgebraic`, `rpResidueFieldNormedField`, `rpResidueFieldUltrametric`,
   `rpResidueFieldComplete` (local instances, namespace `Langlands.LocalGalois.SepClosed`).
2. `SepClosed.residueAlgebra_isAlgClosure` (theorem; seventh clause).
3. `SepClosed.residueClosureEquiv_residue_integerMap` (theorem; eighth clause).

## Literature

- Jürgen Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer (1999), file
  `/srv/central-library/Neukirch--Algebraic number theory (book)--1999.pdf` (SHA-256
  `4f4406e097cf7cc4bfcc3eb818153d8361c5b0d8f5fb9848053d68d6c6239210`): Chapter II, §7,
  Proposition (7.5), printed p. 154, and the paragraph after it: the residue class field
  of the maximal unramified extension `K_nr` of a henselian field is the separable closure
  of the residue class field. Chapter II, §9, the paragraph after Proposition (9.11),
  printed p. 173: for `K` henselian and `K̄_s|K` its separable closure, the inertia field
  is `K_nr`, with residue field the separable closure of `κ`. The theorem here concerns
  the residue field of the separable closure itself, which contains that of `K_nr`; since
  the residue field of `K` is finite, hence perfect, its separable closure is an algebraic
  closure. The Library's proof does not pass through `K_nr`: it shows directly that the
  residue field of `Ω` is separably closed.
- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979), file
  `/srv/central-library/Serre--Local Fields--1979.pdf` (SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`): Chapter III, §5,
  Corollary 1 to Theorem 3, printed pp. 54–55 (`K_nr` is Galois over `K` with residue field
  `k_s`); Chapter V, §4, proof of Lemma 7, printed p. 89 ("The residue field of `K_nr` is
  an algebraic closure of" the residue field, for a complete discretely valued field with
  perfect residue field). Serre's statements are for the maximal unramified extension, not
  for a separable closure.
