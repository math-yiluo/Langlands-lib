# Galois descent for idele classes

`Langlands.ClassField.Global.IdeleClassGaloisDescent` is a proposition
universally quantified over number fields `K : Type u` and `E : Type v`,
in independent universes, with an actual `Algebra K E` and `IsGalois K E`.
The extension is finite because both fields are number fields. The class
groups are Mathlib's actual `NumberField.IdeleClassGroup (𝓞 K) K` and
`NumberField.IdeleClassGroup (𝓞 E) E`.

Write `i` for the published
`Langlands.Global.AdelicFunctoriality.ideleClassInclusion (K := K) (L := E)`.
The proposition says:

1. `i` is injective.
2. For every `c ∈ C_E`, all relative automorphisms fix `c` if and only if
   there exists `a ∈ C_K` with `i(a) = c`.

Here “fix” means the explicit equation
`relativeIdeleClassAut K E σ c = c` for every `σ : E ≃ₐ[K] E`, using the
published action from `Langlands.ClassField.Global.Cocycle`. This action
comes from arithmetic transport of ideles and passage to the principal
idele quotient. The map `i` is the published extension-of-scalars inclusion
from `Langlands.Global.AdelicFunctoriality.Inclusion`, induced by the
completed embeddings at all places. Both imported constructions are used
unchanged.

The two clauses express the identification `C_K ≃ C_E^{Gal(E/K)}` via
this particular inclusion. Injectivity supplies uniqueness of the preimage;
the two directions of the equivalence supply invariance of every image
class and descent of every invariant class. The statement does not assert
surjectivity onto all of `C_E`. It introduces no substitute class group,
arbitrary action, or assumed descent map.

## Exact Lean statement

With the namespace and openings in the paired Lean file, the definition is:

```lean
def IdeleClassGaloisDescent : Prop :=
  ∀ (K : Type u) (E : Type v) [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E] [IsGalois K E],
    Function.Injective (ideleClassInclusion (K := K) (L := E)) ∧
      ∀ c : IdeleClassGroup (𝓞 E) E,
        (∀ σ : E ≃ₐ[K] E, relativeIdeleClassAut K E σ c = c) ↔
          ∃ a : IdeleClassGroup (𝓞 K) K,
            ideleClassInclusion (K := K) (L := E) a = c
```

## Single-universe formulation

Setting both universe parameters to `u` gives
`Langlands.ClassField.Global.IdeleClassGaloisDescent.{u, u}`. Its
quantifiers then range over `K : Type u` and `E : Type u`, as required
by the single-universe consumers of the descent statement. For any such
`K` and `E`, the second conjunct is equivalent to

```lean
∀ c : IdeleClassGroup (𝓞 E) E,
  c ∈ Set.range (ideleClassInclusion (K := K) (L := E)) ↔
    ∀ σ : E ≃ₐ[K] E, relativeIdeleClassAut K E σ c = c
```

This formulation follows by symmetry of the displayed equivalence and
the definition of membership in `Set.range`; the first, injectivity
conjunct is unchanged. This is an explanation of the statement's
specialization, not an additional assertion of a proof of descent.

## Source and scope

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea
edition (2009), Preliminaries section 1, printed pp.1–2 (PDF pp.10–11).
The last paragraph on p.1 states the injections on ideles and idele classes;
the first paragraph on p.2 identifies the idele classes of the base field
with the Galois-fixed classes upstairs. The source's fields `k ⊂ K`
correspond here to `K → E`. Its account derives the class-group
identification from the field and idele invariants and Hilbert's Theorem 90.

Registered source: `artin-tate-2009-class-field-theory`; SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
Retained original:
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.
This statement specializes the source's global-field assertion to number
fields and expands the identification into injectivity and a pointwise
image criterion. The source also gives a closed topological embedding;
that additional assertion is outside this proposition.

This module only defines the proposition. It supplies no proof of Galois
descent or Hilbert 90.
