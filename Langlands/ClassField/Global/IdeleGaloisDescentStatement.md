# Galois descent for ideles

`Langlands.ClassField.Global.IdeleGaloisDescent.{u,v}` is a proposition
quantified over number fields `K : Type u` and `E : Type v`, in independent
universes, with `Algebra K E` and `IsGalois K E`. The extension is finite
because both fields are number fields. The groups are Mathlib's actual
`NumberField.IdeleGroup (𝓞 K) K` and `NumberField.IdeleGroup (𝓞 E) E`,
the units of their full adele rings.

Let `i` be the published
`Langlands.Global.AdelicFunctoriality.ideleInclusion (K := K) (L := E)`.
The proposition states that `i` is injective and that an idele of `E` is
fixed by every relative automorphism if and only if it lies in the image of
`i`. Thus it expresses the identification of `J_K` with
`J_E^{Gal(E/K)}` through this particular inclusion. Injectivity gives
uniqueness of the preimage.

The inclusion comes from the actual completed embeddings at all places,
using the published module
`Langlands.Global.AdelicFunctoriality.Inclusion`. For
`σ : E ≃ₐ[K] E`, the equation expressing invariance is
`ideleEquiv σ.toRingEquiv a = a`, using the published arithmetic transport
from `Langlands.Global.AdelicFunctoriality.Isomorphism`. Both maps are used
unchanged. The proposition introduces no replacement carrier or assumed
descent map.

## Exact Lean statement

With the namespace and openings of the paired Lean file, the definition is:

```lean
def IdeleGaloisDescent : Prop :=
  ∀ (K : Type u) (E : Type v) [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E] [IsGalois K E],
    Function.Injective (ideleInclusion (K := K) (L := E)) ∧
      ∀ a : IdeleGroup (𝓞 E) E,
        (∀ σ : E ≃ₐ[K] E, ideleEquiv σ.toRingEquiv a = a) ↔
          ∃ b : IdeleGroup (𝓞 K) K,
            ideleInclusion (K := K) (L := E) b = a
```

Taking both universe parameters to be `u` gives the same assertion for
fields in one universe. The two universes in the definition remain
independent.

## Source and scope

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea
edition (2009), Preliminaries section 1, printed pp.1–2 (PDF pp.10–11).
The final paragraph on p.1 states the injection of idele groups for finite
extensions. The first paragraph on p.2 identifies the base field's idele
group with the Galois-fixed ideles upstairs. The source's fields `k ⊂ K`
correspond to the Lean fields `K → E`. This formulation specializes the
source's global-field assertion to number fields and expands its
identification into injectivity and an explicit fixed-point/image
equivalence.

Registered source: `artin-tate-2009-class-field-theory`; SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
Retained original:
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.

The source also gives a closed topological embedding and a corresponding
assertion for idele classes. Those assertions are outside this proposition.
This module defines the idele descent statement only; its proof is a
separate obligation.
