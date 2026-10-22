# The idele-class norm as a Galois product

`Langlands.ClassField.Global.IdeleClassNormGaloisProduct` is a proposition
definition. For number fields `K : Type u` and `L : Type v`, an algebra
structure `Algebra K L`, and `IsGalois K L`, it states that every idele class
`x` of `L` satisfies

```text
incl_{L/K}(N_{L/K}(x)) = ∏ (σ ∈ Gal(L/K)), σ(x).
```

Both sides lie in `NumberField.IdeleClassGroup (𝓞 L) L`. The norm first
lands in the idele-class group of `K`; the inclusion then carries that class
back to the idele-class group of `L`. The product contains each relative
field automorphism once.

The fields have independent universes. Their number-field instances imply
that `L` is finite dimensional over `K`, so the extension and its
automorphism group are finite. The local `Fintype.ofFinite` supplies only an
enumeration for the finite product, with no additional mathematical
hypothesis. The statement assumes neither that the Galois group is
abelian nor any unramifiedness condition.

The three maps are the published constructions, used unchanged:

- `Langlands.Global.AdelicFunctoriality.ideleClassNorm` is the continuous
  homomorphism induced by the product of local determinant norms on ideles.
- `Langlands.Global.AdelicFunctoriality.ideleClassInclusion` is the
  continuous homomorphism induced by extension of scalars at every place.
- `Langlands.ClassField.Global.relativeIdeleClassAut K L σ` is the
  arithmetic transport of idele classes along the underlying field
  automorphism of `σ : L ≃ₐ[K] L`.

The statement uses Mathlib's actual quotient of ideles by principal
ideles. It introduces no replacement group, action, norm, or inclusion.
This file states the equality; it does not prove it or assume it as an axiom.

## Source correspondence

Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea edition (2009),
Preliminaries section 1, printed pp. 1–2 (PDF pp. 10–11), describes the
inclusions of ideles and idele classes and the Galois actions, identifying
the lower groups with the invariant subgroups. Chapter XIII section 2,
printed p. 132 (PDF p. 141), writes the multiplicative group norm as
`N(a) = ∏_{σ ∈ G} a^σ`. Registered source:
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.

André Weil, *Basic Number Theory*, second edition (1973), Chapter IV
section 1, Theorem 1 and Corollary 1, printed pp. 62–63 (PDF pp. 79–80),
gives the adelic inclusion through the completed embeddings. Corollary 3,
printed p. 64 (PDF p. 81), gives the norm at a base place as the product of
the local norms over all places above it. Registered source:
`weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.

These pages were read. The displayed Lean proposition is the compatibility
statement between these arithmetic constructions and the Galois group
norm, specialized to number fields. It writes the inclusion explicitly
where the literature identifies the lower idele-class group with its
image. This realization on the published Lean maps is derived from those
source conventions; neither cited passage is claimed to mention these
Lean declarations.
