# Colimit preservation by actual cokernels of compatible local module maps

The declaration

```text
Langlands.Algebra.LocalCokernelColimitPreservationStatement.{uI,uA,uB,uE,uF,uR,uS,uM,uN} : Prop
```

states that the actual cokernel system of a compatible map of local module
systems has a bijective additive colimit comparison when the comparison of the
source system is surjective and that of the target system is bijective. The
universe parameters appear in the order shown; it is fixed by the explicit
universe binder of the definition. This module defines the proposition only.
Its proof is a separate obligation.

## Statement

```lean
def LocalCokernelColimitPreservationStatement.{uI, uA, uB, uE, uF, uR, uS, uM, uN} : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S)
    (M : Type uM) (N : Type uN) [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    (E : LocalModuleSystem.{uI, uA, uB, uE, uR, uS, uM} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (f : M →ₗ[S] N) (φ : LocalModuleSystem.CompatibleMap E F f),
    Function.Surjective E.moduleColimitMap → Function.Bijective F.moduleColimitMap →
      Function.Bijective φ.cokernelSystem.moduleColimitMap
```

## Quantifiers and hypotheses

The proposition universally quantifies:

- a nonempty directed preorder `ι : Type uI`;
- commutative local rings `R : Type uR` and `S : Type uS` with an `R`-algebra
  structure on `S` whose structure map `algebraMap R S` is local;
- exactly one published `LocalAlgebraSystem D` over `ι`, `R` and `S`, with
  base components in `uA` and algebra components in `uB`;
- arbitrary `S`-modules `M : Type uM` and `N : Type uN`;
- published local module systems `E : LocalModuleSystem D M` with components
  in `uE` and `F : LocalModuleSystem D N` with components in `uF`, both over
  the same `D`;
- an `S`-linear map `f : M →ₗ[S] N`;
- a published compatible map `φ : LocalModuleSystem.CompatibleMap E F f`.
  Its components `φ.component i : E.obj i →ₗ[D.alg i] F.obj i` commute with the
  transitions of `E` and `F` (`φ.map_comm`) and satisfy
  `F.ιM i (φ.component i m) = f (E.ιM i m)` (`φ.ιM_comm`).

The two hypotheses are

1. `Function.Surjective E.moduleColimitMap`, and
2. `Function.Bijective F.moduleColimitMap`.

Here `LocalModuleSystem.moduleColimitMap` is the published additive map from
Mathlib's `AddCommGroup.DirectLimit` of the components, along the additive
maps underlying the transitions, to the target module. It is the
direct-limit lift of the system's semilinear cocone `ιM`.

No other hypotheses occur. In particular there is no colimit condition on the
ring system `D` (neither of its ring comparison maps is assumed injective or
surjective), and no approximation, flatness, finite-generation or
finite-presentation hypothesis. The components of `φ` and the map `f` need not
be injective. Injectivity of `E.moduleColimitMap` is not assumed.

## Conclusion

The conclusion is `Function.Bijective φ.cokernelSystem.moduleColimitMap`. It
concerns exactly the published construction `φ.cokernelSystem` from
`Langlands.Algebra.LocalApproximationCokernel`:

- its component at `i` is the actual range quotient
  `F.obj i ⧸ LinearMap.range (φ.component i)`;
- its transitions are `φ.cokernelMap`, induced by `F.map`;
- its target is the actual quotient `N ⧸ LinearMap.range f`, with the cocone
  `φ.cokernelιM` induced by `F.ιM`.

The comparison is the existing `moduleColimitMap` of that system, which the
published lemma `cokernelSystem_moduleColimitMap_of_mk` evaluates as
`[n] ↦ [F.ιM i n]` on canonical representatives. The statement introduces no
replacement carriers, isomorphic copies or alternative comparison maps.

## Strength and the bijective-source case

The source hypothesis is only surjectivity. The case needed downstream, in
which both input comparisons are bijective, follows by projection: for
`hE : Function.Bijective E.moduleColimitMap`, Mathlib's `Function.Bijective`
is the conjunction `Function.Injective _ ∧ Function.Surjective _`, so `hE.2`
supplies the first hypothesis. Thus a proof `h` of the proposition yields
`h ι R S D M N E F f φ hE.2 hF` in that case.

## Provenance

This is an internal derived claim, not a separately numbered theorem of the
literature. It supports the final step of the proof of Stacks Project,
Lemma 10.128.4 (tag [046Y](https://stacks.math.columbia.edu/tag/046Y)), in the
registered original `stacks-algebra-flatness-criteria-2026-10-22` (content
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`;
file `046Y.html`, whose statement and complete proof were read). That proof
shows that for all sufficiently large `λ` "the map `u_λ` is injective and
that `N_λ/u_λ(M_λ)` is flat over `R_λ`", and then says "The lemma follows."
Passing from these component statements to `N/u(M)` uses that the cokernels
`N_λ/u_λ(M_λ)` have colimit `N/u(M)`. The source leaves this step implicit.
The present proposition is this cokernel–colimit compatibility for the
published Lean systems. No source-specific errata note for this source was
found in the current Library notes.

The claim is established by a representative-lifting and eventual-vanishing
argument:

- Surjectivity: a class in `N ⧸ range f` has a representative `n : N`, which
  lifts by surjectivity of `F.moduleColimitMap` to some `F.obj i`; its class
  in the component quotient maps to the given class.
- Injectivity: a component class `[n]` at index `i` whose image is zero
  satisfies `F.ιM i n = f m` for some `m : M`. Surjectivity of
  `E.moduleColimitMap` lifts `m` to some `y : E.obj k`. At a common upper
  index `l`, the difference of the transported `n` and
  `φ.component l (E.map k l _ y)` maps to zero in `N`. By injectivity of
  `F.moduleColimitMap` it vanishes at some later index `l'`. There the
  transported `n` lies in the range of `φ.component l'`, so its class is zero.

Only surjectivity of the source comparison enters this argument. The already
published ordinary theorem
`Langlands.Algebra.LocalModuleSystem.CompatibleMap.cokernelSystem_moduleColimitMap_bijective`,
in the module `Langlands.Algebra.LocalCompatibleMapApproximation`, has
precisely these hypotheses and this conclusion. This statement module does
not import that module, contains no proof, and does not restate or replace
that theorem. The exact-target proof of this proposition is a separate
obligation.

## Universes and imports

All nine universes are independent: `uI` for the index, `uA` and `uB` for the
base and algebra components of `D`, `uE` and `uF` for the component modules of
`E` and `F`, and `uR`, `uS`, `uM`, `uN` for the ambient rings and modules.
These are exactly the levels supported by `LocalModuleSystem.CompatibleMap`.
The cokernel components stay in `uF` and the target quotient stays in `uN`.

The module imports only the published
`Langlands.Algebra.LocalApproximationCokernel` by its Lean name. That module
provides `cokernelSystem`, and its own imports provide `LocalAlgebraSystem`,
`LocalModuleSystem`, `moduleColimitMap` and `CompatibleMap`. It does not modify that construction,
the helper theorem or their imports, and it adds only this proposition.
