# Nonnegative tensor powers of global module-sheaf sections

This module defines `Langlands.SchemeModule.sectionPow` for every scheme
`X : AlgebraicGeometry.Scheme.{u}`, actual module sheaf `M : X.Modules`,
section `s : Langlands.SchemeModule.GlobalSections M`, and natural number `n`.
Its value is a global section of
`Langlands.Scheme.Modules.tensorPow M n`. There are no freeness, rank,
quasicoherence, affineness, separatedness, or noetherianity assumptions.

## Recursive construction

The object powers are the existing right-associated `tensorPow`. Their
zeroth object is the actual structure module, and the successor object is
`tensorObj M (tensorPow M n)`. The definition follows that same recursion:

```lean
sectionPow M s 0 = (1 : Γ(X, ⊤))
sectionPow M s (n + 1) =
  tensorSection M (tensorPow M n) s (sectionPow M s n)
```

The carrier of `Γ(X, ⊤)` is definitionally the carrier of the global
sections of the structure module. Writing one in this ring supplies the
unit section without introducing a ring instance on the module-section
type. `sectionPow_zero` and `sectionPow_succ` are these definitional
equations.

Both `Langlands.SchemeModule.structureModule X` and
`Langlands.Scheme.Modules.structureSheaf X` reduce to Mathlib's
`SheafOfModules.unit X.ringCatSheaf`. The lemma
`sectionHom_sectionPow_zero` makes this identification explicit: the
zeroth section's `sectionHom` is the identity of `structureModule X`.
Its proof applies injectivity of `unitHomEquiv`, compares the resulting
compatible families on every open, and uses that ring restriction maps
preserve one.

`sectionHom_sectionPow_succ` records the actual successor morphism as
the inverse left unitor of the structure module followed by the tensor
of `sectionHom M s` with the lower power's `sectionHom`. It is precisely
the tensor-section characterization, specialized to the recursive factors.
Thus the construction uses the actual sheafified tensor product section.

There is a trailing structure-module factor in each positive power:
the first object power is `tensorObj M (structureSheaf X)`. This file
does not silently replace that object by `M`, or change the chosen
association of any power.

## Naturality

For every actual module-sheaf morphism `f : M ⟶ N`,
`sectionPow_naturality f s n` states exactly

```lean
(tensorPowMap f n).app ⊤ (sectionPow M s n) =
  sectionPow N (f.app ⊤ s) n
```

for all natural numbers `n`, including zero. The proof is induction on `n`.
At zero both sides are the unit section and `tensorPowMap f 0` is the
identity. At a successor, `tensorSection_naturality` applies `f` to the
first factor and `tensorPowMap f n` to the second factor; the induction
hypothesis identifies the second image.

`sectionHom_sectionPow_naturality` expresses the same compatibility as
the equation

```lean
sectionHom (tensorPow N n) (sectionPow N (f.app ⊤ s) n) =
  sectionHom (tensorPow M n) (sectionPow M s n) ≫ tensorPowMap f n
```

by combining the section equation with `sectionHom_naturality`.

## Provenance and scope

These are internal derived definitions giving a categorical realization
of the section power used in the proof of Stacks Project Lemma 28.27.2,
tag [01PT](https://stacks.math.columbia.edu/tag/01PT). The registered
source is `stacks-ample-powers-restriction-quasiaffine-2026-10-24`,
retained in *Stacks Project - Ample powers, closed restriction and
quasi-affineness (HTML snapshot 2026-10-24)*, file `01PT.html`,
directory SHA256
`03dddd39b5528263fbc3633f1545b8544e937bb29c9752ffe4a351bb6e093e9a`.
The proof and both comments were read; the current official page was
also checked on 2026-10-26. The comments add the EGA II 4.5.6(i)
reference and qualify the EGA version's quasicompactness assumption;
they do not amend the Stacks statement.

The source's power notation motivates this recursive construction;
the exact Lean recursion and trailing-unit convention are internal
choices inherited from the Library's `tensorPow`. The geometric
equality of generation opens for positive powers, tensor-power
flattening, and ampleness transport are separate obligations and
are not proved here.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
