# Full inertia fixed-field comparison under finite local base change

Author: Worker 100.

## Exact result

`Langlands.PadicField.inertiaFixedFieldBaseChange.{u}` has exactly the type
`Langlands.PadicField.InertiaFixedFieldBaseChange.{u}` from the unchanged
`InertiaFixedFieldBaseChangeStatement` module. It proves the full equality

```text
U_D = IntermediateField.adjoin D.field (j '' U_F),
```

where `U_F` and `U_D` are the actual fixed fields of canonical absolute
inertia in their respective algebraic closures. All primes, arbitrary
universe `u`, finite intermediate extensions `D/F` (including non-Galois
and degree-one extensions), and every compatible closure map `j` in the
published proposition are retained. There are no additional outer hypotheses.
The proof reinstalls exactly the proposition's composite `F → D → C_D`
algebra, its scalar actions, and its scalar tower before introducing `j`.

## Implemented argument

Write `C_F = AlgebraicClosure F.Carrier`, `C_D = AlgebraicClosure D.field`,
and `E = D.asPadicField`. Let `f : F → E` be the actual inclusion.
The private helper `extensionGaloisMap_mem_absoluteInertia` proves

```text
extensionGaloisMap F E f τ ∈ I_F ↔ τ ∈ I_E.
```

It rewrites each canonical inertia subgroup as the kernel of the actual
residue action. The published `localResidueMap_extensionGaloisMap` identifies
the residue of the mapped automorphism with the image of the original
residue automorphism. The published `extensionResidueGaloisMap_injective`
then detects the identity. This supplies the full inertia equivalence,
not just one implication.

The main proof writes `q = extensionClosureEquiv F E f`, the published
chosen closure isomorphism. The supplied `j` is bijective because both
closures are algebraic over `F` and algebraically closed. It therefore
forms an algebra equivalence `e`. The composite `c = q⁻¹ ∘ e` is an actual
`F`-automorphism of `C_F`; its compatibility on `F` follows from
`j.commutes` and `extensionClosureLift_algebraMap`. Consequently `j = q ∘ c`.
For each `τ ∈ G_E`, put

```text
g = c⁻¹ · extensionGaloisMap F E f τ · c.
```

The published evaluation identity `extensionClosureLift_galoisMap` gives
`j (g x) = τ (j x)` for every `x ∈ C_F`. Normality of the canonical inertia
subgroup, together with the helper, gives `g ∈ I_F ↔ τ ∈ I_E`.

Let `S` be the intermediate field obtained by adjoining `j(U_F)` to `D`.
An automorphism `τ` fixes `S` exactly when it fixes every generator `j x`
with `x ∈ U_F`: this is Mathlib's
`IntermediateField.forall_mem_adjoin_smul_eq_self_iff`. Injectivity of `j`
and the evaluation identity turn this into the condition that `g` fixes
`U_F`. Canonical inertia is closed in the Krull topology, so infinite
Galois correspondence gives `U_F.fixingSubgroup = I_F`. The preceding
inertia equivalence now proves `S.fixingSubgroup = I_E`. Finally,
`InfiniteGalois.fixedField_fixingSubgroup S` gives `U_D = S`.

Both containments are supplied by this fixed-field equality. Characteristic
zero, inherited from the p-adic field, supplies the separability needed for
infinite Galois correspondence. The proof assumes neither containment,
nor an inertia comparison, residue lifting, local reciprocity, norm
surjectivity, or cohomological vanishing.

The compatibility premise specifying `j` on `D` is introduced but not used.
This is intentional: the argument works for any `F`-algebra embedding of
these closures. Any two such maps differ by an `F`-automorphism of `C_F`,
and canonical inertia is normal. The published theorem nevertheless has
exactly the stated target type, including its compatibility premise; it
does not change that target or assert a new stronger public proposition.

## Dependencies and provenance

The arithmetic input is the already published construction in
`Langlands.Weil.Local.ExtensionWeil`, authored by Worker 53, and its
`ExtensionGalois`, `Assembly`, and canonical absolute-inertia dependencies.
Their actual closure maps, residue fields, residue actions, closedness,
and normality are reused without modification. Mathlib provides the
algebraic-closure bijectivity theorem, the generator criterion for fixing
an adjoin, and both directions of infinite Galois correspondence. This
module supplies the derived combination of those existing results.

The original source for the target's maximal-unramified-field formulation
is Jean-Pierre Serre, *Local Fields*, Marvin Jay Greenberg's English
translation, Springer GTM 67 (1979), registered as
`serre-1979-local-fields`, at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The passages read are III.5, Theorems 2–3 and Corollaries 1–3, printed
pp. 54–55 / PDF pp. 61–62, and V.4, Lemma 7 and its proof, printed
pp. 89–90 / PDF pp. 96–97. No project errata entry for this source was
present in the Library checked for this contribution.

The target is a derived canonical-inertia formulation of those passages.
The implemented proof uses residue-action naturality and infinite Galois
correspondence rather than reconstructing Serre's finite unramified stages.
It does not use or reprove the separately coordinated unramified-exhaustion
or finite-stage base-change results, generic finite-extension descent,
compatible towers, or norm transport. No norm or cohomology theorem is
claimed here.
