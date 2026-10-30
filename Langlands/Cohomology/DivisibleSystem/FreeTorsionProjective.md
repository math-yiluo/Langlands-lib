# Free modules over `𝒪/ℓ^m𝒪[Γ]` are projective relative to objects killed by `ℓ ^ m`

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.HomSurjective` (`PowTorsionProjective`,
`homSystem_map_surjective`, `isMittagLeffler_homSystem`,
`towerHomEval_surjective`),
`Langlands.Cohomology.DivisibleSystem.PowTorsionProjective`
(`powTorsionProjective_of_iso`),
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (`repRestrictScalars`,
restriction of scalars of representations, and the local instance
`restrictScalarsModule`) and
`Langlands.Representation.Induction.PermutationInvariants`
(`Induction.compactInducedInvariants_free`). Through these imports it uses
`DivisibleSystem`, `DivisibleSystem.obj` and `powSMul`
(`Langlands.Cohomology.DivisibleSystem`), `homSystem` and `towerHomEval`
(`HomSystem`), and `Induction.compactInduced`
(`Langlands.Representation.Induction.Definitions`). From Mathlib it uses
`Rep`, `Rep.of`, `Rep.ofHom`, `Rep.mkIso`, `Rep.epi_iff_surjective`,
`Rep.equivalenceModuleMonoidAlgebra` (representations of `G` over `k` as
modules over the group algebra `MonoidAlgebra k G`, the module of `P` being
`P.ρ.asModule`), `RestrictScalars.addEquiv`, `Module.IsTorsionBySet` and
`Module.IsTorsionBySet.module`, `Module.Free`, `ModuleCat.projective_of_free`,
`Adjunction.projective_of_map_projective`, `Functor.Full`, `Functor.Faithful`,
`Functor.preimage`, `Functor.epi_of_epi_map`, `Projective.factorThru` and
`Ideal.mem_span_singleton'`.

## Conventions

`ℓ` and `m` are natural numbers. For a commutative ring `R`, `(ℓ ^ m)` denotes
the ideal `Ideal.span {((ℓ : R) ^ m)}` of `R` and `R ⧸ (ℓ ^ m)` the quotient
ring. `powSMul ℓ m X` is the published endomorphism "multiplication by
`ℓ ^ m`" of an object `X` (the `ℓ ^ m`-fold sum of the identity), and "`X` is
killed by `ℓ ^ m`" means `powSMul ℓ m X = 0`.

`PowTorsionProjective ℓ m P` is the published hypothesis that for every
epimorphism `p : X ⟶ Y` such that `X` is killed by `ℓ ^ m`, every morphism
`P ⟶ Y` lifts along `p`. Below it is read as "`P` is projective relative to
objects killed by `ℓ ^ m`".

Representations have carriers in one universe `w` (`Rep.{w}`). `G` is a
monoid unless stated otherwise.

## Restriction of scalars along a quotient (namespace `Langlands.Cohomology`)

`R` and `S` are commutative rings with an algebra structure `algebraMap R S`.
The published functor `repRestrictScalars R S G : Rep S G ⥤ Rep R G` keeps the
operators of a representation and lets `R` act through `algebraMap R S`; on
morphisms it keeps the underlying additive map.

- `repRestrictScalars_faithful G` (instance): restriction of scalars is
  faithful, because a morphism is determined by its underlying additive map.
- `repRestrictScalarsPreimage hS f`: for
  `hS : Function.Surjective (algebraMap R S)`, representations `A`, `B` over
  `S` and a morphism `f` between their restrictions of scalars, the same
  additive map as a morphism `A ⟶ B`. It is `S`-linear because every element
  of `S` is the image of an element `r` of `R` and `f` commutes with `r`.
  `repRestrictScalars_map_preimage hS f` states that restriction of scalars
  sends it to `f`.
- `repRestrictScalars_full_of_surjective G hS`: restriction of scalars along a
  surjective `algebraMap R S` is full.
- `repRestrictScalars_quotient_full I G` (instance): restriction of scalars
  along `R → R ⧸ I` is full, for every ideal `I` of `R`.

## Representations killed by an ideal

`I` is an ideal of `R` and `X` a representation of `G` over `R` with
`hX : Module.IsTorsionBySet R X I` (every element of `I` acts by zero on `X`).

- `torsionQuotientRepresentation X hX`: the representation of `G` over
  `R ⧸ I` on the same additive group with the same operators, where `R ⧸ I`
  acts through Mathlib's `Module.IsTorsionBySet.module` (the class of `r`
  acts as `r`). The operators are `R ⧸ I`-linear because every class lifts to
  `R`.
- `torsionQuotientRep X hX : Rep (R ⧸ I) G`: the corresponding object.
- `torsionQuotientRepIso X hX`: the isomorphism from the restriction of
  scalars of `torsionQuotientRep X hX` along `R → R ⧸ I` to `X`, the identity
  on the underlying additive group (`RestrictScalars.addEquiv`).
- `isTorsionBySet_of_epi p hX`: for an epimorphism `p : X ⟶ Y` in `Rep R G`,
  `Y` is killed by `I` as well (epimorphisms of `Rep` are surjective).
- `powSMul_hom_apply X x`: `powSMul ℓ m X` acts on a vector `x` as scalar
  multiplication by the element `(ℓ : R) ^ m`.
- `isTorsionBySet_of_powSMul_eq_zero h`: if `powSMul ℓ m X = 0`, then `X` is
  killed by the ideal `(ℓ ^ m)`.

## Free representations are projective

- `projective_of_free_asModule P hP`: for a commutative ring `k` and a
  representation `P` of `G` over `k` with
  `hP : Module.Free (MonoidAlgebra k G) P.ρ.asModule` (the module of `P` over
  the group algebra `k[G]` is free), `P` is projective in `Rep k G`. Free
  modules are projective in `ModuleCat` (`ModuleCat.projective_of_free`), and
  projectivity is transported along Mathlib's equivalence
  `Rep.equivalenceModuleMonoidAlgebra` between `Rep k G` and modules over
  `k[G]` (`Adjunction.projective_of_map_projective`).

## From projectivity over `R ⧸ (ℓ ^ m)` to relative projectivity over `R`

The remaining names are in the namespace
`Langlands.Cohomology.DivisibleSystem`.

- `powTorsionProjective_repRestrictScalars P`: for a projective object `P` of
  `Rep (R ⧸ (ℓ ^ m)) G`, its restriction of scalars to `R` satisfies
  `PowTorsionProjective ℓ m` in `Rep R G`. Proof: let `p : X ⟶ Y` be an
  epimorphism in `Rep R G` with `X` killed by `ℓ ^ m`, and `g` a morphism from
  the restriction of `P` to `Y`. Then `X` and `Y` are killed by the ideal
  `(ℓ ^ m)`, so they are restrictions of scalars of
  `torsionQuotientRep X _` and `torsionQuotientRep Y _` up to the isomorphisms
  `torsionQuotientRepIso`. Since restriction of scalars is full, `p` and `g`
  (composed with these isomorphisms) are images of morphisms `p'` and `g'`
  over `R ⧸ (ℓ ^ m)`; `p'` is an epimorphism because a faithful functor
  reflects epimorphisms (`Functor.epi_of_epi_map`). The lift
  `Projective.factorThru g' p'` of `g'` along `p'`, mapped back to `R` and
  composed with the isomorphism at `X`, lifts `g` along `p`.
- `powTorsionProjective_of_projective_torsionQuotientRep h`: for a
  representation `P` over `R` with `h : powSMul ℓ m P = 0` such that
  `torsionQuotientRep P _` is projective in `Rep (R ⧸ (ℓ ^ m)) G` (an instance
  argument), `P` satisfies `PowTorsionProjective ℓ m`. This is the previous
  result transported along `torsionQuotientRepIso P _`
  (`powTorsionProjective_of_iso`).

## Free modules over `(R ⧸ (ℓ ^ m))[G]`

- `FreeOverPowQuotient ℓ m P : Prop` (the entry declaration), for `P` in
  `Rep R G`: there is a proof `h` that `P` is killed by `ℓ ^ m`, and the module
  of `torsionQuotientRep P _` over the group algebra
  `MonoidAlgebra (R ⧸ (ℓ ^ m)) G` is free (`Module.Free`). Its underlying
  additive group is that of `P`, and the group algebra acts through the
  operators of `P` and the action of `R ⧸ (ℓ ^ m)` induced by that of `R`.
  This is Harris's "free `𝒪/ℓ^m𝒪[Γ]`-module" with `𝒪 = R` and `Γ = G`. The
  second condition does not depend on the choice of `h`, since any two proofs
  of a proposition are equal.
- `powTorsionProjective_of_freeOverPowQuotient hP`: `FreeOverPowQuotient ℓ m P`
  implies `PowTorsionProjective ℓ m P`, by `projective_of_free_asModule` over
  `R ⧸ (ℓ ^ m)` and the previous section.

For `ℓ`-divisible systems `T` and `W` in `Rep R G` (the published
`DivisibleSystem (Rep R G) ℓ`) with
`hT : ∀ m, FreeOverPowQuotient ℓ m (T.obj m)`, the published HomSurjective
results for the inverse system `homSystem R T W` of `R`-modules
`m ↦ Hom_G(T m, W m)` hold:

- `homSystem_map_surjective_of_freeOverPowQuotient T W hT φ`: every
  transition `(homSystem R T W).map φ`, for `φ : m ⟶ m'` in `ℕᵒᵖ`, is
  surjective;
- `isMittagLeffler_homSystem_of_freeOverPowQuotient T W hT`: the system
  `homSystem R T W`, composed with the forgetful functor to types, satisfies
  the Mittag-Leffler condition;
- `towerHomEval_surjective_of_freeOverPowQuotient T W hT n`: every morphism
  `T n ⟶ W n` is the level-`n` component of a morphism of inverse systems
  `T.tower ⟶ W.tower` (surjectivity of the published `towerHomEval`).

Each is the published lemma (`homSystem_map_surjective`,
`isMittagLeffler_homSystem`, `towerHomEval_surjective`) with its hypothesis
supplied by `powTorsionProjective_of_freeOverPowQuotient`.

## Invariants of compact inductions

Here `G` is a topological group, `H` and `K` are subgroups with `H` open
(`hH`), `H ≤ K` (`hHK`), `K` normal and `H` of finite index in `K`, and `I` is
a type. The published `Induction.compactInducedInvariants_free` states that
the `K`-invariants of the compact induction from `H` of the trivial
representation on `I →₀ k`, as a representation of `G ⧸ K`, form a free
module over `k[G ⧸ K]`.

- `projective_compactInducedInvariants k hH hHK I`: this representation of
  `G ⧸ K` is projective in `Rep k (G ⧸ K)` (`projective_of_free_asModule`).
- `powTorsionProjective_compactInducedInvariants hH hHK I`: for
  `k = R ⧸ (ℓ ^ m)`, its restriction of scalars to `R` satisfies
  `PowTorsionProjective ℓ m` in `Rep R (G ⧸ K)`
  (`powTorsionProjective_repRestrictScalars`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312
(one-based PDF page 14; Worker 61 read the rendered scanned page), after the
definition of `T_m(j, ẽ)` and the maps (4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)`:
"Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective
for all `m`."

The published HomSurjective module abstracts the freeness of the source used
in this argument as the hypothesis `PowTorsionProjective`. This module proves
that Harris's freeness implies that hypothesis. In our reading, `𝒪` is the
coefficient ring `R`, `𝒪/ℓ^m𝒪` is `R ⧸ (ℓ ^ m)`, and the group
`S(ẽ)/H_p` is `G` (or `G ⧸ K` in the last section). Harris's morphisms over
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]` correspond to morphisms in `Rep R G`: for objects killed
by `ℓ ^ m`, restriction of scalars along `R → R ⧸ (ℓ ^ m)` is full and
faithful. The published results need only the condition on the source; the
target is any `ℓ`-divisible system. Harris also uses the freeness of the
target, which plays no role here.

The last section connects the result to the published
`compactInducedInvariants_free`. On printed pp.311-312, `C^j(ẽ)` is chosen to
be a direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules. As in the published
PermutationInvariants module, `G`, `K` and `H` would correspond to `S(ẽ)`,
`H_p` and a member of the family `H(ẽ)`. This correspondence is our
interpretation.

That free modules over a ring are projective, and that a free
`𝒪/ℓ^m𝒪[Γ]`-module has the lifting property against surjections of modules
killed by `ℓ ^ m`, are standard. The predicate `FreeOverPowQuotient`, the
route through restriction of scalars and all proofs are ours; the module is
derived.

## Scope

The module does not prove that Harris's modules `C^j_m(ẽ)^{H_p}` are free over
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`. Direct limits are not treated, so the passage from the
free modules in the direct limit to `C^j_m(ẽ)` is not formalized. It does not
treat the modules `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`, and it proves no converse.
Relative projectivity is proved in the categories `Rep R G` and
`Rep R (G ⧸ K)` of representations of abstract groups, not in categories of
smooth representations. The Mittag-Leffler statements concern the Hom
systems in a single degree. The Hom complexes (4.10.2), the finiteness of the
right-hand side of (4.9) and the spectral sequence are not treated.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
