# The sheaf of invariant sections along a natural action

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.NaturalActionSections` (imported): natural actions
  `NaturalAction K Φ` of a monoid `K` along a functor `Φ : E ⥤ T` (fields `act` and `comm`),
  and, for a group `K`, the presheaf of invariant sections `a.invariantPresheaf R F`
  (`V ↦ F(Φ V)^K`), the functor `a.sheafInvariantFunctor R J` from module sheaves on `T` to
  module presheaves on `E`, and its finite-limit instance. Through the imports,
  `actionRepresentation F b` from `Langlands.Sheaf.Equivariant.LocalActionCohomology`: the
  representation of `K` on `F(U)` in which `k` acts by `F.map (b k).unop.op`.
- Mathlib: `Presheaf.IsSheaf` (the sheaf condition for presheaves with values in a category
  `A`: `coyoneda.obj (op M)` composed with the presheaf is a sheaf of types for every object
  `M`), `Presieve.FamilyOfElements.map`, `Presieve.IsSheafFor.isSeparatedFor`,
  `Functor.whiskerRight`, `cancel_mono`, `ModuleCat.mono_iff_injective`,
  `Representation.invariants`, `LinearMap.codRestrict`, `Functor.op_comp_isSheaf` (for a
  continuous functor `Φ`, `Φ.op ⋙ F` is a sheaf whenever `F` is), `ObjectProperty.lift`,
  `ObjectProperty.liftCompιIso`, `preservesFiniteLimits_of_natIso`,
  `preservesFiniteLimits_of_reflects_of_preserves`, `sheafToPresheaf`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant`.

## Purpose

`NaturalActionSections` constructs the presheaf `V ↦ F(Φ V)^K` of invariant sections along a
natural action, but does not address the sheaf property. This module proves it: if
`Φ.op ⋙ F` is a sheaf, then so is the presheaf of invariant sections. For a continuous `Φ`
the construction therefore gives a left exact functor from module sheaves on `T` to module
sheaves on `E`. For a `G`-space `X`, that functor is Berkovich's `(b_*F)^G`, constructed in
`AnalyticInvariantSheaf`.

## A joint equalizer of endomorphisms of a sheaf is a sheaf

Let `E : Type uE` with `[Category.{vE} E]`, `A : Type uA` with `[Category.{vA} A]`, and `J`
a Grothendieck topology on `E`.

- `isSheaf_of_isJointEqualizer hP ι e he hfac`. Data:
  - `P Q : Eᵒᵖ ⥤ A` with `hP : Presheaf.IsSheaf J P`;
  - `ι : Q ⟶ P` with `[∀ V, Mono (ι.app V)]`;
  - a family `e : I → (P ⟶ P)` of endomorphisms, indexed by any type `I`;
  - `he : ∀ k V, ι.app V ≫ (e k).app V = ι.app V`;
  - `hfac`: for every object `M` of `A`, every `V` and every `t : M ⟶ P.obj V` with
    `t ≫ (e k).app V = t` for all `k`, there is `t' : M ⟶ Q.obj V` with
    `t' ≫ ι.app V = t`.

  Conclusion: `Presheaf.IsSheaf J Q`.

  Proof: fix `M`, a covering sieve `S` of `V` and a compatible family `x` of morphisms
  `M ⟶ Q.obj Y`. Composing with `ι` gives a compatible family for `P`, which glues to
  `t : M ⟶ P.obj V`. For each `k`, the morphism `t ≫ (e k).app V` glues the family `x`
  composed with `ι ≫ e k`, which is `x` composed with `ι` by `he`. Separatedness of `P` gives
  `t ≫ (e k).app V = t`. By `hfac`, `t` factors as `t' ≫ ι.app V`. The morphism `t'` glues `x`,
  and it is unique, because `ι` is a monomorphism and `P` is separated. The universes of `I`
  and `A` are arbitrary.

## Invariant sections

Let `T : Type u` with `[Category.{v} T]`, `K : Type uK` a group, `Φ : E ⥤ T`,
`a : NaturalAction K Φ`, and `R : Type uR` a commutative ring; modules are in
`ModuleCat.{w} R`. Let `F : Tᵒᵖ ⥤ ModuleCat.{w} R`.

- `a.invariantPresheafι R F : a.invariantPresheaf R F ⟶ Φ.op ⋙ F`: componentwise the
  inclusion of the invariant submodule
  `(actionRepresentation F (a.act V.unop)).invariants`. `invariantPresheafι_app_apply`: it
  sends an invariant section `s` to `s.1`. Naturality holds by `rfl`.
- `invariantPresheafι_mono` (instance): each component is a monomorphism (injective).
- `a.sectionsEndo R F k : Φ.op ⋙ F ⟶ Φ.op ⋙ F`, for `k : K`: at `V` the restriction
  `F.map (a.act V.unop k).unop.op`, the action of `k` on `F(Φ V)` (`sectionsEndo_app`).
  Naturality follows from `a.comm`.
- `a.isSheaf_invariantPresheaf R hF`: if `hF : Presheaf.IsSheaf J (Φ.op ⋙ F)`, then
  `Presheaf.IsSheaf J (a.invariantPresheaf R F)`. Proof: `isSheaf_of_isJointEqualizer` with
  `ι = a.invariantPresheafι R F` and `e = a.sectionsEndo R F`. Invariant sections are fixed by
  every `a.sectionsEndo R F k`. A linear map fixed by all of them has invariant values, so it
  factors through the invariant submodule by `LinearMap.codRestrict`.

## The sheaf functor

Let `J` be a Grothendieck topology on `T` and `JE` one on `E`, with `[Φ.IsContinuous JE J]`.

- `a.sheafInvariantSheafFunctor R J JE : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf JE (ModuleCat.{w} R)`:
  the lift of `a.sheafInvariantFunctor R J` to sheaves. Its value at a sheaf `F` is the
  invariant presheaf of `F.obj`, which is a sheaf by `isSheaf_invariantPresheaf` and
  `Functor.op_comp_isSheaf`. `sheafInvariantSheafFunctor_obj_obj` states this by `rfl`.
- `a.sheafInvariantSheafFunctorCompIso R J JE`: followed by `sheafToPresheaf JE`, it is
  isomorphic to `a.sheafInvariantFunctor R J` (`ObjectProperty.liftCompιIso`).
- `sheafInvariantSheafFunctor_preservesFiniteLimits` (instance): it preserves finite limits.
  Its composite with `sheafToPresheaf JE` is isomorphic to `a.sheafInvariantFunctor R J`,
  which is left exact (`NaturalActionSections`), and `sheafToPresheaf JE` preserves and
  reflects finite limits.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`; proof of
Theorem 1.4.2, step A.4, printed p.9, where `(b_*F)^G(V(G)) = F(V)^G` is called a sheaf on
`X(G)~_qét` without proof. The quotation is in `NaturalActionSections.md`.

## Provenance

Derived. Berkovich gives no proof of the sheaf property. The argument here is standard:
invariants are an equalizer, and limits of sheaves are sheaves. It is phrased as
`isSheaf_of_isJointEqualizer` so that it applies to any family of endomorphisms, with no
condition on the universe of the index type. The geometric input, that `Φ.op ⋙ F` is a
sheaf, is kept as a hypothesis or comes from continuity of `Φ`. For a `G`-space it is
discussed in `AnalyticInvariantSheaf.md`.
