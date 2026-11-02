# Proof: invertibility of the base-change comparison of a map over spectra

The theorem
`Langlands.AlgebraicGeometry.Modules.DerivedSections.pushforwardBaseChangeOfIso`
has type exactly `PushforwardBaseChangeOfIsoStatement.{u}` (module
`Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOfIsoStatement`), at
an arbitrary universe `u` and with no further hypotheses. It uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The statement: for schemes `X`, `X'`, a ring map `φ : R ⟶ T`, morphisms
`f : X ⟶ Spec R`, `f' : X' ⟶ Spec T`, `g : X' ⟶ X` with
`w : g ≫ f = f' ≫ Spec.map φ`, modules `P` on `X` and `N` on `X'` and a map
`a : P ⟶ g_* N`, if `f_* P` and `f'_* N` are quasi-coherent and the scalar
sections comparison `scalarSectionsBaseChangeMapOf φ f f' g w a` is an
isomorphism, then the sheaf comparison
`pushforwardBaseChangeOf f (Spec.map φ) f' g w a : (Spec.map φ)^* f_* P ⟶ f'_* N`
is an isomorphism.

## Proof

`intro` fixes the data `X X' R T φ f f' g w P N a` and the three hypotheses.
Their types are type classes (`IsQuasicoherent`, `IsIso`), so they are local
instances for the rest of the proof. Put `P' = f_* P` on `Spec R` and
`Q = f'_* N` on `Spec T`, and write `Γ(P')` for the global sections module
`(relativeGlobalSections f).obj P`.

1. Both tilde counits `P'.fromTildeΓ : tilde Γ(P') ⟶ P'` and
   `Q.fromTildeΓ` are isomorphisms, by Mathlib's
   `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` applied to `P'` and
   `Q` with the two quasi-coherence hypotheses.
2. `tilde.map (scalarSectionsBaseChangeMapOf φ f f' g w a)` is an isomorphism,
   since it is the image of an isomorphism under the functor `tilde.functor T`
   (`inferInstanceAs`).
3. The published identity
   `pullback_fromTildeΓ_comp_pushforwardBaseChangeOf`
   (module `Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOf`)
   rewrites
   `(Spec.map φ)^* (P'.fromTildeΓ) ≫ pushforwardBaseChangeOf f (Spec.map φ) f' g w a`
   as `(tildePullbackIso φ Γ(P')).hom ≫ affineDirectImageTildeMapOf φ f f' g w a`.
   Unfolding `affineDirectImageTildeMapOf` gives the composite of the
   isomorphism `(tildePullbackIso φ Γ(P')).hom`, the isomorphism of step 2
   and the isomorphism `Q.fromTildeΓ` of step 1, so instance search shows the
   composite is an isomorphism.
4. `(Spec.map φ)^* (P'.fromTildeΓ)` is an isomorphism, as the image of the
   isomorphism of step 1 under the functor `Scheme.Modules.pullback (Spec.map φ)`.
   Mathlib's `IsIso.of_isIso_comp_left` then cancels it from the composite of
   step 3, so `pushforwardBaseChangeOf f (Spec.map φ) f' g w a` is an
   isomorphism.

This is the proof of the Library's unit case
`isIso_pushforwardBaseChange_of_isIso_scalarSectionsBaseChangeMap`
(module `Langlands.AlgebraicGeometry.Modules.AffineDirectImageBaseChange`),
with the arbitrary map `a` in place of the unit of `g^* ⊣ g_*` and the
`...Of` versions of the comparison maps and of the rewriting identity in place
of the unit-case ones.

The file sets `backward.isDefEq.respectTransparency false`, as the Library
modules `PushforwardBaseChangeOf` and `AffineDirectImageBaseChange` do. It is
needed: without it the instance search of step 3 fails to find `IsIso` for the
composite `(tildePullbackIso φ Γ(P')).hom ≫ tilde.map (…) ≫ Q.fromTildeΓ`.

## Dependencies

The module imports only the statement module
`Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOfIsoStatement`,
which imports `Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOf`;
the proof uses the proved Library results `pullback_fromTildeΓ_comp_pushforwardBaseChangeOf`
and the definitions `pushforwardBaseChangeOf`, `scalarSectionsBaseChangeMapOf`,
`affineDirectImageTildeMapOf` and `tildePullbackIso` from that import closure,
and Mathlib. It imports no flat higher-direct-image base-change statement, no
Mumford Euler statement and nothing downstream of them, and it adds no
hypothesis to the statement.

## Provenance

The statement is an internal generalization of the Library's unit case; its
Markdown (`PushforwardBaseChangeOfIsoStatement.md`) records the motivating
source, The Stacks Project, Cohomology of Sheaves, section "The base change
map" (tag 02N6), Lemma 02N7. The Lean proof above does not follow a source
proof; it is the affine tilde argument of the Library's unit case.

## Authorship

The Lean proof and the first version of this Markdown are Worker 1098's shared
draft (revision 1) of task `53d5b991-8c82-4226-bdbc-254bb368b486`; the Lean
file is unchanged. Worker 950 checked it and expanded this Markdown.
