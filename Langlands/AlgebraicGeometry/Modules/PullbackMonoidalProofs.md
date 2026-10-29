# Monoidality of canonical identity and composite pullback comparisons

This proof targets
`Langlands.Scheme.Modules.PullbackComparisonsMonoidalStatement` from
`PullbackMonoidalStatements`, in arbitrary universe `u`. It concerns the
canonical strong symmetric monoidal structures of `PullbackMonoidal` on
the existing functors `Scheme.Modules.pullback`.

Write `F_f = Scheme.Modules.pullback f`,
`c_X(M,N) = localizedTensorIso X M N`,
`D_f(M,N) = pullbackTensorComparisonApp f M N`, and
`d_f(M,N) = localizedPullbackTensorComparisonApp f M N`. The fixed
comparison formula is

`d_f(M,N) = F_f.map c_Y(M,N).hom ≫ D_f(M,N) ≫ c_X(F_f M,F_f N).inv`.

The lemma `localizedPullbackTensorIdentity` proves

`d_id(M,N) ≫ (i_M ⊗ₘ i_N) = i_(M ⊗ N)`,

where `i` is the forward transformation of the existing `pullbackId`.
The proof cancels `c_X(M,N).hom`, expands the displayed formula, uses
naturality of `c_X` at `i_M,i_N`, and cancels the adjacent inverse and
forward maps. The explicit identity law `pullbackTensorIdentity` then
reduces the goal to naturality of `i` at `c_X(M,N).hom`.

The lemma `localizedPullbackTensorComposition` proves

`k_(M ⊗ N) ≫ d_(f ≫ g)(M,N) =
 F_f.map d_g(M,N) ≫ d_f(F_g M,F_g N) ≫ (k_M ⊗ₘ k_N)`,

where `k` is the forward transformation of the existing
`pullbackComp f g : F_g ⋙ F_f ≅ F_(f ≫ g)`. It cancels the target
`c_X.hom`, expands the three localized comparisons, and uses naturality
of `c_X` at `k_M,k_N`. The two intermediate comparison isomorphisms cancel,
one after applying `F_f`. Naturality of `k` at `c_Z(M,N).hom` and the
published explicit law `pullbackTensorComposition` finish the equation.

The private helper `isMonoidal_of_oplax` converts these oplax equations
to the lax equations of `NatTrans.IsMonoidal`. For a transformation
`τ : F ⟶ G` between strong monoidal functors, it takes

- `τ_(𝟙) ≫ η_G = η_F`;
- `τ_(M ⊗ N) ≫ δ_G(M,N) = δ_F(M,N) ≫ (τ_M ⊗ₘ τ_N)`.

It cancels the invertible `η_G` or `δ_G(M,N)` on the right and uses
`ε ≫ η = 𝟙` or `μ ≫ δ = 𝟙`. This gives precisely the unit and tensor
fields of a monoidal natural transformation in pinned Mathlib.

`pullbackIdentityMonoidal` combines this helper with
`pullbackUnitIdentity` and the localized tensor identity. Here the target
identity functor has identity oplax maps. `pullbackCompositionMonoidal`
uses `pullbackUnitComposition` and the localized tensor composition;
the source composite functor has the usual composite oplax maps
`F_f.map η_g ≫ η_f` and `F_f.map δ_g(M,N) ≫ δ_f(F_g M,F_g N)`.
In both proofs the `change` steps unfold the oplax maps of the canonical
structure definitionally: `η_f` is `(pullbackUnitIso f).hom` and
`δ_f(M,N)` is `d_f(M,N)`, as recorded by the `rfl` lemmas
`pullbackMonoidal_η` and `pullbackMonoidal_δ` in `PullbackMonoidal`.
The unit object of `X.Modules` is unfolded to `structureSheaf X`, which
is the module `SheafOfModules.unit X.ringCatSheaf` used in the unit laws.

The theorem `pullbackComparisonsMonoidal` is exactly the conjunction of
these two constituents. The instances `pullbackId_isMonoidal` and
`pullbackComp_isMonoidal` expose the same results for the existing
forward transformations; Mathlib's existing instance gives monoidality
of their inverses. No coherence or preservation premise is added.

This is an internal categorical proof from the already proved unit and
explicit tensor laws, using the definitions in pinned Mathlib's
`CategoryTheory/Monoidal/NaturalTransformation.lean` and
`CategoryTheory/Monoidal/Functor.lean`.
