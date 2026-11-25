# Lifts of continuous actions from lifts of near-identity automorphisms

This module proves the two halves of the Library proposition
`QuasiEtaleActionLiftStatement` for a rigid morphism `f : U ⟶ X`, in the
sense of the Library's `IsRigid`:

- **uniqueness:** any two lifts of a continuous action agree on an open
  subgroup;
- **existence:** a lift exists, provided that every automorphism of `X` close
  enough to the identity has a lift to `U` close to the identity.

Every quasi-étale morphism with compact source is rigid (Library,
`isRigid_of_quasiEtale`). The existence hypothesis is the content of the
proposition `QuasiEtaleAutomorphismLiftStatement`. This module does not import
that proposition: the hypothesis is spelled out in the theorem.

## Original sources

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.4,
printed p.7: "Recall that the Key Lemma 7.2 from [Ber3] implies that given a
quasi-étale morphism U → X with compact U there exist ε ∈ 𝔈(X), δ ∈ 𝔈(U) and
a unique continuous homomorphism 𝒢_ε(X) → 𝒢_δ(U) such that the morphism
U → X commutes with the action of 𝒢_ε(X). It follows that for any quasi-étale
morphism U → X with compact U the action of G on X extends in a canonical way
to a continuous action of some open subgroup G_U ⊂ G on U."

Berkovich gives no further detail. The argument below is the derived
deduction recorded in the Library's `QuasiEtaleActionLiftStatement.md`. The
lifted automorphisms are unique, hence multiply like `ρ` and are invertible.
Continuity comes from the closeness of the lifts.

## Declarations

All declarations are in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. `G` is a topological group,
and `X`, `U` are analytic spaces in `LocalizedCategory.{u, v, v}`.

- `ActionLift.exists_agreeOn (hf : IsRigid f) (a b : ActionLift ρ f)`: there
  is `N : Subgroup G` with `a.AgreeOn b N`.
- `nonempty_actionLift_of_automorphismLift (hρ : IsContinuousAction ρ)
  (hf : IsRigid f) hL : Nonempty (ActionLift ρ f)`. The hypothesis `hL` says:
  for every finite set `E` of test triples of `U` there is a finite set `D` of
  test triples of `X` such that every `σ : Aut X` with `σ ∈ nearIdentity τ`
  for all `τ ∈ D` has a `ψ : U ⟶ U` with `ψ ≫ f = f ≫ σ.hom` and
  `IsNear τ ψ (𝟙 U)` for all `τ ∈ E`. For a quasi-étale `f` with compact `U`
  and Hausdorff `X`, this is the conclusion of
  `QuasiEtaleAutomorphismLiftStatement`.

## Proofs

**Uniqueness.** Apply the Library's `exists_open_subgroup_intertwining` with
`p = q = f` and the identity of `U` as the morphism between them. Its
hypothesis on postcomposition holds trivially: for a test triple `τ` of `U`,
take `{τ}`. It returns an open subgroup `N` inside both lift subgroups with
`a(g) ≫ 𝟙 = 𝟙 ≫ b(g)` for `g ∈ N`. Hence `a(g) = b(g)` as isomorphisms
(`Iso.ext`).

**Existence.** Let `E₀` be the finite set of test triples of the rigidity of
`f`.

1. *Uniqueness of lifts.* Two morphisms `ψ₁`, `ψ₂ : U ⟶ U` that both lie over
   the same `σ` (`ψ_k ≫ f = f ≫ σ.hom`) and are both `E₀`-near `𝟙 U` are
   equal. This is rigidity applied with `ψ = 𝟙 U`.
2. *The open subgroup.* Apply `hL` to `E₀` and get `D₀`. Let `H` be the
   preimage under `ρ` of `⋂_{τ ∈ D₀} nearIdentitySubgroup τ`. It is a
   subgroup. By continuity of `ρ` it is a neighbourhood of `1`, so it is open
   (`Subgroup.isOpen_of_mem_nhds`).
3. *The lifts.* For `h ∈ H`, choose `ψ(h)` with `ψ(h) ≫ f = f ≫ ρ(h).hom`
   that is `E₀`-near `𝟙 U`. By step 1:
   - `ψ(1) = 𝟙 U`;
   - `ψ(h h′) = ψ(h′) ≫ ψ(h)`. Both sides lie over `ρ(h h′)`, and the right
     side is `E₀`-near the identity by `IsNear.comp_of_isNear_id`.

   Hence `ψ(h)` is an isomorphism with inverse `ψ(h⁻¹)`, and `h ↦ ψ(h)` is a
   homomorphism `H →* Aut U`. In `Aut U`, `(σ * σ').hom = σ'.hom ≫ σ.hom`.
4. *Continuity.* Let `τ` be a test triple of `U`. Apply `hL` to
   `insert τ E₀` and get `D`. The elements of `H` whose image under `ρ` lies in
   `nearIdentity σ` for all `σ ∈ D` form a neighbourhood of `1` in `H`. For
   such `h`, `hL` provides a lift that is `(insert τ E₀)`-near `𝟙 U`. By step
   1 that lift equals `ψ(h)`. So `ψ(h) ∈ nearIdentity τ`.
5. *Equivariance* is the defining property `ψ(h) ≫ f = f ≫ ρ(h).hom`.
