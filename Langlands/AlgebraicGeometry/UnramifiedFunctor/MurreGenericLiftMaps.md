# Lifting lemmas for Murre's Lemma 2, case (b)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericLiftMaps`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.GenericLift`. It supports the proof of
`EtaleLocus.GenericNoLargerLiftStatement` (see `MurreGenericNoLargerLift.md` and
`MurreGenericNoLargerLiftProof.md`) and imports the published module `MurreLocalToGlobalSteps`
(for `InfinitesimallyEtaleAt`), together with Mathlib's Nakayama lemma, formally unramified
algebras and zero-dimensional rings. `algebraOver`, `algebraOverBase`, `algHomOver`,
`restrictQuotient` and `NoLargerLift` are those of the published `MurreCriterionStatement`.
All results use only the standard axioms.

Throughout, `S` is a scheme and `F : (Over S)ᵒᵖ ⥤ Type v`.

## Ring maps as morphisms over `S` (section `RHom`)

- `rhom ψ h : Over.mk g₁ ⟶ Over.mk g₂` is the morphism with underlying map
  `Spec.map (CommRingCat.ofHom ψ)`, for a ring map `ψ : T₂ →+* T₁` and structure morphisms
  `g₁ : Spec T₁ ⟶ S`, `g₂ : Spec T₂ ⟶ S` with `h : Spec ψ ≫ g₂ = g₁`. `rhom_left` computes
  its underlying morphism.
- `spec_comp₁₁`, `spec_comp₁₂`, `spec_comp₂₁` turn an equality of composites of ring maps
  (for example `ψ.comp α = β.comp γ`) into the corresponding equality of composites of their
  `Spec.map`s followed by a morphism `g`. These produce the side conditions `h`.
- `rhom_comp`: `rhom ψ₁ h₁ ≫ rhom ψ₂ h₂ = rhom (ψ₁.comp ψ₂) _`. `rhom_congr`: `rhom` depends
  only on `ψ`. `rhom_id`: `rhom (RingHom.id _) _ = 𝟙 _`.
- `map_rhom_map_rhom`, `map_rhom_eq`, `map_rhom_eq'`: the same facts for the maps
  `F.map (rhom ψ h).op` on elements.

## The maps of `NoLargerLift` (section `Forms`)

For `f : Spec A ⟶ S`: `algebraOverBase_eq` and `algHomOver_eq` say that `algebraOverBase f B`
and `algHomOver f φ` are `rhom (algebraMap A B) _` and `rhom φ _`. Both hold by `rfl`.
`noLargerLift_iff` restates `NoLargerLift B ξ'` with its two maps written as `rhom`s: the
quotient map `Ideal.Quotient.factor : B/J → B/IB` and `Ideal.quotientMap : A/I → B/IB`. It
also holds by `rfl`.

## Change of base ring (section `BaseChange`)

Let `f : Spec R' ⟶ S`, `A` an `R'`-algebra and `𝔍` an ideal of `R'`. `baseOver f A` is the
composite `Spec A ⟶ Spec R' ⟶ S`. `restrictBase f A 𝔍 ξ` is the restriction of
`ξ ∈ F(algebraOver f (R' ⧸ 𝔍))` to `Spec (A/𝔍A)`, as an object over `S` through `Spec A`.

`noLargerLift_restrictBase_iff`: for an `A`-algebra `C` with `R' → A → C` a scalar tower,
`NoLargerLift (f := baseOver f A) C (restrictBase f A 𝔍 ξ) ↔ NoLargerLift (f := f) C ξ`.

Proof. The ideals `(𝔍A)C` and `𝔍C` coincide (`map_map_eq`). A candidate lift `η` over
`Spec (C/J)`, viewed over `S` through `Spec A`, corresponds to the same `Spec (C/J)` viewed
through `Spec R'`. The two are related by `rhom (RingHom.id _)`. So a lift for one base gives
a lift for the other. Each direction compares the two restrictions to `Spec (C/𝔍C)` by
applying `F.map` of the identification `C/𝔍C = C/(𝔍A)C` to the given equality, and then
rewriting composites of `rhom`s with `map_rhom_map_rhom` and `map_rhom_eq'`.

## Nakayama transfer (section `Nakayama`)

`noLargerLift_of_surjective`: let `π : B →ₐ[R'] C` be a surjection of `R'`-algebras with `B`
local noetherian and `ker π ≤ 𝔪_B · 𝔍B`. Then `NoLargerLift C ξ → NoLargerLift B ξ`.

Proof. Let `J < 𝔍B` and let `η` over `Spec (B/J)` restrict to the restriction of `ξ`. Push
`η` forward along the induced map `B/J → C/π(J)C`. Then `π(J)C ≤ 𝔍C` because `π(𝔍B) = 𝔍C`.
If equality held, every `x ∈ 𝔍B` would satisfy `π x = π j` for some `j ∈ J`, so
`x - j ∈ ker π ⊆ 𝔪_B · 𝔍B`. That gives `𝔍B ≤ J ⊔ 𝔪_B · 𝔍B`. Nakayama's lemma
(`Submodule.le_of_le_smul_of_le_jacobson_bot`; `𝔍B` is finitely generated, and `𝔪_B` is the
Jacobson radical) would then give `𝔍B ≤ J`, contradicting `J < 𝔍B`. Hence `π(J)C < 𝔍C`. The
pushed-forward element restricts to the restriction of `ξ` to `Spec (C/𝔍C)`: apply `F.map`
of `B/𝔍B → C/𝔍C` to the given equality. This contradicts `NoLargerLift C ξ`.

## Infinitesimal étaleness along surjections (section `Infinitesimal`)

`exists_lift_of_surjective`: `InfinitesimallyEtaleAt F ξ y` is stated with quotient maps
`L → L/J`. This lemma gives the lifting property for any surjection `π : L → D` with
nilpotent kernel, `L` local artinian. Given `u₀ : Spec D ⟶ U` sending every point to `y` and
`v ∈ F(Spec L)` compatible with `ξ` on `Spec D`, there is `u : Spec L ⟶ U` with
`rhom π _ ≫ u = u₀` and `F.map u.op ξ = v`. Proof: apply the definition to `J = ker π`, and
transport along the isomorphism `L/ker π ≅ D`, `RingHom.quotientKerEquivOfSurjective`.

## Artinian local rings (section `Artinian`)

`noLargerLift_of_isArtinianRing`: let `R` be a ring and `R'` a formally unramified
`R`-algebra. Let `ξ ∈ F(algebraOver (Spec R' ⟶ Spec R) (R'/𝔍))` be infinitesimally étale at
`y ∈ Spec (R'/𝔍)`. Let `C` be a local artinian `R'`-algebra (with `R → R' → C` a scalar
tower) whose maximal ideal lies over the prime `y.asIdeal.comap (Ideal.Quotient.mk 𝔍)` of
`R'`. Then `NoLargerLift C ξ`.

Proof. Let `J < 𝔍C` and let `η` over `Spec (C/J)` restrict to the restriction of `ξ` on
`Spec (C/𝔍C)`. Then `C/J` is local artinian, and `π : C/J → C/𝔍C` is surjective with
nilpotent kernel: the kernel lies in the maximal ideal, which is nilpotent in an artinian
local ring. The map `u₀ : Spec (C/𝔍C) ⟶ Spec (R'/𝔍)` induced by `R'/𝔍 → C/𝔍C` sends the
unique point to `y`. `exists_lift_of_surjective` gives `u : Spec (C/J) ⟶ Spec (R'/𝔍)` over
`Spec R`. Write `u = Spec σ` (`Spec.preimage`). Then:

- `σ ∘ mk` is an `R`-algebra map `R' → C/J`, because `u` is a morphism over `Spec R`;
- `π ∘ σ` is the map `R'/𝔍 → C/𝔍C`, because `rhom π _ ≫ u = u₀`.

So `σ ∘ mk` and the structure map `R' → C/J` agree after composing with `π`, whose kernel is
nilpotent. Formal unramifiedness of `R'` over `R` (`Algebra.FormallyUnramified.ext'`) makes
them equal. Hence `𝔍` maps to zero in `C/J`, that is `𝔍C ≤ J`, a contradiction.

This is step 1 of Murre's case (b) (printed p.251, PDF p.10 of
`murre-1965-bourbaki-294-unramified-functors`, SHA-256
`e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`). Murre deduces it from
the closed immersion `ξ_(y)` and the étale map of local rings. Here it is derived directly
from infinitesimal étaleness (SGA 3, XI, Remark 1.8) and formal unramifiedness.
