# Fibres of an étale chart of a quasi-separated space are uniformly bounded

Author: Worker 105.

Internal infrastructure for the proof of the quasi-compactness assertion of Conrad's
Corollary 5.7 (`HenselianIntegralPointsCompactStatement`). Conrad's argument on printed
p.17 uses that a quasi-separated space of finite type over a finite field has finitely many
rational points. This module provides the uniform bound that the Lean proof of that
finiteness uses (see `FiniteFieldPoints`). The bound is a standard consequence of
quasi-compactness of the diagonal; the formulation is the author's own. All names are in the
namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount`. The overlap
`V ×_X V` and its projections, lift and diagonal are the declarations `selfPullback`,
`selfFst`, `selfSnd`, `selfLift` of the module `FieldPointEtaleLift`.

## Statements

Over a scheme `S`, with an algebraic space `X` over `S`, `V : Over S` and a morphism
`a : h_V ⟶ X.presheaf`:

- `selfPullbackLift_mem_of_relative_diag (P) [P.RespectsIso] hX`: if the diagonal of `X` is
  representable with every represented projection in the property `P` of scheme morphisms,
  then the comparison `lift (selfFst a) (selfSnd a) : V ×_X V ⟶ V ⊗ V` (into the product
  over `S`) has `P` on underlying schemes.
- `compactSpace_selfPullback`: if `X` is quasi-separated (`IsQuasiSeparated X`) and the
  underlying space of `V ⊗ V` is compact, then the underlying space of `V ×_X V` is compact.

Counting points:

- `exists_card_le_of_etale_affine (g : Y ⟶ Z) [Etale g] (W : Y.affineOpens)`, for schemes
  with `Z` affine: there is `D` such that for every field `L`, every morphism
  `z : Spec L ⟶ Z` and every finite family `y : ι → (Spec L ⟶ Y)` of pairwise distinct
  morphisms with `y i ≫ g = z` and range in `W`, `Fintype.card ι ≤ D`.
- `exists_fibre_card_le (hX : IsQuasiSeparated X) (ha : IsEtale a) [IsAffine V.left]`, for
  `X` over `Spec C`: there is `D` such that for every field `L` with a `C`-algebra
  structure, every `s : ringTest C L ⟶ V` and every finite family
  `v : ι → (ringTest C L ⟶ V)` of pairwise distinct points with
  `h(v i) ≫ a = h(s) ≫ a` for all `i`, `Fintype.card ι ≤ D`.

## Proofs

`selfPullbackLift_mem_of_relative_diag`: let `g : h_{V ⊗ V} → X × X` be the pair of the two
projections followed by `a`. Let `ι : Z ⟶ V ⊗ V` be the represented pullback of the diagonal
along `g`; `ι` has `P` by hypothesis. Its other projection equals both `h(ι ≫ fst) ≫ a` and
`h(ι ≫ snd) ≫ a`, which gives `ψ : Z ⟶ V ×_X V`. Conversely, the pullback square of
`V ×_X V` gives `φ : V ×_X V ⟶ Z` with `φ ≫ ι = lift (selfFst a) (selfSnd a)`
(`Functor.relativelyRepresentable.lift`). The two are mutually inverse: `φ ≫ ψ = 𝟙` by
`hom_ext'`, and `ψ ≫ φ = 𝟙` by the pullback property of `Z`. So the comparison is `ι`
composed with an isomorphism and has `P` (`MorphismProperty.cancel_left_of_respectsIso`).
Unlike the Library lemma `pairPullbackLift_mem_of_relative_diag`, this needs no
monomorphism hypothesis on `P` and works over any base scheme.

`compactSpace_selfPullback`: apply the previous statement with `P = QuasiCompact`, then
`QuasiCompact.compactSpace_of_compactSpace`.

`exists_card_le_of_etale_affine`: let `θ : Γ(Z, ⊤) → Γ(Y, W)` be the ring map with
`Spec θ = W.fromSpec ≫ g ≫ Z.isoSpec.hom`. It is étale, so
`EtaleAlgHomCount.exists_card_algHom_le` gives `D`. Each `y i` lifts through the open
immersion `W.fromSpec`. The lift is `Spec ψ_i` for a ring map `ψ_i : Γ(Y, W) → L`, with
`θ ≫ ψ_i` the ring map of `z`. So the `ψ_i` are pairwise distinct `Γ(Z, ⊤)`-algebra maps,
and there are at most `D` of them.

`exists_fibre_card_le`: `V ⊗ V` is affine, so `V ×_X V` is compact and covered by a finite
set `t` of affine opens. Its second projection `selfSnd a` is étale, being a base change of
`a`. Take `D = ∑_{W ∈ t} D_W` with `D_W` from the previous statement. Given `s` and `v`, the
points `r i = selfLift a (v i) s` of `V ×_X V` are pairwise distinct and lie over `s`. Each
lies in some `W ∈ t`, because `Spec L` has one point. Counting fibrewise over this choice
(`Finset.card_eq_sum_card_fiberwise`) bounds `Fintype.card ι` by `∑_{W ∈ t} D_W`.

All proofs use only the standard axioms.
