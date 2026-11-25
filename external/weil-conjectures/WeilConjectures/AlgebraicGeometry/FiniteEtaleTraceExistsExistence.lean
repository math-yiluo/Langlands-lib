/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDescent
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalization
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTracePullbackSum

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Existence of a finite étale trace family satisfying naturality, étale localization,
and the sum formula for every finite clopen splitting, including the empty splitting.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE, and the descent
argument in SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-exists-existence)

Proof. Put `W_Y = W ×_X Y` and use the restriction isomorphism to identify
`f_* f⁻¹ F` with the sheaf `P_F(W) = F(W_Y)`. For a splitting `D` of `T_Y` with
sections `σ_j`, define the homomorphism `Σ_D(t) = ∑ j, F(σ_j)(t)`. These sums commute
with restriction: pulling `D` back along `h : T' → T` pulls its sections back, and the
pullback universal property gives `h_Y ∘ σ'_j = σ_j ∘ h`.

The sums are independent of the splitting. For splittings indexed by finite sets `J`
and `K`, intersect their clopen pieces. The images `T_jk` of the intersections in `T`
are clopen, partition `T` for each fixed `j` and for each fixed `k`, and on `T_jk`
the two sections agree, since both invert the same isomorphism. At each point they
therefore determine a bijection `π : J ≃ K`. The opens `⋂ j, T_j(π j)` cover `T`;
on each such open reindexing the finite sum proves equality. Sheaf separatedness
proves equality on `T`. If the cardinalities differ, `T` is empty and its group of
sections is zero; thus the empty splitting causes no exception.

Finite étale local splitting (Stacks 04HN) and covering base change provide every `W`
with a covering `h_a : W_a → W` on which `W_a ×_X Y` splits. For `t ∈ F(W_Y)` form
`u_a = Σ_Da(F((h_a)_Y)(t))`. On overlaps restriction compatibility and independence
of splittings make the `u_a` agree. Glue them by the sheaf condition to `u ∈ F(W)`.
This `u` is uniquely characterized by
`F(h)(u) = Σ_D(F(h_Y)(t))` for every `h : T → W` and every splitting `D` of `T_Y`:
to check the identity pull the chosen covering back to `T`, compare both local sums,
and apply separatedness. Uniqueness follows on the original splitting covering.

Define `τ_W(t) = u`. The characterization proves additivity, compatibility with all
restrictions, and naturality in `F`, since each local sum has these properties. Hence
`τ : P_F → F` is a sheaf morphism. Transport it across the restriction isomorphism to
obtain `tr`. For a splitting of `Y` over `X`, pull its pieces and sections back to `W`
and apply the characterization with `h = id_W`; this gives the required sum formula.

For étale `g : X' → X`, the canonical pullback-pasting isomorphism `κ_W` carries
splittings for the pullback of `f` to splittings for `f` at the corresponding object
of `X.Etale`. The two induced restrictions of sections commute with `κ`, by equality
of their two pullback projections. Thus the characterization identifies the trace
for `F|_X'` with the transported trace for `F`. Naturality in the sheaf transports
this identity along `g⁻¹ F ≅ F|_X'`, giving precisely the displayed localization
identity. Choosing this construction for all `f` and `F` gives the asserted family. -/
theorem finiteEtaleTrace_exists :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Etale f) (W : X.Etale) ↦
      (MorphismProperty.Over.map ⊤ hf).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
    let T := ∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsFinite f) (_ : Etale f)
      (F : Sheaf X.smallEtaleTopology A),
      (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F
    ∃ tr : T,
      let bar := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (W : X.Etale) ↦
        (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
            (tr X Y f hfin hf F).hom.app (op W)
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F G : Sheaf X.smallEtaleTopology A) (φ : F ⟶ G),
        tr X Y f hfin hf F ≫ φ =
          (lowerStar A f).map ((upperStar A f).map φ) ≫ tr X Y f hfin hf G) ∧
      (∀ (X Y X' : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (g : X' ⟶ X) (hg : Etale g) (F : Sheaf X.smallEtaleTopology A),
        letI := hfin
        letI := hf
        let f' := pullback.snd f g
        let hf' : Etale f' := inferInstance
        let F' := (upperStar A g).obj F
        ∀ (W : X'.Etale)
          (κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
            B f hf ((MorphismProperty.Over.map ⊤ hg).obj W)),
          κ.hom.left ≫ pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' →
          κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
            pullback.snd W.hom f' ≫ pullback.fst f g →
          bar f' inferInstance hf' F' W ≫
              ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app (op W) =
            ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app
                (op (B f' hf' W)) ≫ F.obj.map κ.inv.op ≫
              bar f hfin hf F ((MorphismProperty.Over.map ⊤ hg).obj W)) ∧
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (J : Type u) [Fintype J]
          (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y) (t : ∀ j, X ⟶ V j)
          (_ : IsColimit (Cofan.mk Y i))
          (hinv₁ : ∀ j, t j ≫ i j ≫ f = 𝟙 X)
          (_ : ∀ j, i j ≫ f ≫ t j = 𝟙 (V j))
          (_ : ∀ j, IsOpenImmersion (i j))
          (_ : ∀ j, IsClosedImmersion (i j))
          (W : X.Etale),
          bar f hfin hf F W = ∑ j, F.obj.map (MorphismProperty.Over.homMk
            (A := W) (B := B f hf W)
            (pullback.lift (𝟙 W.left) (W.hom ≫ t j ≫ i j)
              (by simp [Category.assoc, hinv₁]))
            (by simp [B, Category.assoc, hinv₁])).op) := by
  classical
  dsimp only
  choose τ hτ using fun (X Y : Scheme.{u}) (f : Y ⟶ X)
    (hfin : IsFinite f) (hf : Etale f) ↦ finiteEtaleTrace_descent f hfin hf
  refine ⟨fun X Y f hfin hf F ↦ (τ X Y f hfin hf).app F, ?_, ?_, ?_⟩
  · intro X Y f hfin hf F G φ
    exact ((τ X Y f hfin hf).naturality φ).symm
  · intro X Y X' f hfin hf g hg F
    let := hfin
    let := hf
    dsimp only
    intro W κ hfst hsnd
    simpa only [Category.assoc] using
      finiteEtaleTrace_localization_of_localSums f hfin hf g hg F
        ((τ X Y f hfin hf).app F)
        ((τ X' (pullback f g) (pullback.snd f g) inferInstance inferInstance).app
          ((upperStar AddCommGrpCat.{u + 1} g).obj F))
        (hτ X Y f hfin hf F)
        (hτ X' (pullback f g) (pullback.snd f g) inferInstance inferInstance
          ((upperStar AddCommGrpCat.{u + 1} g).obj F)) W κ hfst hsnd
  · intro X Y f hfin hf F J hJ V i t hc hinv₁ hinv₂ hopen hclosed W
    exact finiteEtaleTrace_sum_of_localSums f hf F ((τ X Y f hfin hf).app F)
      (hτ X Y f hfin hf F) J V i t hc hinv₁ hinv₂ hopen hclosed W

end AlgebraicGeometry.Etale
