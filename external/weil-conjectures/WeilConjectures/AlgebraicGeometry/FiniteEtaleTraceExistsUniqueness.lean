/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Mathlib.AlgebraicGeometry.Sites.Etale

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Uniqueness of a finite étale trace family satisfying the three displayed properties.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE; SGA 4,
Exposé IX, 5.1 (uniqueness from localization and the split formula).
(blueprint: lem-weil-pbc-finite-etale-trace-exists-uniqueness)

Proof. Fix two such families, a finite étale `f`, and a sheaf `F`. Transport their
components through the restriction isomorphism to morphisms `P_F → F`, where
`P_F(W) = F(W ×_X Y)`. For any object `W` choose a jointly surjective étale covering
`h_a : W_a → W` such that `W_a ×_X Y → W_a` splits into finitely many clopen pieces.
Such a covering follows from Stacks 04HN and covering base change.

Apply each family's localization identity to `g_a : W_a → X` and the terminal
object of `W_a.Etale`. Pullback pasting identifies its double fibre product with
`W_a ×_X Y`. Apply the split formula to the pullback of `f` over `W_a`: its sections
are exactly the transported sections of the chosen splitting. Naturality of the
restriction isomorphism turns both formulas into the same sum of restrictions
`F(W_a ×_X Y) → F(W_a)`. Cancel the restriction and pasting isomorphisms, which are
invertible; the two transported trace components at `W_a` are equal.

For `t ∈ P_F(W)`, naturality of each sheaf morphism in `W` now says that the two
images of `t` have identical restrictions along every `h_a`. Separatedness of `F`
gives equality in `F(W)`. This proves component equality for all `W` and `t`, hence
morphism equality. Transport back through the restriction isomorphism and apply
function extensionality in `X`, `Y`, `f`, its proofs, and `F` to obtain family equality.
The argument does not require the naturality-in-`F` hypotheses. The empty splitting
has zero local sum, and the empty base has zero sections by the empty-cover sheaf
condition, so these cases are included. -/
theorem finiteEtaleTrace_unique :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Etale f) (W : X.Etale) ↦
      (MorphismProperty.Over.map ⊤ hf).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
    let T := ∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsFinite f) (_ : Etale f)
      (F : Sheaf X.smallEtaleTopology A),
      (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F
    ∀ tr₁ tr₂ : T, (
      let bar := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (W : X.Etale) ↦
        (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
            (tr₁ X Y f hfin hf F).hom.app (op W)
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F G : Sheaf X.smallEtaleTopology A) (φ : F ⟶ G),
        tr₁ X Y f hfin hf F ≫ φ =
          (lowerStar A f).map ((upperStar A f).map φ) ≫ tr₁ X Y f hfin hf G) ∧
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
            (by simp [B, Category.assoc, hinv₁])).op)) → (
      let bar := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (W : X.Etale) ↦
        (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
            (tr₂ X Y f hfin hf F).hom.app (op W)
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F G : Sheaf X.smallEtaleTopology A) (φ : F ⟶ G),
        tr₂ X Y f hfin hf F ≫ φ =
          (lowerStar A f).map ((upperStar A f).map φ) ≫ tr₂ X Y f hfin hf G) ∧
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
            (by simp [B, Category.assoc, hinv₁])).op)) → tr₁ = tr₂ := by
  classical
  dsimp only
  intro tr₁ tr₂ h₁ h₂
  funext X Y f hfin hf F
  let := hfin
  let := hf
  -- The split formula determines components after a splitting localization.
  have hlocal (U : Scheme.{u}) (g : U ⟶ X) (hg : Etale g)
      (J : Type u) [Fintype J] (V : J → Scheme.{u})
      (i : ∀ j, V j ⟶ pullback f g)
      (hc : IsColimit (Cofan.mk (pullback f g) i))
      (hi : ∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j))
      (e : ∀ j, V j ≅ U) (he : ∀ j, (e j).hom = i j ≫ pullback.snd f g)
      (W : U.Etale) :
      (tr₁ X Y f hfin hf F).hom.app
          (op ((MorphismProperty.Over.map ⊤ hg).obj W)) =
        (tr₂ X Y f hfin hf F).hom.app
          (op ((MorphismProperty.Over.map ⊤ hg).obj W)) := by
    let := hg
    let f' := pullback.snd f g
    let hf' : Etale f' := inferInstance
    let F' := (upperStar AddCommGrpCat.{u + 1} g).obj F
    let t : ∀ j, U ⟶ V j := fun j ↦ (e j).inv
    have ht₁ (j : J) : t j ≫ i j ≫ f' = 𝟙 U := by
      simp [t, f', ← he j]
    have ht₂ (j : J) : i j ≫ f' ≫ t j = 𝟙 (V j) := by
      dsimp [t, f']
      rw [← Category.assoc, ← he j, Iso.hom_inv_id]
    have hs := (h₁.2.2 _ _ f' inferInstance hf' F' J V i t hc ht₁ ht₂
      (fun j ↦ (hi j).1) (fun j ↦ (hi j).2) W).trans
      (h₂.2.2 _ _ f' inferInstance hf' F' J V i t hc ht₁ ht₂
        (fun j ↦ (hi j).1) (fun j ↦ (hi j).2) W).symm
    let B := fun {S T : Scheme.{u}} (a : T ⟶ S) (ha : Etale a) (Z : S.Etale) ↦
      (MorphismProperty.Over.map ⊤ ha).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ a).obj Z)
    -- Construct the comparison of the iterated and single pullbacks over X.
    let k : pullback W.hom f' ⟶ pullback (W.hom ≫ g) f :=
      pullback.lift (pullback.fst W.hom f')
        (pullback.snd W.hom f' ≫ pullback.fst f g) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc,
            pullback.condition]
          simp [f'])
    let l : pullback (W.hom ≫ g) f ⟶ pullback W.hom f' :=
      pullback.lift (pullback.fst (W.hom ≫ g) f)
        (pullback.lift (pullback.snd (W.hom ≫ g) f)
          (pullback.fst (W.hom ≫ g) f ≫ W.hom) (by
            rw [Category.assoc, ← pullback.condition])) (by simp [f'])
    let q : pullback W.hom f' ≅ pullback (W.hom ≫ g) f :=
      { hom := k
        inv := l
        hom_inv_id := by
          apply pullback.hom_ext
          · simp [k, l]
          · apply pullback.hom_ext
            · simp [k, l]
            · simp [k, l, f', ← pullback.condition]
        inv_hom_id := by
          apply pullback.hom_ext <;> simp [k, l] }
    let κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
        B f hf ((MorphismProperty.Over.map ⊤ hg).obj W) :=
      MorphismProperty.Over.isoMk q (by
        change k ≫ (pullback.snd (W.hom ≫ g) f ≫ f) =
          (pullback.snd W.hom f' ≫ f') ≫ g
        dsimp only [k]
        rw [← Category.assoc, pullback.lift_snd, Category.assoc, pullback.condition]
        rfl)
    have hk₁ : κ.hom.left ≫ pullback.fst (W.hom ≫ g) f =
        pullback.fst W.hom f' := by simp [κ, q, k]
    have hk₂ : κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
        pullback.snd W.hom f' ≫ pullback.fst f g := by simp [κ, q, k]
    have hl₁ := h₁.2.1 X Y U f hfin hf g hg F W κ hk₁ hk₂
    have hl₂ := h₂.2.1 X Y U f hfin hf g hg F W κ hk₁ hk₂
    -- Localization gives equality after precomposition with three isomorphisms.
    have hh := hl₁.symm.trans ((congrArg (fun a ↦ a ≫
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g hg).app F).hom.hom.app
        (op W)) hs).trans hl₂)
    exact (cancel_epi _).mp ((cancel_epi _).mp ((cancel_epi _).mp hh))
  -- Pull back the splitting neighborhoods to cover each object of the small site.
  choose U g u hg hu J V i hJ hc hi hp using finite_etale_etale_local_split f
  let (x : X) : Etale (g x) := hg x
  let (x : X) : Finite (J x) := hJ x
  let (x : X) : Fintype (J x) := Fintype.ofFinite (J x)
  choose e he using hp
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  induction W using Opposite.rec with
  | _ W =>
    let Z (x : X) : (U x).Etale :=
      (MorphismProperty.Over.pullback @Etale ⊤ (g x)).obj W
    let Z' (x : X) : X.Etale := (MorphismProperty.Over.map ⊤ (hg x)).obj (Z x)
    let a (x : X) : Z' x ⟶ W :=
      MorphismProperty.Over.homMk (pullback.fst W.hom (g x))
        (by exact pullback.condition)
    have hcov : Sieve.ofArrows Z' a ∈ X.smallEtaleTopology W := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
      apply Set.eq_univ_of_forall
      intro w
      obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
        w (u (W.hom w)) (hu (W.hom w)).symm
      exact Set.mem_iUnion.mpr ⟨W.hom w, z, hz⟩
    -- Separatedness and naturality turn local component equality into global equality.
    apply F.property.hom_ext_ofArrows a hcov
    intro x
    rw [← (tr₁ X Y f hfin hf F).hom.naturality,
      ← (tr₂ X Y f hfin hf F).hom.naturality]
    rw [hlocal (U x) (g x) (hg x) (J x) (V x) (i x) (hc x).some (hi x)
      (e x) (he x) (Z x)]

end AlgebraicGeometry.Etale
