/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalSums

/-!
# Transport of the local trace section formula

The algebraic and pullback-pasting step of trace compatibility with localization.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem sum_sandwich {J : Type u} [Fintype J]
    {L M N P Q : AddCommGrpCat.{u + 1}} (a : L ⟶ M) (b : M ⟶ N)
    (c : J → (N ⟶ P)) (d : P ⟶ Q) :
    a ≫ b ≫ (∑ j, c j) ≫ d = ∑ j, a ≫ b ≫ c j ≫ d := by
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
/-- The transported trace section satisfies the local sum formula on every split
object over `W`. This lemma concerns only the trace on `X`; no trace on `X'` is used.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-localization-section-formula)

Proof. Write `rho` for the restriction isomorphism for `g`. Naturality of `rho`
and the trace on `X` identifies the restriction of the displayed section to `T`
with the trace applied to the input restricted to `T`, transported through the
pasting isomorphism for `T`. Construct that isomorphism by the pullback universal
property. Its projections, and the two specified projections of the isomorphism
at `W`, imply compatibility with the pullback maps induced by `h`.

Transport the given splitting of `T ×_X' Y'` along the pasting isomorphism.
Compose each inclusion with its hom and retain the same inverse map from `T`.
Isomorphisms preserve the colimit cofan, open and closed immersions. The first
projection identity preserves both inverse equations, so this is a splitting of
`T ×_X Y`. Apply the local sum predicate for the trace on `X` to this splitting.
Naturality of `rho` along each section identifies its summands, after transport
back by `rho.inv`, with the summands displayed here. Additive homomorphisms
preserve finite sums. The second projection identity ensures that the sections
are morphisms over `X`. This proves the formula, with an empty index type giving
zero on both sides; no existence of a splitting cover or separatedness is needed. -/
theorem finiteEtaleTrace_localization_section_formula
    {X Y X' : Scheme.{u}} (f : Y ⟶ X) (hf : Etale f)
    (g : X' ⟶ X) (hg : Etale g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {S Z : Scheme.{u}} (q : Z ⟶ S) (hq : Etale q) (W : S.Etale) ↦
      (MorphismProperty.Over.map ⊤ hq).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ q).obj W)
    letI := hf
    let f' := pullback.snd f g
    let hf' : Etale f' := inferInstance
    let F' := (upperStar A g).obj F
    ∀ (τ : (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F),
      FiniteEtaleTraceLocalSums f hf F τ →
      ∀ (W : X'.Etale)
        (κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
          B f hf ((MorphismProperty.Over.map ⊤ hg).obj W)),
        κ.hom.left ≫ pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' →
        κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
          pullback.snd W.hom f' ≫ pullback.fst f g →
        ∀ (s : F'.obj.obj (op (B f' hf' W)))
          (T : X'.Etale) (h : T ⟶ W) (J : Type u) [Fintype J]
          (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ pullback T.hom f')
          (t : ∀ j, T.left ⟶ V j)
          (_ : IsColimit (Cofan.mk (pullback T.hom f') i))
          (hinv₁ : ∀ j, t j ≫ i j ≫ pullback.fst T.hom f' = 𝟙 T.left)
          (_ : ∀ j, i j ≫ pullback.fst T.hom f' ≫ t j = 𝟙 (V j))
          (_ : ∀ j, IsOpenImmersion (i j)) (_ : ∀ j, IsClosedImmersion (i j)),
          F'.obj.map h.op
            ((((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app
              (op (B f' hf' W)) ≫ F.obj.map κ.inv.op ≫
              (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
                  ((MorphismProperty.Over.map ⊤ hg).obj W)))) ≫
              τ.hom.app (op ((MorphismProperty.Over.map ⊤ hg).obj W)) ≫
              ((upperStarIsoLocalizationRestriction A g hg).app F).inv.hom.app (op W)) s) =
            ∑ j, F'.obj.map (MorphismProperty.Over.homMk
              (A := T) (B := B f' hf' T) (t j ≫ i j)
              (by
                change (t j ≫ i j) ≫ pullback.snd T.hom f' ≫ f' = T.hom
                rw [← pullback.condition]
                simpa [← Category.assoc] using
                  congrArg (fun k ↦ k ≫ T.hom) (hinv₁ j))).op
                    (F'.obj.map
                      ((MorphismProperty.Over.pullback @Etale ⊤ f' ⋙
                        MorphismProperty.Over.map ⊤ hf').map h).op s) := by
  classical
  dsimp only
  intro τ hτ W κ hk₁ hk₂ s T h J hJ V i t hc hinv₁ hinv₂ hopen hclosed
  let A := AddCommGrpCat.{u + 1}
  let M := MorphismProperty.Over.map ⊤ hg
  let P := MorphismProperty.Over.pullback @Etale ⊤ f
  let D := P ⋙ MorphismProperty.Over.map ⊤ hf
  let f' := pullback.snd f g
  let hf' : Etale f' := inferInstance
  let D' := MorphismProperty.Over.pullback @Etale ⊤ f' ⋙
    MorphismProperty.Over.map ⊤ hf'
  let F' := (upperStar A g).obj F
  let ρ := (upperStarIsoLocalizationRestriction A g hg).app F
  let β := (lowerStar A f).map
    ((upperStarIsoLocalizationRestriction A f hf).app F).inv ≫ τ
  let k : pullback T.hom f' ⟶ pullback (T.hom ≫ g) f :=
    pullback.lift (pullback.fst T.hom f')
      (pullback.snd T.hom f' ≫ pullback.fst f g) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
        simp [f'])
  let l : pullback (T.hom ≫ g) f ⟶ pullback T.hom f' :=
    pullback.lift (pullback.fst (T.hom ≫ g) f)
      (pullback.lift (pullback.snd (T.hom ≫ g) f)
        (pullback.fst (T.hom ≫ g) f ≫ T.hom) (by
          rw [Category.assoc, ← pullback.condition])) (by simp [f'])
  let q : pullback T.hom f' ≅ pullback (T.hom ≫ g) f :=
    { hom := k
      inv := l
      hom_inv_id := by
        apply pullback.hom_ext
        · simp [k, l]
        · apply pullback.hom_ext
          · simp [k, l]
          · simp [k, l, f', ← pullback.condition]
      inv_hom_id := by apply pullback.hom_ext <;> simp [k, l] }
  let κT : M.obj (D'.obj T) ≅ D.obj (M.obj T) :=
    MorphismProperty.Over.isoMk q (by
      change k ≫ (pullback.snd (T.hom ≫ g) f ≫ f) =
        (pullback.snd T.hom f' ≫ f') ≫ g
      dsimp only [k]
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, pullback.condition]
      rfl)
  let a : ∀ j, V j ⟶ pullback (T.hom ≫ g) f := fun j ↦ i j ≫ q.hom
  have ha₁ (j : J) : t j ≫ a j ≫ pullback.fst (T.hom ≫ g) f = 𝟙 T.left := by
    simpa [a, q, k] using hinv₁ j
  have ha₂ (j : J) : a j ≫ pullback.fst (T.hom ≫ g) f ≫ t j = 𝟙 (V j) := by
    simpa [a, q, k] using hinv₂ j
  have hca : IsColimit (Cofan.mk (pullback (T.hom ≫ g) f) a) :=
    IsColimit.ofIsoColimit hc (Cocone.ext q (by intro j; simp [a]))
  have : IsIso q.hom := ⟨⟨q.inv, q.hom_inv_id, q.inv_hom_id⟩⟩
  have hao (j : J) : IsOpenImmersion (a j) := by
    let := hopen j
    dsimp [a]
    infer_instance
  have hac (j : J) : IsClosedImmersion (a j) := by
    let := hclosed j
    dsimp [a]
    infer_instance
  have hs := hτ (M.obj T) J V a t hca ha₁ ha₂ hao hac
  let σ : ∀ j, T ⟶ D'.obj T := fun j ↦ MorphismProperty.Over.homMk (t j ≫ i j)
    (by
      change (t j ≫ i j) ≫ pullback.snd T.hom f' ≫ f' = T.hom
      rw [← pullback.condition]
      simpa [← Category.assoc] using
        congrArg (fun k ↦ k ≫ T.hom) (hinv₁ j))
  have hσ (j : J) : MorphismProperty.Over.homMk
      (A := M.obj T) (B := D.obj (M.obj T)) (t j ≫ a j)
      (by
        change (t j ≫ a j) ≫ pullback.snd (T.hom ≫ g) f ≫ f = T.hom ≫ g
        rw [← pullback.condition]
        simpa [← Category.assoc] using
          congrArg (fun k ↦ k ≫ T.hom ≫ g) (ha₁ j)) = M.map (σ j) ≫ κT.hom := by
    ext
    simp [σ, κT, a, M, Category.assoc]
  change β.hom.app (op (M.obj T)) = _ at hs
  simp only [hσ] at hs
  have hnκ : M.map (D'.map h) ≫ κ.hom = κT.hom ≫ D.map (M.map h) := by
    ext
    change (M.map (D'.map h)).left ≫ κ.hom.left =
      κT.hom.left ≫ (D.map (M.map h)).left
    apply pullback.hom_ext
    · change (M.map (D'.map h)).left ≫ κ.hom.left ≫
        pullback.fst (W.hom ≫ g) f = _
      rw [hk₁]
      change pullback.lift (pullback.fst T.hom f' ≫ h.left)
          (pullback.snd T.hom f') _ ≫ pullback.fst W.hom f' =
        k ≫ pullback.lift (pullback.fst (T.hom ≫ g) f ≫ h.left)
          (pullback.snd (T.hom ≫ g) f) _ ≫ pullback.fst (W.hom ≫ g) f
      simp [k]
    · change (M.map (D'.map h)).left ≫ κ.hom.left ≫
        pullback.snd (W.hom ≫ g) f = _
      rw [hk₂]
      change pullback.lift (pullback.fst T.hom f' ≫ h.left)
          (pullback.snd T.hom f') _ ≫ pullback.snd W.hom f' ≫ pullback.fst f g =
        k ≫ pullback.lift (pullback.fst (T.hom ≫ g) f ≫ h.left)
          (pullback.snd (T.hom ≫ g) f) _ ≫ pullback.snd (W.hom ≫ g) f
      simp [k]
  have hnκi : D.map (M.map h) ≫ κ.inv = κT.inv ≫ M.map (D'.map h) := by
    apply (cancel_mono κ.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hnκ, Iso.inv_hom_id_assoc]
  have hnρinv : ρ.inv.hom.app (op W) ≫ F'.obj.map h.op =
      F.obj.map (M.map h).op ≫ ρ.inv.hom.app (op T) :=
    (ρ.inv.hom.naturality h.op).symm
  have hnβ : β.hom.app (op (M.obj W)) ≫ F.obj.map (M.map h).op =
      F.obj.map (D.map (M.map h)).op ≫ β.hom.app (op (M.obj T)) :=
    (β.hom.naturality (M.map h).op).symm
  have hnρhom : ρ.hom.hom.app (op (D'.obj W)) ≫ F.obj.map (M.map (D'.map h)).op =
      F'.obj.map (D'.map h).op ≫ ρ.hom.hom.app (op (D'.obj T)) :=
    (ρ.hom.hom.naturality (D'.map h).op).symm
  have hnFκ : F.obj.map κ.inv.op ≫ F.obj.map (D.map (M.map h)).op =
      F.obj.map (M.map (D'.map h)).op ≫ F.obj.map κT.inv.op := by
    simpa only [op_comp, Functor.map_comp] using
      congrArg (fun z ↦ F.obj.map z.op) hnκi
  have heach (j : J) :
      ρ.hom.hom.app (op (D'.obj T)) ≫ F.obj.map κT.inv.op ≫
        F.obj.map (M.map (σ j) ≫ κT.hom).op ≫ ρ.inv.hom.app (op T) =
      F'.obj.map (σ j).op := by
    have hcancel : F.obj.map κT.inv.op ≫ F.obj.map κT.hom.op = 𝟙 _ := by
      calc
        _ = F.obj.map (κT.hom ≫ κT.inv).op :=
          (F.obj.map_comp κT.inv.op κT.hom.op).symm
        _ = F.obj.map (𝟙 (M.obj (D'.obj T))).op := by rw [κT.hom_inv_id]
        _ = 𝟙 _ := F.obj.map_id _
    simp only [op_comp, F.obj.map_comp, Category.assoc]
    rw [← Category.assoc (F.obj.map κT.inv.op), hcancel, Category.id_comp]
    have hnσ : ρ.hom.hom.app (op (D'.obj T)) ≫ F.obj.map (M.map (σ j)).op =
        F'.obj.map (σ j).op ≫ ρ.hom.hom.app (op T) :=
      (ρ.hom.hom.naturality (σ j).op).symm
    rw [← Category.assoc (ρ.hom.hom.app _), hnσ, Category.assoc]
    have hρid := congrArg (fun z ↦ z.hom.app (op T)) ρ.hom_inv_id
    change ρ.hom.hom.app (op T) ≫ ρ.inv.hom.app (op T) = 𝟙 _ at hρid
    rw [hρid, Category.comp_id]
  have hsum : ρ.hom.hom.app (op (D'.obj T)) ≫ F.obj.map κT.inv.op ≫
      (∑ j, F.obj.map (M.map (σ j) ≫ κT.hom).op) ≫ ρ.inv.hom.app (op T) =
      ∑ j, F'.obj.map (σ j).op := by
    calc
      _ = ∑ j, ρ.hom.hom.app (op (D'.obj T)) ≫ F.obj.map κT.inv.op ≫
          F.obj.map (M.map (σ j) ≫ κT.hom).op ≫ ρ.inv.hom.app (op T) := by
        exact sum_sandwich _ _ _ _
      _ = _ := Finset.sum_congr rfl (fun j _ ↦ heach j)
  have he :
      (ρ.hom.hom.app (op (D'.obj W)) ≫ F.obj.map κ.inv.op ≫
        β.hom.app (op (M.obj W)) ≫ ρ.inv.hom.app (op W)) ≫ F'.obj.map h.op =
      F'.obj.map (D'.map h).op ≫ ∑ j, F'.obj.map (σ j).op := by
    simp only [Category.assoc]
    rw [hnρinv, ← Category.assoc (β.hom.app _), hnβ]
    simp only [Category.assoc]
    rw [← Category.assoc (F.obj.map κ.inv.op), hnFκ]
    simp only [Category.assoc]
    rw [← Category.assoc (ρ.hom.hom.app _), hnρhom]
    simp only [Category.assoc]
    rw [hs]
    exact congrArg (fun z ↦ F'.obj.map (D'.map h).op ≫ z) hsum
  have heval {M N : AddCommGrpCat.{u + 1}} (v : J → (M ⟶ N)) (x : M) :
      (∑ j, v j) x = ∑ j, v j x := by
    change ((∑ j, v j).hom) x = _
    have hv := map_sum (AddCommGrpCat.homAddEquiv (M := M) (N := N)) v Finset.univ
    change (∑ j, v j).hom = ∑ j, (v j).hom at hv
    rw [hv]
    exact AddMonoidHom.finsetSum_apply _ _ _
  change F'.obj.map h.op
    ((ρ.hom.hom.app (op (D'.obj W)) ≫ F.obj.map κ.inv.op ≫
      β.hom.app (op (M.obj W)) ≫ ρ.inv.hom.app (op W)) s) =
    ∑ j, F'.obj.map (σ j).op (F'.obj.map (D'.map h).op s)
  have hev := congrArg (fun z ↦ z s) he
  change F'.obj.map h.op
    ((ρ.hom.hom.app (op (D'.obj W)) ≫ F.obj.map κ.inv.op ≫
      β.hom.app (op (M.obj W)) ≫ ρ.inv.hom.app (op W)) s) = (∑ j, F'.obj.map (σ j).op)
    (F'.obj.map (D'.map h).op s) at hev
  rw [heval] at hev
  exact hev

end AlgebraicGeometry.Etale
