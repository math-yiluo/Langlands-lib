/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleSectionContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.AlgebraicGeometry.Sites.TorsorPullback
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting

/-!
# Vanishing of geometric stalks of higher direct images

Let `h : X ⟶ S` be a morphism of schemes, `F` an abelian étale sheaf on `X` and
`s : Spec Ω ⟶ S` a geometric point. For a pointed étale neighbourhood `V` of `s` write
`X_V = X ×_S V`. If every class in `Hᵠ(X_V, F|)` dies on `X_{V'}` for some smaller pointed
étale neighbourhood `V' ⟶ V`, then the geometric stalk of `Rᵠh_* F` at `s` vanishes
(`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_forall_exists`).

The proof is by dimension shifting: embedding `F` into an injective sheaf `I` with quotient `Q`,
`Rᵠh_* F ≅ Rᵠ⁻¹h_* Q` for `q ≥ 2` and the hypothesis passes from `F` in degree `q` to `Q` in degree
`q - 1`, since the restrictions of `I` to the `X_V` are injective. In degree one, a germ of a
section `σ` of `h_* Q` at `s` is a section of `Q` over some `X_V`; its coboundary dies on a
smaller `X_{V'}`, so that `σ` lifts to `I` there, and the germ of `σ` in `R¹h_* F` vanishes.
Since a sheaf on `Spec Ω` is zero as soon as its stalk at the identity point vanishes, and
that stalk of `s^* G` is the geometric stalk `G_s`, everything is proved on geometric stalks
(`AlgebraicGeometry.Etale.isZero_sheafFiber_rightDerived_lowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

section Sections

variable {X S : Scheme.{u}} (h : X ⟶ S)

instance etale_pullbackFst (V : S.Etale) : AlgebraicGeometry.Etale (pullback.fst h V.hom) :=
  MorphismProperty.pullback_fst _ _ V.prop

/-- The morphism `X ×_S V' ⟶ X ×_S V` induced by a morphism `b : V' ⟶ V` of étale
`S`-schemes. -/
noncomputable abbrev pullbackEtaleMap {V V' : S.Etale} (b : V' ⟶ V) :
    pullback h V'.hom ⟶ pullback h V.hom :=
  pullback.map h V'.hom h V.hom (𝟙 X) b.left (𝟙 S) (by simp)
    (by simp [MorphismProperty.Over.w b])

lemma pullbackEtaleMap_fst {V V' : S.Etale} (b : V' ⟶ V) :
    pullback.fst h V'.hom = pullbackEtaleMap h b ≫ pullback.fst h V.hom := by
  simp

instance etale_pullbackEtaleMap {V V' : S.Etale} (b : V' ⟶ V) :
    AlgebraicGeometry.Etale (pullbackEtaleMap h b) := by
  have hb : AlgebraicGeometry.Etale b.left := by
    have : AlgebraicGeometry.Etale (b.left ≫ V.hom) := by
      rw [MorphismProperty.Over.w b]; exact V'.prop
    exact AlgebraicGeometry.Etale.of_comp b.left V.hom
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Etale)
    (MorphismProperty.id_mem _ X) hb (by simp) (by simp [MorphismProperty.Over.w b])

/-- The terminal étale `Y`-scheme `𝟙 : Y ⟶ Y`. -/
noncomputable abbrev topEtale (Y : Scheme.{u}) : Y.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem @AlgebraicGeometry.Etale Y)

/-- Pullback of sections is natural in the sheaf. -/
lemma pullSection_naturality {R T : Scheme.{u}} (t : T ⟶ R)
    {G G' : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}} (ψ : G ⟶ G')
    {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t)
    (g : G.obj.obj (op U)) :
    (((t)^*[AddCommGrpCat.{u + 1}]).map ψ).hom.app (op V) (pullSection t G φ hφ g) =
      pullSection t G' φ hφ (ψ.hom.app (op U) g) := by
  have h₁ := NatTrans.naturality_apply (((t)^*[AddCommGrpCat.{u + 1}]).map ψ).hom
    (homToPullback t φ hφ).op
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g)
  have h₂ := congrArg (fun α ↦ α.hom.app (op U) g)
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.naturality ψ)
  rw [pullSection, h₁, pullSection]
  congr 1
  exact h₂.symm

variable (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- A section of `G` over `V ×_S X`, that is a section of `h_* G` over the étale `S`-scheme
`V`, viewed as a global section of the pullback of `G` to `X ×_S V`. -/
noncomputable def pullbackSection (V : S.Etale) :
    G.obj.obj (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj V)) →+
      ((pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (topEtale _)) where
  toFun := pullSection (pullback.fst h V.hom) G (V := topEtale _)
    (U := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj V)
    (pullbackSymmetry h V.hom).hom
    ((pullbackSymmetry_hom_comp_snd _ _).trans (Category.id_comp _).symm)
  map_zero' := pullSection_zero (pullback.fst h V.hom) G _ _
  map_add' := pullSection_add (pullback.fst h V.hom) G _ _

lemma bijective_pullbackSection (V : S.Etale) : Function.Bijective (pullbackSection h G V) :=
  bijective_pullSection_of_etale (pullback.fst h V.hom) inferInstance G _ _

lemma pullbackSection_naturality {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ G') (V : S.Etale)
    (σ : G.obj.obj (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj V))) :
    (((pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}]).map ψ).hom.app _
        (pullbackSection h G V σ) =
      pullbackSection h G' V (ψ.hom.app _ σ) :=
  pullSection_naturality _ ψ _ _ σ

lemma pullbackEtaleMap_comp_id {V V' : S.Etale} (b : V' ⟶ V) :
    pullbackEtaleMap h b ≫ (topEtale (pullback h V.hom)).hom =
      (topEtale (pullback h V'.hom)).hom ≫ pullbackEtaleMap h b :=
  (Category.comp_id _).trans (Category.id_comp _).symm

lemma restrictAlong_pullbackSection {V V' : S.Etale} (b : V' ⟶ V)
    (σ : G.obj.obj (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj V))) :
    restrictAlong (pullback.fst h V.hom) G (pullbackEtaleMap h b) (pullback.fst h V'.hom)
        (pullbackEtaleMap_fst h b) (V := topEtale _) (V' := topEtale _) (pullbackEtaleMap h b)
        (pullbackEtaleMap_comp_id h b) (pullbackSection h G V σ) =
      pullbackSection h G V'
        (G.obj.map ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).map b).op σ) := by
  simp only [pullbackSection, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [restrictAlong_pullSection, ← pullSection_comp]
  apply pullSection_congr
  apply pullback.hom_ext <;> simp

lemma equiv₀_map_cohomologyMap_pullbackEtaleMap {V V' : S.Etale} (b : V' ⟶ V)
    (c : Sheaf.H ((pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}].obj G) 0) :
    Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _)
        (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} (pullbackEtaleMap h b)
          (pullback.fst h V.hom) (pullback.fst h V'.hom) (pullbackEtaleMap_fst h b)).inv.app G) 0
          (cohomologyMap (pullbackEtaleMap h b) _ 0 c)) =
      restrictAlong (pullback.fst h V.hom) G (pullbackEtaleMap h b) (pullback.fst h V'.hom)
        (pullbackEtaleMap_fst h b) (V := topEtale _) (V' := topEtale _) (pullbackEtaleMap h b)
        (pullbackEtaleMap_comp_id h b) (Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _) c) := by
  have e₁ := Sheaf.H.equiv₀_naturality (hT := Scheme.isTerminalEtale (pullback h V'.hom))
    ((upperStarComp AddCommGrpCat.{u + 1} (pullbackEtaleMap h b)
      (pullback.fst h V.hom) (pullback.fst h V'.hom) (pullbackEtaleMap_fst h b)).inv.app G)
    (cohomologyMap (pullbackEtaleMap h b) _ 0 c)
  have e₂ := equiv₀_cohomologyMap (pullbackEtaleMap h b) _ c
    (Scheme.isTerminalEtale _) (Scheme.isTerminalEtale _)
    (homToPullback (pullbackEtaleMap h b) (pullbackEtaleMap h b) (pullbackEtaleMap_comp_id h b))
  refine e₁.symm.trans ?_
  erw [e₂]
  simp only [restrictAlong, transition]
  exact NatTrans.naturality_apply (((upperStarComp AddCommGrpCat.{u + 1} (pullbackEtaleMap h b)
    (pullback.fst h V.hom) (pullback.fst h V'.hom) (pullbackEtaleMap_fst h b)).inv.app G).hom) _ _

end Sections

section Stalk

variable {X S : Scheme.{u}} (h : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The hypothesis of `isZero_upperStar_rightDerived_lowerStar_of_forall_exists` for a geometric
point `t` of `S`, an abelian sheaf `F` on `X` and a degree `q`: every class of
`Hᵠ(X ×_S V, F|)` vanishes on `X ×_S V'` for some morphism `V' ⟶ V` of pointed étale
neighbourhoods of `t`. -/
def ClassesDieLocally (t : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) : Prop :=
  ∀ (x : PointedEtaleNeighborhood t)
    (c : Sheaf.H ((pullback.fst h x.1.hom)^*[AddCommGrpCat.{u + 1}].obj F) q),
    ∃ (y : PointedEtaleNeighborhood t) (f : y ⟶ x),
      cohomologyMap (pullbackEtaleMap h f.1) _ q c = 0

variable {h}

/-- **Dimension shifting for `ClassesDieLocally`.** For a short exact sequence `0 → F → I → Q → 0`
with `I` injective, if classes of `F` die locally in degree `q + 2`, then classes of `Q` die
locally in degree `q + 1`: the restrictions of `I` are injective, hence acyclic. -/
lemma ClassesDieLocally.cokernel (t : Spec (.of Ω) ⟶ S)
    {T : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hT : T.ShortExact)
    [Injective T.X₂] {q : ℕ} (H : ClassesDieLocally h t T.X₁ (q + 2)) :
    ClassesDieLocally h t T.X₃ (q + 1) := by
  intro x c
  have hTx := hT.map_of_exact (pullback.fst h x.1.hom)^*[AddCommGrpCat.{u + 1}]
  obtain ⟨y, f, hf⟩ := H x (Sheaf.H.δSucc hTx (q + 1) c)
  refine ⟨y, f, ?_⟩
  replace hf := (cohomologyMap_δSucc (pullbackEtaleMap h f.1) hTx (q + 1) c).symm.trans hf
  obtain ⟨z, hz⟩ := (Sheaf.H.exact_map_δSucc (hTx.map_of_exact _) (q + 1) _).1 hf
  have : Injective ((pullback.fst h x.1.hom)^*[AddCommGrpCat.{u + 1}].obj T.X₂) :=
    injective_upperStar_obj_of_etale_addCommGrp _ _
  have : Injective ((pullbackEtaleMap h f.1)^*[AddCommGrpCat.{u + 1}].obj
      ((pullback.fst h x.1.hom)^*[AddCommGrpCat.{u + 1}].obj T.X₂)) :=
    injective_upperStar_obj_of_etale_addCommGrp _ _
  have hz0 : z = 0 := Subsingleton.elim (α := Sheaf.H
      ((pullbackEtaleMap h f.1)^*[AddCommGrpCat.{u + 1}].obj
      ((pullback.fst h x.1.hom)^*[AddCommGrpCat.{u + 1}].obj T.X₂)) (q + 1)) _ _
  rw [hz0, map_zero] at hz
  exact hz.symm

/-- **Degree one.** For a short exact sequence `0 → F → I → Q → 0` such that classes of `F` die
locally in degree one, the map of geometric stalks `(h_* I)_t → (h_* Q)_t` is surjective: a
germ of a section of `h_* Q` is a section `σ` of `Q` over some `X ×_S V`, whose coboundary
dies on some `X ×_S V'`, so that the restriction of `σ` lifts to `I` there. -/
lemma surjective_sheafFiber_map_lowerStar (t : Spec (.of Ω) ⟶ S)
    {T : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hT : T.ShortExact)
    (H : ClassesDieLocally h t T.X₁ 1) :
    Function.Surjective
      ((pointSmallEtale t).sheafFiber.map ((h)_*[AddCommGrpCat.{u + 1}].map T.g)) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro p
  obtain ⟨V, v, σ, rfl⟩ := (pointSmallEtale t).toPresheafFiber_jointly_surjective p
  have hTx := hT.map_of_exact (pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}]
  obtain ⟨y, f, hf⟩ := H ⟨v⟩ (Sheaf.H.δSucc hTx 0
    ((Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _)).symm (pullbackSection h T.X₃ V σ)))
  replace hf := (cohomologyMap_δSucc (pullbackEtaleMap h f.1) hTx 0 _).symm.trans hf
  obtain ⟨z, hz⟩ := (Sheaf.H.exact_map_δSucc (hTx.map_of_exact _) 0 _).1 hf
  let θ := upperStarComp AddCommGrpCat.{u + 1} (pullbackEtaleMap h f.1) (pullback.fst h V.hom)
    (pullback.fst h y.1.hom) (pullbackEtaleMap_fst h f.1)
  obtain ⟨τ, hτ⟩ := (bijective_pullbackSection h T.X₂ y.1).2
    (Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _) (Sheaf.H.map (θ.inv.app T.X₂) 0 z))
  have hz' : Sheaf.H.map ((pullbackEtaleMap h f.1)^*[AddCommGrpCat.{u + 1}].map
      ((pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}].map T.g)) 0 z =
      cohomologyMap (pullbackEtaleMap h f.1)
        ((pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}].obj T.X₃) 0
        ((Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _)).symm (pullbackSection h T.X₃ V σ)) := hz
  have hθ : θ.inv.app T.X₂ ≫ (pullback.fst h y.1.hom)^*[AddCommGrpCat.{u + 1}].map T.g =
      (pullbackEtaleMap h f.1)^*[AddCommGrpCat.{u + 1}].map
        ((pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}].map T.g) ≫ θ.inv.app T.X₃ :=
    (θ.inv.naturality T.g).symm
  have e := equiv₀_map_cohomologyMap_pullbackEtaleMap h T.X₃ f.1
    ((Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _)).symm (pullbackSection h T.X₃ V σ))
  have e₃ := (Sheaf.H.map_comp_apply ((pullbackEtaleMap h f.1)^*[AddCommGrpCat.{u + 1}].map
      ((pullback.fst h V.hom)^*[AddCommGrpCat.{u + 1}].map T.g)) (θ.inv.app T.X₃) z).symm.trans
    ((congrArg (fun φ ↦ Sheaf.H.map φ 0 z) hθ.symm).trans
      (Sheaf.H.map_comp_apply (θ.inv.app T.X₂)
        ((pullback.fst h y.1.hom)^*[AddCommGrpCat.{u + 1}].map T.g) z))
  have e₄ : pullbackSection h T.X₃ y.1 (T.g.hom.app _ τ) =
      pullbackSection h T.X₃ y.1
        (T.X₃.obj.map ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).map f.1).op
          σ) := by
    refine (pullbackSection_naturality h T.g y.1 τ).symm.trans ?_
    rw [hτ]
    refine (Sheaf.H.equiv₀_naturality _ _ _).trans ?_
    refine (congrArg (fun w ↦ Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _) w) e₃.symm).trans ?_
    refine (congrArg (fun w ↦ Sheaf.H.equiv₀ _ (Scheme.isTerminalEtale _)
      (Sheaf.H.map (θ.inv.app T.X₃) 0 w)) hz').trans ?_
    refine e.trans ?_
    rw [AddEquiv.apply_symm_apply, restrictAlong_pullbackSection]
  have key : ((h)_*[AddCommGrpCat.{u + 1}].map T.g).hom.app (op y.1) τ =
      ((h)_*[AddCommGrpCat.{u + 1}].obj T.X₃).obj.map f.1.op σ :=
    (bijective_pullbackSection h T.X₃ y.1).1 e₄
  refine ⟨(pointSmallEtale t).toPresheafFiber y.1 y.2
    ((h)_*[AddCommGrpCat.{u + 1}].obj T.X₂).obj τ, ?_⟩
  have e₁ := (pointSmallEtale t).toPresheafFiber_naturality_apply
    ((h)_*[AddCommGrpCat.{u + 1}].map T.g).hom y.1 y.2 τ
  have e₂ := (pointSmallEtale t).toPresheafFiber_w_apply f.1 y.2
    ((h)_*[AddCommGrpCat.{u + 1}].obj T.X₃).obj σ
  rw [f.2] at e₂
  exact e₁.trans ((congrArg _ key).trans e₂)

/-- The stalk version of the main statement, by induction on the degree. -/
lemma isZero_sheafFiber_rightDerived_lowerStar (t : Spec (.of Ω) ⟶ S) (q : ℕ) :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), ClassesDieLocally h t F (q + 1) →
      IsZero ((pointSmallEtale t).sheafFiber.obj
        ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived (q + 1)).obj F)) := by
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
  let Φ := (pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  induction q with
  | zero =>
    intro F H
    let T := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hT : T.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hδ : Epi (hT.rightDerivedδ ((h)_*[AddCommGrpCat.{u + 1}]) 0) :=
      (hT.rightDerivedδ_exact₃ ((h)_*[AddCommGrpCat.{u + 1}]) 0).epi_f
        ((((h)_*[AddCommGrpCat.{u + 1}]).isZero_rightDerived_obj_injective_succ 0 _).eq_of_tgt _ _)
    have hg : Epi (Φ.map ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived 0).map T.g)) := by
      have e := ((h)_*[AddCommGrpCat.{u + 1}]).rightDerivedZeroIsoSelf.hom.naturality T.g
      have e' : (((h)_*[AddCommGrpCat.{u + 1}]).rightDerived 0).map T.g =
          ((h)_*[AddCommGrpCat.{u + 1}]).rightDerivedZeroIsoSelf.hom.app T.X₂ ≫
            ((h)_*[AddCommGrpCat.{u + 1}]).map T.g ≫
              ((h)_*[AddCommGrpCat.{u + 1}]).rightDerivedZeroIsoSelf.inv.app T.X₃ := by
        rw [← reassoc_of% e, Iso.hom_inv_id_app, Category.comp_id]
      have : Epi (Φ.map (((h)_*[AddCommGrpCat.{u + 1}]).map T.g)) :=
        (AddCommGrpCat.epi_iff_surjective _).2 (surjective_sheafFiber_map_lowerStar t hT H)
      rw [e', Φ.map_comp, Φ.map_comp]
      exact epi_comp' inferInstance (epi_comp' this inferInstance)
    have h0 : Φ.map (hT.rightDerivedδ ((h)_*[AddCommGrpCat.{u + 1}]) 0) = 0 := by
      rw [← cancel_epi (Φ.map ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived 0).map T.g)),
        ← Φ.map_comp, hT.comp_rightDerivedδ ((h)_*[AddCommGrpCat.{u + 1}]) 0, Φ.map_zero, comp_zero]
    have : Epi (Φ.map (hT.rightDerivedδ ((h)_*[AddCommGrpCat.{u + 1}]) 0)) := inferInstance
    rw [h0] at this
    exact IsZero.of_epi_zero
      (Φ.obj ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived 0).obj T.X₃)) _
  | succ q ih =>
    intro F H
    let T := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hT : T.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have : Injective T.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hδ : Epi (hT.rightDerivedδ ((h)_*[AddCommGrpCat.{u + 1}]) (q + 1)) :=
      (hT.rightDerivedδ_exact₃ ((h)_*[AddCommGrpCat.{u + 1}]) (q + 1)).epi_f
        ((((h)_*[AddCommGrpCat.{u + 1}]).isZero_rightDerived_obj_injective_succ (q + 1)
          _).eq_of_tgt _ _)
    exact (ih T.X₃ (H.cokernel t hT)).of_epi
      (Φ.map (hT.rightDerivedδ ((h)_*[AddCommGrpCat.{u + 1}]) (q + 1)))

/-- An abelian étale sheaf on the spectrum of a separably closed field whose stalk at the
identity geometric point vanishes is zero. -/
lemma isZero_of_isZero_uliftSheafFiber
    (Z : Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hZ : IsZero (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber.obj Z)) :
    IsZero Z := by
  have hc := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of Ω)) (ι := PUnit.{u + 1}) (Ω := fun _ ↦ Ω) (fun _ ↦ 𝟙 _)
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨PUnit.unit, x, rfl⟩)
  have : IsIso (0 : Z ⟶ Z) := by
    refine ((hc.jointlyReflectIsomorphisms AddCommGrpCat.{u + 1}).isIso_iff _).2 ?_
    rintro ⟨-, ⟨-⟩⟩
    exact ⟨⟨𝟙 _, hZ.eq_of_src _ _, hZ.eq_of_src _ _⟩⟩
  refine (IsZero.iff_id_eq_zero Z).2 ?_
  rw [← IsIso.hom_inv_id (0 : Z ⟶ Z), zero_comp]

end Stalk

variable {X S : Scheme.{u}} (h : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The morphism `X ×_S V' ⟶ X ×_S V` induced by a morphism `f : V' ⟶ V` of pointed étale
neighbourhoods of a geometric point of `S`. -/
noncomputable abbrev pullbackNeighborhoodMap {x y : PointedEtaleNeighborhood s} (f : y ⟶ x) :
    pullback h y.1.hom ⟶ pullback h x.1.hom :=
  pullback.map h y.1.hom h x.1.hom (𝟙 X) f.1.left (𝟙 S) (by simp)
    (by simp [MorphismProperty.Over.w f.1])

/-- **Geometric stalks of higher direct images.** Let `h : X ⟶ S`, `F` an abelian étale sheaf
on `X`, `s` a geometric point of `S` and `q > 0`. If for every pointed étale neighbourhood `V`
of `s` every class of `Hᵠ(X ×_S V, F|)` vanishes on `X ×_S V'` for some pointed étale
neighbourhood `V' ⟶ V`, then the geometric stalk `s^* Rᵠh_* F` vanishes. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_forall_exists
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q)
    (H : ∀ (x : PointedEtaleNeighborhood s)
      (c : Sheaf.H ((pullback.fst h x.1.hom)^*[AddCommGrpCat.{u + 1}].obj F) q),
      ∃ (y : PointedEtaleNeighborhood s) (f : y ⟶ x),
        cohomologyMap (pullbackNeighborhoodMap h s f) _ q c = 0) :
    IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F)) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have key : IsZero ((pointSmallEtale (𝟙 _ ≫ s)).sheafFiber.obj
      ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived (q + 1)).obj F)) := by
    rw [Category.id_comp]
    exact isZero_sheafFiber_rightDerived_lowerStar s q F H
  refine isZero_of_isZero_uliftSheafFiber _ (key.of_iso ?_)
  exact (upperStarCompUliftSheafFiberIso AddCommGrpCat.{u + 1} s (𝟙 _)).app _ ≪≫
    ((pointSmallEtale (𝟙 _ ≫ s)).uliftSheafFiberIso AddCommGrpCat.{u + 1}).app _

end AlgebraicGeometry.Etale
