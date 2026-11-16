import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneralStatement
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType

/-! # Finite coefficient models of homomorphisms over arbitrary algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

private theorem general_comparison_inv_fst_fst {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (a : S'' ⟶ S') (c : S'' ⟶ S) (h : a ≫ b = c)
    (G : GroupScheme S) :
    ((pullbackComparison b a c h G).inv.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) a) ≫ pullback.fst G.X.hom b =
      pullback.fst G.X.hom c := by
  have hh := pullbackComparison_inv_fst b a c h G
  change (pullbackComparison b a c h G).inv.hom.hom.left ≫
      pullback.fst (pullback.snd G.X.hom b) a ≫ pullback.fst G.X.hom b =
    pullback.fst G.X.hom c at hh
  simpa only [Category.assoc] using hh

private theorem general_comparison_inv_fst_snd {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (a : S'' ⟶ S') (c : S'' ⟶ S) (h : a ≫ b = c)
    (G : GroupScheme S) :
    ((pullbackComparison b a c h G).inv.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) a) ≫ pullback.snd G.X.hom b =
      pullback.snd G.X.hom c ≫ a := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ a) (pullbackComparison b a c h G).inv.hom.hom.w

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Equality of two maps over the coefficient ring descends, and persists at
all larger coefficient subalgebras. -/
theorem exists_fg_map_eq
    {X Y : Over (Spec (CommRingCat.of R))}
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    (f g : X ⟶ Y)
    (h : (Over.pullback (Spec.algebraMap R A)).map f =
      (Over.pullback (Spec.algebraMap R A)).map g) (s : Finset A) :
    ∃ T : Subalgebra R A, T.FG ∧ (s : Set A) ⊆ T ∧
      ∀ (U : Subalgebra R A), T ≤ U →
        (Over.pullback (Spec.algebraMap R U)).map f =
          (Over.pullback (Spec.algebraMap R U)).map g := by
  have hfst : pullback.fst X.hom (Spec.algebraMap R A) ≫ f.left =
      pullback.fst X.hom (Spec.algebraMap R A) ≫ g.left := by
    have he := congrArg (fun q => q.left ≫ pullback.fst Y.hom (Spec.algebraMap R A)) h
    simpa only [Over.pullback_map_left, pullback.lift_fst] using he
  obtain ⟨T, hT, hs, heq⟩ :=
    exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      X.hom Y.hom f.left g.left f.w g.w hfst s
  refine ⟨T, hT, hs, ?_⟩
  intro U hTU
  let b := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTU).toRingHom)
  have hb : b ≫ Spec.algebraMap R T = Spec.algebraMap R U := by
    rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let q : pullback X.hom (Spec.algebraMap R U) ⟶
      pullback X.hom (Spec.algebraMap R T) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b) (by
      rw [Category.assoc, hb, pullback.condition])
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((Over.pullback _).map f).left ≫ _ = ((Over.pullback _).map g).left ≫ _
    simp only [Over.pullback_map_left, pullback.lift_fst]
    have he := congrArg (fun k => q ≫ k) heq
    simpa only [Spec.algebraMap, ← Category.assoc, q, pullback.lift_fst] using he
  · exact ((Over.pullback _).map f).w.trans ((Over.pullback _).map g).w.symm

/-- If a supplied map becomes a group homomorphism over an arbitrary algebra,
it becomes a homomorphism already over finite coefficients. -/
theorem exists_fg_isMonHom
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [QuasiCompact G.X.hom] [LocallyOfFiniteType H.X.hom]
    (f : G.X ⟶ H.X)
    [IsMonHom ((Over.pullback (Spec.algebraMap R A)).map f)] (s : Finset A) :
    ∃ T : Subalgebra R A, T.FG ∧ (s : Set A) ⊆ T ∧
      IsMonHom ((Over.pullback (Spec.algebraMap R T)).map f) := by
  let F := Over.pullback (Spec.algebraMap R A)
  have h₀ : F.map (η[G.X] ≫ f) = F.map η[H.X] := by
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    rw [F.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (F.map f)
  have h₂ : F.map (μ[G.X] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[H.X]) := by
    apply (cancel_epi (Functor.LaxMonoidal.μ F G.X G.X)).mp
    rw [F.map_comp, F.map_comp, ← Category.assoc,
      ← Functor.LaxMonoidal.μ_natural_assoc]
    exact IsMonHom.mul_hom (F.map f)
  have : QuasiCompact (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
    rw [Over.tensorUnit_hom]
    exact MorphismProperty.id_mem @QuasiCompact _
  have : QuasiCompact (G.X ⊗ G.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  obtain ⟨T₀, hT₀, hs, he₀⟩ := exists_fg_map_eq (η[G.X] ≫ f) η[H.X] h₀ s
  obtain ⟨T₂, hT₂, _, he₂⟩ := exists_fg_map_eq (μ[G.X] ≫ f)
    ((f ⊗ₘ f) ≫ μ[H.X]) h₂ (∅ : Finset A)
  let T := T₀ ⊔ T₂
  have hT : T.FG := hT₀.sup hT₂
  let Fₜ := Over.pullback (Spec.algebraMap R T)
  refine ⟨T, hT, Set.Subset.trans hs (show T₀ ≤ T from le_sup_left), ?_⟩
  constructor
  · have he := he₀ T le_sup_left
    change (Functor.LaxMonoidal.ε Fₜ ≫ Fₜ.map η[G.X]) ≫ Fₜ.map f =
      Functor.LaxMonoidal.ε Fₜ ≫ Fₜ.map η[H.X]
    rw [Category.assoc, ← Fₜ.map_comp, he]
  · have he := he₂ T le_sup_right
    change (Functor.LaxMonoidal.μ Fₜ G.X G.X ≫ Fₜ.map μ[G.X]) ≫ Fₜ.map f =
      (Fₜ.map f ⊗ₘ Fₜ.map f) ≫
        (Functor.LaxMonoidal.μ Fₜ H.X H.X ≫ Fₜ.map μ[H.X])
    rw [Category.assoc, ← Fₜ.map_comp, he, Fₜ.map_comp,
      Functor.LaxMonoidal.μ_natural_assoc]

/-- Descent of a supplied homomorphism over an arbitrary coefficient algebra. -/
theorem exists_fg_hom_general
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (f : (baseChange (Spec.algebraMap R A)).obj G ⟶
      (baseChange (Spec.algebraMap R A)).obj H) (s : Finset A) :
    ∃ (T : Subalgebra R A), T.FG ∧ (s : Set A) ⊆ T ∧
      ∃ g : (baseChange (Spec.algebraMap R T)).obj G ⟶
          (baseChange (Spec.algebraMap R T)).obj H,
        (baseChange (Spec.algebraMap T A)).map g ≫
            (pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T A)
              (Spec.algebraMap R A)
              (by
                rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
                  ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                rfl) H).hom =
          (pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T A)
              (Spec.algebraMap R A)
              (by
                rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
                  ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                rfl) G).hom ≫ f := by
  obtain ⟨T, hT, hs, g₀, hg₀, hrec⟩ :=
    exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      G.X.hom H.X.hom f.hom.hom.left f.hom.hom.w s
  let b := Spec.algebraMap R T
  let q := Spec.algebraMap T A
  let c := Spec.algebraMap R A
  have hqb : q ≫ b = c := by
    dsimp [q, b, c, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let eG := pullbackComparison b q c hqb G
  let eH := pullbackComparison b q c hqb H
  let g : ((baseChange b).obj G).X ⟶ ((baseChange b).obj H).X :=
    Over.homMk g₀ hg₀
  let ψ := eG.hom ≫ f ≫ eH.inv
  have hrec' :
      (eG.inv.hom.hom.left ≫ pullback.fst (pullback.snd G.X.hom b) q) ≫ g₀ =
        f.hom.hom.left ≫
          (eH.inv.hom.hom.left ≫ pullback.fst (pullback.snd H.X.hom b) q) :=
    hrec _ _ (general_comparison_inv_fst_fst b q c hqb G)
      (general_comparison_inv_fst_snd b q c hqb G)
      (general_comparison_inv_fst_fst b q c hqb H)
      (general_comparison_inv_fst_snd b q c hqb H)
  have hmap : (Over.pullback q).map g = ψ.hom.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((Over.pullback q).map g).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst]
      have hr := congrArg (fun z => eG.hom.hom.hom.left ≫ z) hrec'
      have hi := congrArg (fun z => z.hom.hom.left) eG.hom_inv_id
      change eG.hom.hom.hom.left ≫ eG.inv.hom.hom.left = 𝟙 _ at hi
      change pullback.fst (pullback.snd G.X.hom b) q ≫ g₀ =
        (eG.hom.hom.hom.left ≫ f.hom.hom.left ≫ eH.inv.hom.hom.left) ≫
          pullback.fst (pullback.snd H.X.hom b) q
      simpa only [← Category.assoc, hi, Category.id_comp] using hr
    · exact ((Over.pullback q).map g).w.trans ψ.hom.hom.w.symm
  have : IsMonHom ((Over.pullback q).map g) := by
    rw [hmap]
    infer_instance
  have : QuasiCompact ((baseChange b).obj G).X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType ((baseChange b).obj H).X.hom := by
    change LocallyOfFiniteType (pullback.snd H.X.hom b)
    infer_instance
  obtain ⟨U, hU, -, hhom⟩ := exists_fg_isMonHom g (∅ : Finset A)
  let d := Spec.algebraMap T U
  let a := Spec.algebraMap U A
  let v := Spec.algebraMap R U
  have hdb : d ≫ b = v := by
    dsimp [d, b, v, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have had : a ≫ d = q := by
    dsimp [a, d, q, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hav : a ≫ v = c := by
    rw [← hdb, ← Category.assoc, had, hqb]
  let iG := pullbackComparison b d v hdb G
  let iH := pullbackComparison b d v hdb H
  let jG := pullbackComparison v a c hav G
  let jH := pullbackComparison v a c hav H
  let : IsMonHom ((Over.pullback d).map g) := hhom
  let gU : (baseChange d).obj ((baseChange b).obj G) ⟶
      (baseChange d).obj ((baseChange b).obj H) :=
    Grp.homMk ((Over.pullback d).map g)
  let gV := iG.inv ≫ gU ≫ iH.hom
  have hfinite : (U.restrictScalars R).FG := by
    have h₁ : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
    have h₂ : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
    have h₃ : Algebra.FiniteType R U := Algebra.FiniteType.trans h₁ h₂
    exact (Subalgebra.fg_iff_finiteType (U.restrictScalars R)).mpr h₃
  refine ⟨U.restrictScalars R, hfinite, ?_, gV, ?_⟩
  · intro x hx
    exact U.algebraMap_mem ⟨x, hs hx⟩
  change (baseChange a).map gV ≫ jH.hom = jG.hom ≫ f
  have hproj :
      pullback.fst (pullback.snd G.X.hom v) a ≫
          iG.inv.hom.hom.left ≫ pullback.fst (pullback.snd G.X.hom b) d =
        jG.hom.hom.hom.left ≫ eG.inv.hom.hom.left ≫
          pullback.fst (pullback.snd G.X.hom b) q := by
    apply pullback.hom_ext
    · have hi := general_comparison_inv_fst_fst b d v hdb G
      have he := general_comparison_inv_fst_fst b q c hqb G
      have hj := pullbackComparison_hom_fst v a c hav G
      change jG.hom.hom.hom.left ≫ pullback.fst G.X.hom c =
        pullback.fst (pullback.snd G.X.hom v) a ≫ pullback.fst G.X.hom v at hj
      simp only [Category.assoc] at hi he ⊢
      rw [hi, he]
      exact hj.symm
    · simp only [Category.assoc, pullback.condition]
      have hiw := iG.inv.hom.hom.w
      change iG.inv.hom.hom.left ≫ pullback.snd (pullback.snd G.X.hom b) d =
        pullback.snd G.X.hom v at hiw
      have hew := eG.inv.hom.hom.w
      change eG.inv.hom.hom.left ≫ pullback.snd (pullback.snd G.X.hom b) q =
        pullback.snd G.X.hom c at hew
      have hjw := jG.hom.hom.hom.w
      change jG.hom.hom.hom.left ≫ pullback.snd G.X.hom c =
        pullback.snd (pullback.snd G.X.hom v) a at hjw
      rw [← Category.assoc iG.inv.hom.hom.left, hiw]
      rw [← Category.assoc, pullback.condition, Category.assoc, had]
      rw [← Category.assoc eG.inv.hom.hom.left, hew]
      rw [← Category.assoc jG.hom.hom.hom.left, hjw]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (((Over.pullback a).map gV.hom.hom).left ≫ jH.hom.hom.hom.left) ≫
        pullback.fst H.X.hom c =
      (jG.hom.hom.hom.left ≫ f.hom.hom.left) ≫ pullback.fst H.X.hom c
    rw [Category.assoc, pullbackComparison_hom_fst]
    change ((Over.pullback a).map gV.hom.hom).left ≫
        pullback.fst (pullback.snd H.X.hom v) a ≫ pullback.fst H.X.hom v = _
    have hgV : ((Over.pullback a).map gV.hom.hom).left ≫
        pullback.fst (pullback.snd H.X.hom v) a =
      pullback.fst (pullback.snd G.X.hom v) a ≫ gV.hom.hom.left :=
      pullback.lift_fst _ _ _
    rw [← Category.assoc, hgV]
    change (pullback.fst (pullback.snd G.X.hom v) a ≫
        (iG.inv.hom.hom.left ≫ ((Over.pullback d).map g).left ≫
          iH.hom.hom.hom.left)) ≫ pullback.fst H.X.hom v = _
    have hiH := pullbackComparison_hom_fst b d v hdb H
    change iH.hom.hom.hom.left ≫ pullback.fst H.X.hom v =
      pullback.fst (pullback.snd H.X.hom b) d ≫ pullback.fst H.X.hom b at hiH
    simp only [Category.assoc]
    rw [hiH]
    have hgd : ((Over.pullback d).map g).left ≫
        pullback.fst (pullback.snd H.X.hom b) d =
      pullback.fst (pullback.snd G.X.hom b) d ≫ g₀ :=
      pullback.lift_fst _ _ _
    rw [← Category.assoc ((Over.pullback d).map g).left, hgd]
    have hproj' := congrArg (fun z => z ≫ g₀ ≫ pullback.fst H.X.hom b) hproj
    simp only [Category.assoc] at hproj' ⊢
    rw [hproj']
    have hr := congrArg
      (fun z => jG.hom.hom.hom.left ≫ z ≫ pullback.fst H.X.hom b) hrec'
    have heH := general_comparison_inv_fst_fst b q c hqb H
    have heH' := congrArg
      (fun z => jG.hom.hom.hom.left ≫ f.hom.hom.left ≫ z) heH
    simp only [Category.assoc] at hr heH'
    exact hr.trans heH'
  · exact ((baseChange a).map gV ≫ jH.hom).hom.hom.w.trans
      (jG.hom ≫ f).hom.hom.w.symm

/-- Exact finite coefficient descent, uniform in the universe. -/
theorem homGeneral : HomGeneralStatement.{u} := by
  intro R A _ _ _ G H _ _ _ f s
  exact exists_fg_hom_general G H f s

end Langlands.GroupScheme.Descent.FiniteCoefficient
