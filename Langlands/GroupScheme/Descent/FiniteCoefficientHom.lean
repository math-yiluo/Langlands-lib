import Langlands.GroupScheme.Descent.Data
import Langlands.AbelianScheme.RelativeHomNeronExtension
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map
import Mathlib.RingTheory.Localization.AsSubring

/-! # Finite coefficient models of supplied group-scheme homomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

private theorem comparison_inv_fst_fst {S S' S'' : Scheme.{u}}
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

private theorem comparison_inv_fst_snd {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (a : S'' ⟶ S') (c : S'' ⟶ S) (h : a ≫ b = c)
    (G : GroupScheme S) :
    ((pullbackComparison b a c h G).inv.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) a) ≫ pullback.snd G.X.hom b =
      pullback.snd G.X.hom c ≫ a := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ a) (pullbackComparison b a c h G).inv.hom.hom.w

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Reflect the homomorphism property from the generic fibre of a flat source. -/
theorem isMonHom_of_generic
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [Flat G.X.hom] [IsSeparated H.X.hom] (g : G.X ⟶ H.X)
    [IsMonHom ((Over.pullback (Spec.algebraMap R K)).map g)] :
    IsMonHom g := by
  have : Flat (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
    rw [Over.tensorUnit_hom]
    exact MorphismProperty.id_mem @Flat _
  have : Flat (G.X ⊗ G.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  exact Langlands.AbelianScheme.isMonHom_of_map
    (Over.pullback (Spec.algebraMap R K)) g
    (fun _ _ h => Langlands.AbelianScheme.genericFibre_map_injective K h)
    (fun _ _ h => Langlands.AbelianScheme.genericFibre_map_injective K h)

omit [IsDomain R] in
/-- A supplied generic homomorphism descends to a finitely generated coefficient
subalgebra, with its actual pullback compatibility. -/
theorem exists_fg_hom
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [IsSeparated H.X.hom]
    (f : (baseChange (Spec.algebraMap R K)).obj G ⟶
      (baseChange (Spec.algebraMap R K)).obj H) :
    ∃ (T : Subalgebra R K), T.FG ∧
      ∃ g : (baseChange (Spec.algebraMap R T)).obj G ⟶
          (baseChange (Spec.algebraMap R T)).obj H,
        (baseChange (Spec.algebraMap T K)).map g ≫
            (pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T K)
              (Spec.algebraMap R K)
              (by simp [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]) H).hom =
          (pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T K)
              (Spec.algebraMap R K)
              (by simp [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]) G).hom ≫ f := by
  obtain ⟨T, hT, _, g₀, hg₀, hrec⟩ :=
    exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      G.X.hom H.X.hom f.hom.hom.left f.hom.hom.w ∅
  let b := Spec.algebraMap R T
  let a := Spec.algebraMap T K
  let c := Spec.algebraMap R K
  have hab : a ≫ b = c := by
    dsimp [a, b, c, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let eG := pullbackComparison b a c hab G
  let eH := pullbackComparison b a c hab H
  let g : ((baseChange b).obj G).X ⟶ ((baseChange b).obj H).X :=
    Over.homMk g₀ hg₀
  let ψ := eG.hom ≫ f ≫ eH.inv
  have hrec' :
      (eG.inv.hom.hom.left ≫ pullback.fst (pullback.snd G.X.hom b) a) ≫ g₀ =
        f.hom.hom.left ≫
          (eH.inv.hom.hom.left ≫ pullback.fst (pullback.snd H.X.hom b) a) :=
    hrec _ _ (comparison_inv_fst_fst b a c hab G)
      (comparison_inv_fst_snd b a c hab G)
      (comparison_inv_fst_fst b a c hab H)
      (comparison_inv_fst_snd b a c hab H)
  have hmap : (Over.pullback a).map g = ψ.hom.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((Over.pullback a).map g).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst]
      have hr := congrArg (fun q => eG.hom.hom.hom.left ≫ q) hrec'
      have hi := congrArg (fun q => q.hom.hom.left) eG.hom_inv_id
      change eG.hom.hom.hom.left ≫ eG.inv.hom.hom.left = 𝟙 _ at hi
      change pullback.fst (pullback.snd G.X.hom b) a ≫ g₀ =
        (eG.hom.hom.hom.left ≫ f.hom.hom.left ≫ eH.inv.hom.hom.left) ≫
          pullback.fst (pullback.snd H.X.hom b) a
      simpa only [← Category.assoc, hi, Category.id_comp] using hr
    · exact ((Over.pullback a).map g).w.trans ψ.hom.hom.w.symm
  have : IsMonHom ((Over.pullback a).map g) := by
    rw [hmap]
    infer_instance
  have : Flat ((baseChange b).obj G).X.hom := by
    change Flat (pullback.snd G.X.hom b)
    infer_instance
  have : IsSeparated ((baseChange b).obj H).X.hom := by
    change IsSeparated (pullback.snd H.X.hom b)
    infer_instance
  have : IsMonHom g := isMonHom_of_generic (K := K) g
  refine ⟨T, hT, Grp.homMk g, ?_⟩
  change (baseChange a).map (Grp.homMk g) ≫ eH.hom = eG.hom ≫ f
  have heq : (baseChange a).map (Grp.homMk g) = ψ := by
    apply Grp.hom_ext
    exact hmap
  rw [heq]
  simp [ψ]

omit [IsDomain R] [IsFractionRing R K] in
/-- A homomorphism with closed generic fibre becomes closed over a finitely
generated coefficient subalgebra. -/
theorem exists_fg_closed_baseChange
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [LocallyOfFiniteType G.X.hom]
    (f : G ⟶ H)
    [IsClosedImmersion ((baseChange (Spec.algebraMap R K)).map f).hom.hom.left] :
    ∃ (T : Subalgebra R K), T.FG ∧
      IsClosedImmersion ((baseChange (Spec.algebraMap R T)).map f).hom.hom.left := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) :=
    f.hom.hom.w.symm ▸ (inferInstance : LocallyOfFiniteType G.X.hom)
  let : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  have hw : f.hom.hom.left ≫ H.X.hom = G.X.hom := f.hom.hom.w
  have hA :
      ∀ mA : pullback (f.hom.hom.left ≫ H.X.hom) (Spec.algebraMap R K) ⟶
          pullback H.X.hom (Spec.algebraMap R K),
        mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.hom.hom.left →
        mA ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion mA := by
    rw [hw]
    intro mA hf hs
    have he : mA = ((baseChange (Spec.algebraMap R K)).map f).hom.hom.left := by
      apply pullback.hom_ext
      · change _ = ((Over.pullback (Spec.algebraMap R K)).map f.hom.hom).left ≫ _
        simpa only [Over.pullback_map_left, pullback.lift_fst] using hf
      · exact hs.trans ((Over.pullback (Spec.algebraMap R K)).map f.hom.hom).w.symm
    rw [he]
    infer_instance
  obtain ⟨T, hT, _, hc⟩ :=
    IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map
      f.hom.hom.left H.X.hom hA ∅
  rw [hw] at hc
  refine ⟨T, hT, hc _ ?_ ?_⟩
  · change ((Over.pullback (Spec.algebraMap R T)).map f.hom.hom).left ≫ _ = _
    simp only [Over.pullback_map_left, pullback.lift_fst]
  · exact ((Over.pullback (Spec.algebraMap R T)).map f.hom.hom).w

omit [IsDomain R] in
/-- A finite coefficient model of the supplied generic homomorphism. -/
structure HomModel
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    (f : (baseChange (Spec.algebraMap R K)).obj G ⟶
      (baseChange (Spec.algebraMap R K)).obj H) where
  coefficients : Subalgebra R K
  finite : coefficients.FG
  hom : (baseChange (Spec.algebraMap R coefficients)).obj G ⟶
    (baseChange (Spec.algebraMap R coefficients)).obj H
  recovery : (baseChange (Spec.algebraMap coefficients K)).map hom ≫
      (pullbackComparison (Spec.algebraMap R coefficients)
        (Spec.algebraMap coefficients K) (Spec.algebraMap R K)
        (by simp [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq]) H).hom =
    (pullbackComparison (Spec.algebraMap R coefficients)
      (Spec.algebraMap coefficients K) (Spec.algebraMap R K)
      (by simp [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]) G).hom ≫ f

omit [IsDomain R] in
/-- Choose the actual finite coefficient model, including its exact recovery. -/
def homModel
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [IsSeparated H.X.hom]
    (f : (baseChange (Spec.algebraMap R K)).obj G ⟶
      (baseChange (Spec.algebraMap R K)).obj H) : HomModel G H f :=
  let h := exists_fg_hom G H f
  { coefficients := Classical.choose h
    finite := (Classical.choose_spec h).1
    hom := Classical.choose (Classical.choose_spec h).2
    recovery := Classical.choose_spec (Classical.choose_spec h).2 }

end Langlands.GroupScheme.Descent.FiniteCoefficient
