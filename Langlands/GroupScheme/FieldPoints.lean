import Langlands.GroupScheme.AffinePoints
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.CentralSurjectionImage.SurjectiveCharacterPoint
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Lifting and descending points of group schemes along field extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.FieldPoints

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]

/-- A morphism of group schemes that is surjective on underlying schemes lifts every point
over a field `K` to a point over some field extension `L/K`. -/
theorem exists_field_lift {H G : GroupScheme (Spec (CommRingCat.of k))} (p : H ⟶ G)
    (hp : Surjective p.hom.hom.left) (g : Lie.AffinePoints G K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra k L) (_ : IsScalarTower k K L)
      (h : Lie.AffinePoints H L),
        h ≫ p.hom.hom = Lie.affineMap G (IsScalarTower.toAlgHom k K L) g := by
  classical
  let R := CommRingCat.of k
  let gL : Spec (CommRingCat.of K) ⟶ G.X.left := g.left
  let pL := p.hom.hom.left
  obtain ⟨z, hz⟩ := hp.surj (gL (IsLocalRing.closedPoint K))
  let α := G.X.left.descResidueField (Scheme.stalkClosedPointTo gL)
  have hα : Spec.map α ≫ G.X.left.fromSpecResidueField _ = gL :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K _ gL
  let β := (G.X.left.residueFieldCongr hz.symm).hom ≫ pL.residueFieldMap z
  have hβ : Spec.map β ≫ G.X.left.fromSpecResidueField _ =
      H.X.left.fromSpecResidueField z ≫ pL := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  obtain ⟨L, _, _, a, b, hab⟩ := CentralSurjectionImage.exists_isAlgClosed_compositum β.hom α.hom
  let _ : Algebra K L := b.toAlgebra
  let _ : Algebra k L := (b.comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let x' : Spec (CommRingCat.of L) ⟶ H.X.left :=
    Spec.map (CommRingCat.ofHom a) ≫ H.X.left.fromSpecResidueField z
  have e : β ≫ CommRingCat.ofHom a = α ≫ CommRingCat.ofHom b := by
    ext r
    exact congrArg (fun f : _ →+* L => f r) hab
  have hx' : x' ≫ pL = Spec.map (CommRingCat.ofHom b) ≫ gL := by
    calc x' ≫ pL = Spec.map (CommRingCat.ofHom a) ≫ (H.X.left.fromSpecResidueField z ≫ pL) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom a) ≫ (Spec.map β ≫ G.X.left.fromSpecResidueField _) := by
          rw [hβ]
      _ = Spec.map (β ≫ CommRingCat.ofHom a) ≫ G.X.left.fromSpecResidueField _ := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (α ≫ CommRingCat.ofHom b) ≫ G.X.left.fromSpecResidueField _ := by rw [e]
      _ = Spec.map (CommRingCat.ofHom b) ≫ (Spec.map α ≫ G.X.left.fromSpecResidueField _) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom b) ≫ gL :=
          congrArg (Spec.map (CommRingCat.ofHom b) ≫ ·) hα
  have hw : x' ≫ H.X.hom = ((algSpec R).obj (op (CommAlgCat.of R L))).hom := by
    have h1 : pL ≫ G.X.hom = H.X.hom := Over.w p.hom.hom
    have h2 : gL ≫ G.X.hom = ((algSpec R).obj (op (CommAlgCat.of R K))).hom := Over.w g
    rw [← h1, ← Category.assoc, hx', Category.assoc, h2, algSpec_obj_hom, algSpec_obj_hom,
      ← Spec.map_comp]
    rfl
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, Over.homMk x' hw, ?_⟩
  apply Over.OverMorphism.ext
  change x' ≫ pL = ((algSpec R).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k K L)).op).left ≫ gL
  rw [hx']
  rfl

variable {L : Type u} [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]

variable (K L) in
/-- The spectrum map of a field extension is an effective epimorphism of schemes. -/
theorem effectiveEpi_specMap : EffectiveEpi (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc K L
  infer_instance

/-- Restriction of points along a field extension `L/K` is injective. -/
theorem affineMap_injective (H : GroupScheme (Spec (CommRingCat.of k))) :
    Function.Injective (Lie.affineMap H (IsScalarTower.toAlgHom k K L)) := by
  intro x y hxy
  have := effectiveEpi_specMap K L
  apply Over.OverMorphism.ext
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K L)))]
  exact congrArg CommaMorphism.left hxy

/-- Fpqc descent of points along a field extension `L/K`: a point over `L` whose two
restrictions to `L ⊗[K] L` agree comes from a point over `K`. -/
theorem exists_affineMap_eq (H : GroupScheme (Spec (CommRingCat.of k)))
    (x : Lie.AffinePoints H L)
    (hx : Lie.affineMap H
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] L).restrictScalars k) x =
      Lie.affineMap H
        ((Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L).restrictScalars k) x) :
    ∃ y : Lie.AffinePoints H K, Lie.affineMap H (IsScalarTower.toAlgHom k K L) y = x := by
  have := effectiveEpi_specMap K L
  let π := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hl : Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ x.left =
      Spec.map (CommRingCat.ofHom (R := L) (S := L ⊗[K] L)
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L))) ≫
          x.left :=
    congrArg CommaMorphism.left hx
  have hw : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of L)), g₁ ≫ π = g₂ ≫ π →
      g₁ ≫ x.left = g₂ ≫ x.left := by
    intro Z g₁ g₂ h
    let l := pullback.lift g₁ g₂ h
    have e1 : g₁ = l ≫ (pullbackSpecIso K L L).hom ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
      rw [pullbackSpecIso_hom_fst, pullback.lift_fst]
    have e2 : g₂ = l ≫ (pullbackSpecIso K L L).hom ≫
        Spec.map (CommRingCat.ofHom (R := L) (S := L ⊗[K] L)
          (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L))) := by
      rw [pullbackSpecIso_hom_snd, pullback.lift_snd]
    rw [e1, e2, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hl]
  let d : Spec (CommRingCat.of K) ⟶ H.X.left := EffectiveEpi.desc π x.left hw
  have hd : π ≫ d = x.left := EffectiveEpi.fac π x.left hw
  have hover : d ≫ H.X.hom =
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k K))).hom := by
    rw [← cancel_epi π, ← Category.assoc, hd, Over.w x, algSpec_obj_hom, algSpec_obj_hom,
      ← Spec.map_comp]
    congr 1
    ext r
    exact IsScalarTower.algebraMap_apply k K L r
  refine ⟨Over.homMk d hover, ?_⟩
  apply Over.OverMorphism.ext
  exact hd

end Langlands.GroupScheme.FieldPoints
