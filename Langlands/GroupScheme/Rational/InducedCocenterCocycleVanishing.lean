import Langlands.GroupScheme.Rational.SimplyConnectedBorelTorusCocycles
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.FiniteSeparableQuotientLifts
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction
import Langlands.GroupScheme.CocycleAffineRefinement

/-! # Cocycles of a group with induced cocenter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1150000

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {G : GroupScheme (Spec (CommRingCat.of F))} {Q : CommGroupScheme (Spec (CommRingCat.of F))}

private theorem exists_cochain_lift_on_finiteGalois_cover (q : G ⟶ Q.toGrp)
    [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    (v : GaloisCocycle.cover F L ⟶ Q.X) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (r : GaloisCocycle.cover F E ⟶ GaloisCocycle.cover F L) (g : GaloisCocycle.cover F E ⟶ G.X),
      g ≫ q.hom.hom = r ≫ v := by
  let T : Over (Spec (CommRingCat.of L)) := Over.mk (pullback.snd q.hom.hom.left v.left)
  let : Smooth T.hom := inferInstanceAs (Smooth (pullback.snd q.hom.hom.left v.left))
  let : Surjective T.hom := inferInstanceAs (Surjective (pullback.snd q.hom.hom.left v.left))
  let : Nonempty T.left := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨z, _⟩ := (inferInstance : Surjective T.hom).surj x
    exact ⟨z⟩
  obtain ⟨M, _, _, hfin, hsep, ⟨w⟩⟩ :=
    Langlands.AlgebraicGeometry.exists_finiteSeparable_point_of_smooth (F := L) T
  let : Algebra F M := ((algebraMap L M).comp (algebraMap F L)).toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional L M := hfin
  let : Algebra.IsSeparable L M := hsep
  let : FiniteDimensional F M := FiniteDimensional.trans F L M
  let : Algebra.IsSeparable F M := Algebra.IsSeparable.trans F L M
  let φ := IsScalarTower.toAlgHom F L M
  let s := ringTestMap F φ
  have hleft : w.left ≫ pullback.snd q.hom.hom.left v.left = s.left := Over.w w
  let g : ringTest F M ⟶ G.X := Over.homMk (w.left ≫ pullback.fst q.hom.hom.left v.left) (by
    rw [Category.assoc, ← Over.w q.hom.hom, pullback.condition_assoc,
      Over.w v, ← Category.assoc, hleft]
    exact Over.w s)
  have hg : g ≫ q.hom.hom = s ≫ v := by
    apply Over.OverMorphism.ext
    change (w.left ≫ pullback.fst q.hom.hom.left v.left) ≫ q.hom.hom.left = s.left ≫ v.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hleft]
  obtain ⟨E, hfin, hgal, ⟨j⟩⟩ := exists_finite_galois_algHom F M
  let : FiniteDimensional F E := hfin
  let : IsGalois F E := hgal
  let t := ringTestMap F j
  exact ⟨E, inferInstance, inferInstance, hfin, hgal, t ≫ s, t ≫ g,
    by rw [Category.assoc, hg, Category.assoc]⟩

/-- Vanishing for a represented smooth kernel and an induced torus quotient
implies vanishing on each finite Galois cover of the base field. -/
theorem Cocycle.isTrivial_of_inducedTorusQuotient
    {D : GroupScheme (Spec (CommRingCat.of F))} (i : D ⟶ G) [Mono i.hom.hom]
    (q : G ⟶ Q.toGrp) [QuasiCompact q.hom.hom.left] (hD : Smooth D.X.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) (hQ : IsInducedTorus Q)
    (hvan : ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
      (ζ : Cocycle D (GaloisCocycle.cover F E)), ζ.IsTrivial)
    (ξ : Cocycle G (GaloisCocycle.cover F L)) : ξ.IsTrivial := by
  let U := GaloisCocycle.cover F L
  obtain ⟨hs, hf, _⟩ := fieldExtension_fpqc F L
  let : Surjective U.hom := hs
  let : Flat U.hom := hf
  let : IsAffineHom U.hom := inferInstanceAs (IsAffineHom (algebraBaseMap F L))
  obtain ⟨v, hv⟩ := (ξ.map q).isTrivial_of_isInducedTorus (U := U) hQ
  let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hD
  let : Surjective q.hom.hom.left := hq.2.1
  obtain ⟨E, _, _, _, _, r, f, hf⟩ := exists_cochain_lift_on_finiteGalois_cover q v
  let W := GaloisCocycle.cover F E
  let corrected := (ξ.refine r).twist f
  have hval {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ W) :
      ∃ d : Z ⟶ D.X, d ≫ i.hom.hom = corrected.toFun a b := by
    apply SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hq.2.2.2
    have hab := hv (a ≫ r) (b ≫ r)
    change ξ.toFun (a ≫ r) (b ≫ r) ≫ q.hom.hom = ((a ≫ r) ≫ v) * ((b ≫ r) ≫ v)⁻¹ at hab
    change ((a ≫ f)⁻¹ * ξ.toFun (a ≫ r) (b ≫ r) * (b ≫ f)) ≫ q.hom.hom = 1
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hf, hab]
    group
  have h := hvan E (corrected.lift i (fun _ _ => hval _ _))
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F E
  let : Surjective W.hom := hs
  let : Flat W.hom := hf
  let : QuasiCompact W.hom := hq
  exact Cocycle.IsTrivial.of_refine_fpqcCover (V := W) r
    (Cocycle.IsTrivial.of_twist (Cocycle.IsTrivial.of_lift h))

end Langlands.GroupScheme
