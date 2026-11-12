import Langlands.AlgebraicGeometry.Picard.FlatPicardInfinitesimalGluing
import Langlands.AlgebraicGeometry.Picard.LineBundleStackDictionary
import Langlands.AlgebraicGeometry.Picard.SquareGluingFullyFaithful
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentUniquenessProof
import Langlands.CategoryTheory.Sites.PseudofunctorSquareGluing

/-! # Square gluing for the actual relative Picard pseudofunctor -/

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorSquareGluing

/-- The module form of an inverse composition comparison of the line-bundle
pseudofunctor. -/
lemma realization_modHom_mapComp'_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (u : Y ⟶ Z)
    (u' : X ⟶ Z) (h : g ≫ u = u') (hp : u.op.toLoc ≫ g.op.toLoc = u'.op.toLoc)
    (M : pseudofunctor.{u}.obj (.mk (op Z))) :
    moduleRealization.modHom ((pseudofunctor.{u}.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc
      hp).inv.toNatTrans.app M) =
      (UnitCocycleDescentUniqueness.compIso g u u' h (mod M)).hom := by
  have hcomp :
      moduleRealization.modHom ((pseudofunctor.{u}.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc
        hp).hom.toNatTrans.app M) =
        (UnitCocycleDescentUniqueness.compIso g u u' h (mod M)).inv :=
    modHom_mapComp'_hom g u u' h hp M
  have h1 := moduleRealization.modHom_comp
    ((pseudofunctor.{u}.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc hp).inv.toNatTrans.app M)
    ((pseudofunctor.{u}.mapComp' u.op.toLoc g.op.toLoc u'.op.toLoc hp).hom.toNatTrans.app M)
  rw [Cat.Hom.inv_hom_id_toNatTrans_app, moduleRealization.modHom_id] at h1
  rw [hcomp] at h1
  rw [← cancel_mono (UnitCocycleDescentUniqueness.compIso g u u' h (mod M)).inv, ← h1]
  simp

set_option maxHeartbeats 4000000 in
/-- The overlap isomorphism of the line-bundle pseudofunctor on a commuting square of
schemes is the published `squarePullbackIso`. -/
lemma squareIso_pseudofunctor {Y₀ Y₁ Y₂ Y : Scheme.{u}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂}
    {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Z : PicardGroupoid Y) :
    squareIso pseudofunctor.{u} w Z = (squarePullbackIso i₁ i₂ j₁ j₂ w).app Z := by
  have hcomp (hp : j₂.op.toLoc ≫ i₂.op.toLoc = (i₁ ≫ j₁).op.toLoc) :
      moduleRealization.modHom
        ((pseudofunctor.{u}.mapComp' j₂.op.toLoc i₂.op.toLoc (i₁ ≫ j₁).op.toLoc
          hp).hom.toNatTrans.app Z) =
        (UnitCocycleDescentUniqueness.compIso i₂ j₂ (i₁ ≫ j₁) w.symm (mod Z)).inv :=
    modHom_mapComp'_hom i₂ j₂ (i₁ ≫ j₁) w.symm hp Z
  apply Iso.ext
  apply moduleRealization.hom_ext
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Cat.Hom.toNatIso_inv, Cat.Hom.toNatIso_hom, moduleRealization.modHom_comp]
  rw [realization_modHom_mapComp'_inv i₁ j₁ (i₁ ≫ j₁) rfl]
  rw [hcomp]
  change _ = ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app Z).iso.hom.hom
  rw [SquareGluingFullyFaithful.squarePullbackIso_app,
    UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso j₂ i₁ i₂ j₁ w (i₁ ≫ j₁) rfl
      w.symm]

variable {S X : Scheme.{u}} (f : X ⟶ S) {T₀ T₁ T₂ T : Over S}
  {i₁ : T₀ ⟶ T₁} {i₂ : T₀ ⟶ T₂} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T}

/-- The overlap isomorphism of the relative Picard pseudofunctor on a commuting square of
test objects is the published comparison isomorphism of the base-changed square. -/
lemma squareIso_relative (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Z : PicardGroupoid ((relativeSpace f).obj T)) :
    squareIso (relative f) w Z =
      (squarePullbackIso ((relativeSpace f).map i₁) ((relativeSpace f).map i₂)
        ((relativeSpace f).map j₁) ((relativeSpace f).map j₂)
        (relativeSquare_comm f i₁ i₂ j₁ j₂ w)).app Z :=
  (squareIso_comp (relativeSpace f) pseudofunctor.{u} w Z).trans (squareIso_pseudofunctor _ Z)

set_option maxHeartbeats 4000000 in
/-- If the published comparison functor of a square of test objects is an equivalence,
morphisms of the relative Picard pseudofunctor glue uniquely along the square. -/
theorem isSquareHomGluing_of_isEquivalence (w : i₁ ≫ j₁ = i₂ ≫ j₂)
    (hC : (relativeSquareComparison f i₁ i₂ j₁ j₂ w).IsEquivalence) :
    IsSquareHomGluing (relative f) w := by
  intro Z Z' φ₁ φ₂ h
  rw [squareIso_relative, squareIso_relative] at h
  let ψ : (relativeSquareComparison f i₁ i₂ j₁ j₂ w).obj Z ⟶
      (relativeSquareComparison f i₁ i₂ j₁ j₂ w).obj Z' :=
    { left := φ₁, right := φ₂, w := h }
  obtain ⟨φ, hφ⟩ := (relativeSquareComparison f i₁ i₂ j₁ j₂ w).map_surjective ψ
  refine ⟨φ, ⟨congrArg CommaMorphism.left hφ, congrArg CommaMorphism.right hφ⟩, ?_⟩
  rintro φ' ⟨h₁, h₂⟩
  apply (relativeSquareComparison f i₁ i₂ j₁ j₂ w).map_injective
  rw [hφ]
  apply Comma.hom_ext
  · exact h₁
  · exact h₂

set_option maxHeartbeats 4000000 in
/-- If the published comparison functor of a square of test objects is an equivalence,
objects of the relative Picard pseudofunctor glue along the square. -/
theorem isSquareEffective_of_isEquivalence (w : i₁ ≫ j₁ = i₂ ≫ j₂)
    (hC : (relativeSquareComparison f i₁ i₂ j₁ j₂ w).IsEquivalence) :
    IsSquareEffective (relative f) w := by
  intro M₁ M₂ e
  let D : SquareGluingData ((relativeSpace f).map i₁) ((relativeSpace f).map i₂) :=
    { left := M₁, right := M₂, hom := e.hom }
  let eD := (relativeSquareComparison f i₁ i₂ j₁ j₂ w).objObjPreimageIso D
  refine ⟨(relativeSquareComparison f i₁ i₂ j₁ j₂ w).objPreimage D, Comma.leftIso eD,
    Comma.rightIso eD, ?_⟩
  apply Iso.ext
  rw [Iso.trans_hom, Iso.trans_hom, squareIso_relative]
  exact eD.hom.w.symm

section Affine

variable {k R A B C : Type u} [CommRing k] [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [Flat g]
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))

/-- Over a flat scheme, actual line bundles glue along the affine square of a ring
pullback `R = A ×_C B` with `B → C` surjective with nilpotent kernel. -/
theorem affine_isSquareEffective (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    IsSquareEffective (relative g) (affineSquare_comm p q a b h) :=
  isSquareEffective_of_isEquivalence g _
    (FlatInfinitesimalGluing.affineSquareComparison_isEquivalence g p q a b h hb hn)

/-- Over a flat scheme, actual isomorphisms of line bundles glue uniquely along the affine
square of a ring pullback `R = A ×_C B` with `B → C` surjective with nilpotent kernel. -/
theorem affine_isSquareHomGluing (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    IsSquareHomGluing (relative g) (affineSquare_comm p q a b h) :=
  isSquareHomGluing_of_isEquivalence g _
    (FlatInfinitesimalGluing.affineSquareComparison_isEquivalence g p q a b h hb hn)

end Affine

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
