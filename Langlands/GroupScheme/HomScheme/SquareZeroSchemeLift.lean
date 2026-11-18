import Langlands.GroupScheme.HomScheme.GenericReduction
import Langlands.AlgebraicGeometry.SmoothLifting.SquareZero

/-! # Scheme lifts of homomorphisms through square-zero thickenings

Let `I` be a square-zero ideal of `R`, `G` a smooth group scheme over `Spec R` (not assumed
affine) and `H` an affine group scheme over `Spec R`. Every homomorphism `f₀ : H_{R/I} ⟶ G_{R/I}`
is the base change of some morphism of schemes `s : H.X ⟶ G.X` over `Spec R` (not necessarily a
homomorphism). Also, for smooth `G`, reduction `G(A) → G(A ⧸ J)` is surjective for square-zero `J`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme

open Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}}

/-- **Surjectivity of reduction** for smooth group schemes and square-zero ideals. -/
theorem reduction_surjective (G : GroupScheme (Spec R)) [Smooth G.X.hom] {A : Type u}
    [CommRing A] [Algebra R A] (J : Ideal A) (hJ : SqZero J) :
    Function.Surjective (Lie.NonaffineKernel.reduction G J) := by
  intro p
  have hK : SqZero (RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom) := by
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker]
    exact hJ
  obtain ⟨x, hx₀, hxs⟩ := exists_lift_sqZero (f := G.X.hom)
    (CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective hK p.left
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) (by
      rw [← Spec.map_comp]
      exact Over.w p)
  exact ⟨Over.homMk x hxs, Over.OverMorphism.ext hx₀⟩

/-- **Scheme lift** of a homomorphism over `R ⧸ I` for square-zero `I`, affine source and smooth
target: some morphism `s : H.X ⟶ G.X` over `Spec R` base-changes to `f₀`. -/
theorem exists_schemeLift (I : Ideal R) [hI : Fact (SqZero I)] (H G : GroupScheme (Spec R))
    [IsAffineHom H.X.hom] [Smooth G.X.hom]
    (f₀ : (GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H ⟶
      (GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj G) :
    ∃ s : H.X ⟶ G.X, (Over.pullback (Spec.algebraMap R (R ⧸ I))).map s = f₀.hom.hom := by
  have hP := isPullback_reduction I (Lie.coordinateIso H)
  let D := Lie.coordinateAlgebra H
  let J := I.map (algebraMap R D)
  let x₀ : Spec (CommRingCat.of (D ⧸ J)) ⟶ G.X.left := hP.isoPullback.hom ≫
    f₀.hom.hom.left ≫ pullback.fst G.X.hom (Spec.algebraMap R (R ⧸ I))
  have hK : SqZero (RingHom.ker (CommRingCat.ofHom (algebraMap D (D ⧸ J))).hom) := by
    rw [CommRingCat.hom_ofHom, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact hI.out.map _
  have hw₀ : f₀.hom.hom.left ≫ pullback.snd G.X.hom (Spec.algebraMap R (R ⧸ I)) =
      pullback.snd H.X.hom (Spec.algebraMap R (R ⧸ I)) :=
    Over.w f₀.hom.hom
  have c := pullback.condition (f := G.X.hom) (g := Spec.algebraMap R (R ⧸ I))
  have hsq : x₀ ≫ G.X.hom = Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ J))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
    have e1 : x₀ ≫ G.X.hom = hP.isoPullback.hom ≫ f₀.hom.hom.left ≫
        pullback.snd G.X.hom (Spec.algebraMap R (R ⧸ I)) ≫ Spec.algebraMap R (R ⧸ I) := by
      change (hP.isoPullback.hom ≫ f₀.hom.hom.left ≫ pullback.fst G.X.hom _) ≫ G.X.hom = _
      exact ((Category.assoc _ _ _).trans (congrArg (fun k => hP.isoPullback.hom ≫ k)
        ((Category.assoc _ _ _).trans (congrArg (fun k => f₀.hom.hom.left ≫ k) c))))
    have e2 : hP.isoPullback.hom ≫ f₀.hom.hom.left ≫
        pullback.snd G.X.hom (Spec.algebraMap R (R ⧸ I)) ≫ Spec.algebraMap R (R ⧸ I) =
          hP.isoPullback.hom ≫ pullback.snd H.X.hom (Spec.algebraMap R (R ⧸ I)) ≫
            Spec.algebraMap R (R ⧸ I) :=
      congrArg (fun k => hP.isoPullback.hom ≫ k)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ Spec.algebraMap R (R ⧸ I)) hw₀))
    have e3 : hP.isoPullback.hom ≫ pullback.snd H.X.hom (Spec.algebraMap R (R ⧸ I)) ≫
        Spec.algebraMap R (R ⧸ I) =
          Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) (D ⧸ J))) ≫
            Spec.algebraMap R (R ⧸ I) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ Spec.algebraMap R (R ⧸ I)) hP.isoPullback_hom_snd)
    have e4 : Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) (D ⧸ J))) ≫
        Spec.algebraMap R (R ⧸ I) = Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ J))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
      rw [Spec.algebraMap, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
    exact e1.trans (e2.trans (e3.trans e4))
  obtain ⟨x, hx₀, hxs⟩ := exists_lift_sqZero (f := G.X.hom)
    (CommRingCat.ofHom (algebraMap D (D ⧸ J))) Ideal.Quotient.mk_surjective hK x₀
    (Spec.map (CommRingCat.ofHom (algebraMap R D))) hsq
  let s : H.X ⟶ G.X := (Lie.coordinateIso H).inv ≫ Over.homMk x hxs
  refine ⟨s, ?_⟩
  have hid : (Lie.coordinateIso H).hom.left ≫ (Lie.coordinateIso H).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hinv : (Lie.coordinateIso H).hom.left ≫ (Lie.coordinateIso H).inv.left ≫ x = x :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ x) hid).trans (Category.id_comp x))
  apply Over.OverMorphism.ext
  apply (cancel_epi hP.isoPullback.hom).mp
  apply pullback.hom_ext
  · have l1 : ((Over.pullback (Spec.algebraMap R (R ⧸ I))).map s).left ≫
        pullback.fst G.X.hom (Spec.algebraMap R (R ⧸ I)) =
          pullback.fst H.X.hom (Spec.algebraMap R (R ⧸ I)) ≫
            (Lie.coordinateIso H).inv.left ≫ x :=
      pullback.lift_fst _ _ _
    have l2 : hP.isoPullback.hom ≫ pullback.fst H.X.hom (Spec.algebraMap R (R ⧸ I)) ≫
        (Lie.coordinateIso H).inv.left ≫ x = x₀ :=
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ (Lie.coordinateIso H).inv.left ≫ x)
        hP.isoPullback_hom_fst)).trans ((Category.assoc _ _ _).trans
          ((congrArg (fun k => Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ J))) ≫ k)
            hinv).trans hx₀))
    exact ((Category.assoc _ _ _).trans ((congrArg (fun k => hP.isoPullback.hom ≫ k) l1).trans
      l2)).trans (Category.assoc _ _ _).symm
  · have l1 : ((Over.pullback (Spec.algebraMap R (R ⧸ I))).map s).left ≫
        pullback.snd G.X.hom (Spec.algebraMap R (R ⧸ I)) =
          pullback.snd H.X.hom (Spec.algebraMap R (R ⧸ I)) :=
      pullback.lift_snd _ _ _
    exact ((Category.assoc _ _ _).trans (congrArg (fun k => hP.isoPullback.hom ≫ k) l1)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => hP.isoPullback.hom ≫ k) hw₀)).symm

end Langlands.GroupScheme.HomScheme
