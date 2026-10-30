import Langlands.AlgebraicGeometry.Picard.PicardZeroQuasiSeparatedExtensionStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Mathlib.AlgebraicGeometry.Gluing

/-! # Extending the Picard-zero classification from quasi-separated tests -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} (A : AbelianScheme S)

private lemma classesPullback_comp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V)
    (q : RigidifiedClasses A V) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        h (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
          (unitSection_comp A) k q) =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (h ≫ k) q := by
  exact (congrArg (fun m ↦ m q) ((RigidifiedLineBundle.classPresheaf
    RigidifiedModule.pullbackCoherence A.X.hom (unitSection A)
    (unitSection_comp A)).map_comp k.op h.op)).symm

private lemma classifyingMap_comp {P T U : Over S} (L : RigidifiedFamily A P)
    (h : T ⟶ U) (k : U ⟶ P) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
        (unitSection_comp A) L T (h ≫ k) =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        h (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
          (unitSection_comp A) L U k) :=
  RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A)
    (unitSection_comp A) RigidifiedModule.pullbackCoherence L h k

/-- Restricted uniqueness compares parameter maps on any quasi-separated common test. -/
private lemma local_parameter_maps_agree {P T U V W : Over S}
    [QuasiSeparatedSpace W.left] (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZeroOnQuasiSeparatedTests A L) (q : PicardZeroClasses A T)
    (f : U ⟶ T) (g : V ⟶ T) (a : U ⟶ P) (b : V ⟶ P)
    (ha : RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
      (unitSection_comp A) L U a =
      (picardZeroClassesPullback picardZeroPullback A f q).val)
    (hb : RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
      (unitSection_comp A) L V b =
      (picardZeroClassesPullback picardZeroPullback A g q).val)
    (r : W ⟶ U) (s : W ⟶ V) (comm : r ≫ f = s ≫ g) :
    r ≫ a = s ≫ b := by
  obtain ⟨c, hc, hu⟩ := hL.2 W
    (picardZeroClassesPullback picardZeroPullback A (r ≫ f) q)
  have hra : RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
      (unitSection_comp A) L W (r ≫ a) =
      (picardZeroClassesPullback picardZeroPullback A (r ≫ f) q).val := by
    rw [classifyingMap_comp A, ha]
    exact classesPullback_comp A r f q.val
  have hsb : RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
      (unitSection_comp A) L W (s ≫ b) =
      (picardZeroClassesPullback picardZeroPullback A (r ≫ f) q).val := by
    rw [classifyingMap_comp A, hb]
    change RigidifiedLineBundle.classesPullback _ _ _ s
      (RigidifiedLineBundle.classesPullback _ _ _ g q.val) =
        RigidifiedLineBundle.classesPullback _ _ _ (r ≫ f) q.val
    rw [classesPullback_comp A, comm]
  exact (hu _ hra).trans (hu _ hsb).symm

/-- Parameter maps glue uniquely over a cover whose members are quasi-separated. -/
private lemma existsUnique_parameter_map_on_cover {P T : Over S}
    (L : RigidifiedFamily A P)
    (hL : IsUniversalPicardZeroOnQuasiSeparatedTests A L) (q : PicardZeroClasses A T)
    (𝒰 : T.left.OpenCover.{u}) [∀ i, QuasiSeparatedSpace (𝒰.X i)] :
    ∃! h : T ⟶ P, ∀ i,
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)
        (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
          (unitSection_comp A) L T h) =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) q.val := by
  let V : 𝒰.I₀ → Over S := fun i ↦ Over.mk (𝒰.f i ≫ T.hom)
  let j : ∀ i, V i ⟶ T := fun i ↦ Over.homMk (𝒰.f i)
  have (i : 𝒰.I₀) : QuasiSeparatedSpace (V i).left :=
    inferInstanceAs (QuasiSeparatedSpace (𝒰.X i))
  choose a ha hu using fun i ↦ hL.2 (V i)
    (picardZeroClassesPullback picardZeroPullback A (j i) q)
  have compatible (i k : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f k) ≫ (a i).left =
        pullback.snd (𝒰.f i) (𝒰.f k) ≫ (a k).left := by
    let W : Over S := Over.mk (pullback.fst (𝒰.f i) (𝒰.f k) ≫ (𝒰.f i ≫ T.hom))
    let r : W ⟶ V i := Over.homMk (pullback.fst (𝒰.f i) (𝒰.f k))
    let s : W ⟶ V k := Over.homMk (pullback.snd (𝒰.f i) (𝒰.f k))
      (by dsimp [W, V]; exact (pullback.condition_assoc T.hom).symm)
    let : QuasiSeparatedSpace W.left :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (𝒰.f i) (𝒰.f k))
    have comm : r ≫ j i = s ≫ j k := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    exact congrArg (fun m ↦ m.left)
      (local_parameter_maps_agree A L hL q (j i) (j k) (a i) (a k)
        (ha i) (ha k) r s comm)
  let b : T.left ⟶ P.left := 𝒰.glueMorphisms (fun i ↦ (a i).left) compatible
  have wb : b ≫ P.hom = T.hom := by
    apply 𝒰.hom_ext
    intro i
    dsimp [b]
    rw [𝒰.ι_glueMorphisms_assoc]
    exact (a i).w
  let h : T ⟶ P := Over.homMk b wb
  have jh (i : 𝒰.I₀) : j i ≫ h = a i := by
    apply Over.OverMorphism.ext
    exact 𝒰.ι_glueMorphisms _ compatible i
  refine ⟨h, ?_, ?_⟩
  · intro i
    change RigidifiedLineBundle.classesPullback _ _ _ (j i)
      (RigidifiedLineBundle.classifyingMap _ _ _ L T h) = _
    rw [← classifyingMap_comp A, jh i]
    exact ha i
  · intro k hk
    apply Over.OverMorphism.ext
    apply 𝒰.hom_ext
    intro i
    have jk : j i ≫ k = a i := by
      apply hu i
      rw [classifyingMap_comp A]
      exact hk i
    exact (congrArg (fun m ↦ m.left) jk).trans
      (congrArg (fun m ↦ m.left) (jh i)).symm

/-- A Picard-zero family classifying quasi-separated tests classifies every test. -/
theorem picardZeroQuasiSeparatedExtension :
    PicardZeroQuasiSeparatedExtensionStatement.{u} := by
  intro S _ A P L hL
  refine ⟨hL.1, ?_⟩
  intro T q
  obtain ⟨h, hh, hu⟩ := existsUnique_parameter_map_on_cover A L hL q T.left.affineCover
  refine ⟨h, rigidifiedClassesZariskiSeparated S A T T.left.affineCover _ _ hh, ?_⟩
  intro k hk
  apply hu k
  intro i
  rw [hk]

end Langlands.AbelianScheme
