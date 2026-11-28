import Langlands.AlgebraicGeometry.SectionComponentLocality
import Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverProof
import Langlands.AbelianScheme.PointedProjectiveAbelianLocusStatement

/-! # Base change and locality for the pointed abelian-scheme condition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PointedProjectiveAbelianLocus

open OpenCoverStructure
open Langlands.AlgebraicGeometry

variable {S X T V : Scheme.{u}} {p : X ⟶ S} {s : S ⟶ X} {g : ℕ}

/-- The pointed condition is equivalent to the existence of an isomorphism over the
base with an abelian scheme of the prescribed dimension. Translation by the inverse of the
image of the prescribed section arranges the identity condition. -/
theorem pointed_iff_overIso (hs : s ≫ p = 𝟙 S) (t : T ⟶ S) :
    HasPointedAbelianPullback p s g t ↔
      ∃ A : AbelianScheme T, A.HasRelativeDimension g ∧
        Nonempty (A.X ≅ (Over.pullback t).obj (Over.mk p)) := by
  constructor
  · rintro ⟨A, e, hd, hp, -⟩
    exact ⟨A, hd, ⟨Over.isoMk e hp⟩⟩
  · rintro ⟨A, hd, ⟨e⟩⟩
    let q := sec (Over.mk p) (Over.homMk s hs : 𝟙_ (Over S) ⟶ Over.mk p) t
    let φ := e.symm ≪≫ GrpObj.mulRight (q ≫ e.inv)⁻¹
    have hφ : q ≫ φ.hom = η[A.X] := by
      simpa only [φ, Iso.trans_hom, Iso.symm_hom, ← Category.assoc] using
        comp_mulRight_inv A (q ≫ e.inv)
    have hη : η[A.X] ≫ φ.inv = q := by rw [← hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    refine ⟨A, (Over.forget T).mapIso φ.symm, hd, Over.w φ.inv, ?_⟩
    simpa [q, sec] using congrArg (fun f => f.left ≫ pullback.fst p t) hη

/-- The pointed condition is preserved by arbitrary change of the test scheme. -/
theorem pointed_baseChange (hs : s ≫ p = 𝟙 S) {t : T ⟶ S}
    (ht : HasPointedAbelianPullback p s g t) (v : V ⟶ T) :
    HasPointedAbelianPullback p s g (v ≫ t) := by
  obtain ⟨A, hd, ⟨e⟩⟩ := (pointed_iff_overIso hs t).mp ht
  exact (pointed_iff_overIso hs (v ≫ t)).mpr
    ⟨(AbelianScheme.baseChange v).obj A, A.hasRelativeDimension_baseChange g hd v,
      ⟨(Over.pullback v).mapIso e ≪≫ (restrictIso (Over.mk p) v t).symm⟩⟩

/-- The test condition computed in a base-changed family agrees with the condition on the
composite map to the original base. -/
theorem pointed_iterated (hs : s ≫ p = 𝟙 S) (t : T ⟶ S) (v : V ⟶ T) :
    HasPointedAbelianPullback (pullback.snd p t) (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection _ _ hs t) g v ↔
      HasPointedAbelianPullback p s g (v ≫ t) := by
  rw [pointed_iff_overIso (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection_snd _ _ hs t), pointed_iff_overIso hs]
  constructor
  · rintro ⟨A, hd, ⟨e⟩⟩
    exact ⟨A, hd, ⟨e ≪≫ (restrictIso (Over.mk p) v t).symm⟩⟩
  · rintro ⟨A, hd, ⟨e⟩⟩
    exact ⟨A, hd, ⟨e ≪≫ restrictIso (Over.mk p) v t⟩⟩

/-- An isomorphism over the base is a base change along the identity. -/
theorem baseChangeProperty_of_overIso (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Y Z : Over T} (e : Y ≅ Z) (h : P Z.hom) : P Y.hom := by
  let : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  have hpb : IsPullback e.hom.left Y.hom Z.hom (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact MorphismProperty.of_isPullback hpb h

/-- Pointed abelian-scheme structures of the same dimension glue on a cover of a test scheme. -/
theorem pointed_of_openCover (hs : s ≫ p = 𝟙 S) (t : T ⟶ S)
    (𝒰 : T.OpenCover.{u})
    (h : ∀ i, HasPointedAbelianPullback p s g (𝒰.f i ≫ t)) :
    HasPointedAbelianPullback p s g t := by
  let P := (Over.pullback t).obj (Over.mk p)
  let q := sec (Over.mk p) (Over.homMk s hs : 𝟙_ (Over S) ⟶ Over.mk p) t
  choose A hd e using fun i => (pointed_iff_overIso hs (𝒰.f i ≫ t)).mp (h i)
  let e' (i : 𝒰.I₀) : (A i).X ≅ (Over.pullback (𝒰.f i)).obj P :=
    (e i).some ≪≫ restrictIso (Over.mk p) (𝒰.f i) t
  obtain ⟨B, b, -⟩ := abelianSchemeStructureOfOpenCover T P q 𝒰
    (fun i => ⟨A i, ⟨(e' i).symm⟩⟩)
  let : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hdim : SmoothOfRelativeDimension g P.hom :=
    IsZariskiLocalAtTarget.of_openCover (P := @SmoothOfRelativeDimension.{u} g) 𝒰 fun i =>
      baseChangeProperty_of_overIso (@SmoothOfRelativeDimension.{u} g) (e' i).symm (hd i)
  refine (pointed_iff_overIso hs t).mpr ⟨B, ?_, ⟨b.symm⟩⟩
  exact baseChangeProperty_of_overIso (@SmoothOfRelativeDimension.{u} g) b.symm hdim

end Langlands.AbelianScheme.PointedProjectiveAbelianLocus
