import Langlands.AbelianScheme.PointedAbelianArtinianLifting
import Langlands.AbelianScheme.PointedAbelianLawRepresentabilityProof
import Langlands.AbelianScheme.PointedProjectiveAbelianLocus.Geometry
import Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.AffineComparison
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.Geometry
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # The open locus of pointed abelian-scheme structures -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry PointedProjectiveAbelianLocus

variable {S X Z : Scheme.{u}}

private theorem representer_isOpenImmersion
    [IsLocallyNoetherian S] {p : X ⟶ S} {s : S ⟶ X} (hs : s ≫ p = 𝟙 S)
    {g : ℕ} [SmoothOfRelativeDimension g p] [IsProper p]
    (z : Z ⟶ S) [Mono z] [LocallyOfFinitePresentation z]
    (hZ : ∀ (T : Scheme.{u}) (t : T ⟶ S),
      (∃ f : T ⟶ Z, f ≫ z = t) ↔ HasPointedAbelianPullback p s g t) :
    IsOpenImmersion z := by
  have hArtin : ArtinianLiftingSmooth.LiftsArtinian z := by
    intro R B _ _ _ _ _ _ q hq hker α β hαβ _
    let ρ := Spec.map (CommRingCat.ofHom q)
    have hα : HasPointedAbelianPullback p s g (ρ ≫ β) :=
      (hZ _ _).mp ⟨α, hαβ⟩
    obtain ⟨A₀, e₀, -, hp₀, hη₀⟩ := (pointed_iterated hs β ρ).mpr hα
    let pβ := pullback.snd p β
    let sβ := SectionComponent.baseChangeSection p s hs β
    have hsβ : sβ ≫ pβ = 𝟙 _ := SectionComponent.baseChangeSection_snd p s hs β
    let hdimβ : SmoothOfRelativeDimension g pβ :=
      inferInstanceAs (SmoothOfRelativeDimension g (pullback.snd p β))
    obtain ⟨A, e, hp, hη⟩ := pointedAbelianArtinianLifting R B q hq hker _ pβ sβ hsβ
      (SmoothOfRelativeDimension.smooth g pβ) (inferInstanceAs (IsProper (pullback.snd p β)))
      ⟨A₀, e₀, hp₀, hη₀⟩
    let e' : A.X ≅ Over.mk pβ := Over.isoMk e hp
    have hd : A.HasRelativeDimension g :=
      baseChangeProperty_of_overIso (@SmoothOfRelativeDimension.{u} g) e' hdimβ
    have hβ : HasPointedAbelianPullback p s g β := by
      refine ⟨A, e, hd, hp, ?_⟩
      simpa [sβ, SectionComponent.baseChangeSection] using
        congrArg (· ≫ pullback.fst p β) hη
    obtain ⟨γ, hγ⟩ := (hZ _ _).mpr hβ
    refine ⟨γ, hγ, (cancel_mono z).mp ?_⟩
    rw [Category.assoc, hγ, hαβ]
  let : Smooth z := ArtinianLiftingSmooth.smooth_of_liftsArtinian z hArtin
  exact IsOpenImmersion.of_flat_of_mono z

private theorem hProjective_of_projective_baseChange
    {m : ℕ} (i : X ⟶ RelativeProjectiveSpace S m) [IsClosedImmersion i]
    (R : CommRingCat.{u}) (j : Spec R ⟶ S) :
    IsHProjective (pullback.snd (i ≫ RelativeProjectiveSpace.toBase S m) j) := by
  let f := RelativeProjectiveSpace.toBase S m
  let e := (pullbackRightPullbackFstIso f j i).inv
  let a := pullback.snd i (pullback.fst f j)
  let b := (pullbackSymmetry f j).hom
  let c := (RelativeProjectiveSpace.baseChangeIso m j).inv
  let d := (RelativeProjectiveSpace.affineComparisonIso R m).inv
  let : IsIso e := inferInstanceAs (IsIso (pullbackRightPullbackFstIso f j i).inv)
  let : IsClosedImmersion a := inferInstanceAs (IsClosedImmersion (pullback.snd i (pullback.fst f j)))
  let : IsIso b := inferInstanceAs (IsIso (pullbackSymmetry f j).hom)
  let : IsIso c := inferInstanceAs (IsIso (RelativeProjectiveSpace.baseChangeIso m j).inv)
  let : IsIso d := inferInstanceAs (IsIso (RelativeProjectiveSpace.affineComparisonIso R m).inv)
  refine ⟨m, e ≫ a ≫ b ≫ c ≫ d, inferInstance, ?_⟩
  simp [e, a, b, c, d, f]

/-- The locus of abelian-scheme structures of fixed relative dimension and prescribed
identity section is open in the base of the flat projective family. -/
theorem pointedProjectiveAbelianLocus : PointedProjectiveAbelianLocusStatement.{u} := by
  intro S X hS m g i hi s p hs hflat hlfp
  let : IsProper p := inferInstanceAs (IsProper (i ≫ RelativeProjectiveSpace.toBase S m))
  let J : Type u := {V : S.Opens // HasPointedAbelianPullback p s g V.ι}
  let U : S.Opens := ⨆ j : J, j.1
  refine ⟨U, ?_⟩
  intro T _ t
  constructor
  · intro ht
    let V : J → T.Opens := fun j => t ⁻¹ᵁ j.1
    have hV : IsOpenCover V := by
      apply top_unique
      intro x _
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (ht ⟨x, rfl⟩)
      exact Opens.mem_iSup.mpr ⟨j, hj⟩
    let 𝒰 := T.openCoverOfIsOpenCover V hV
    apply pointed_of_openCover hs t 𝒰
    intro j
    let v := t ∣_ j.1
    have hv : v ≫ j.1.ι = 𝒰.f j ≫ t := morphismRestrict_ι t j.1
    rw [← hv]
    exact pointed_baseChange hs j.2 v
  · intro ht
    rintro _ ⟨x, rfl⟩
    let tₓ := T.fromSpecResidueField x ≫ t
    have htx : HasPointedAbelianPullback p s g tₓ :=
      pointed_baseChange hs ht (T.fromSpecResidueField x)
    obtain ⟨R, hR, j, a, hj, ha, hdim, hconn⟩ := exists_affine_geometry hs tₓ htx
    let q := pullback.snd p j
    let sec := SectionComponent.baseChangeSection p s hs j
    have hsec := SectionComponent.baseChangeSection_snd p s hs j
    have hq : IsHProjective q := hProjective_of_projective_baseChange i R j
    obtain ⟨Z, z, hz, hfp, hZ⟩ := pointedAbelianLawRepresentability R _ q sec g hsec hq hdim hconn
    let : IsProper q := IsHProjective.isProper hq
    let : IsOpenImmersion z := representer_isOpenImmersion hsec z hZ
    let w := z ≫ j
    let : IsOpenImmersion w := inferInstanceAs (IsOpenImmersion (z ≫ j))
    have hw : HasPointedAbelianPullback p s g w :=
      (pointed_iterated hs j z).mp ((hZ Z z).mp ⟨𝟙 Z, Category.id_comp z⟩)
    have hW : HasPointedAbelianPullback p s g w.opensRange.ι := by
      simpa only [Scheme.Hom.isoOpensRange_inv_comp] using
        pointed_baseChange hs hw w.isoOpensRange.inv
    obtain ⟨b, hb⟩ := (hZ _ a).mpr ((pointed_iterated hs j a).mpr (by rw [ha]; exact htx))
    have hbcomp : b ≫ w = tₓ := by
      change b ≫ z ≫ j = tₓ
      rw [← Category.assoc, hb, ha]
    let x₀ : ↥(Spec (T.residueField x)) := IsLocalRing.closedPoint (T.residueField x)
    refine Opens.mem_iSup.mpr ⟨⟨w.opensRange, hW⟩, ?_⟩
    refine ⟨b x₀, ?_⟩
    calc
      w (b x₀) = (b ≫ w) x₀ := rfl
      _ = tₓ x₀ := congrArg (fun a : Spec (T.residueField x) ⟶ S => a x₀) hbcomp
      _ = t x := congrArg t (Scheme.fromSpecResidueField_apply x x₀)

end Langlands.AbelianScheme
