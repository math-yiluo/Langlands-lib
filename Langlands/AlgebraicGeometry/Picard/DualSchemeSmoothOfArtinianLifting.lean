import Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianLiftingStatement
import Langlands.AlgebraicGeometry.Picard.DualSchemeSubalgebraFactorization
import Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
import Mathlib.RingTheory.FiniteType

/-! # Smoothness of the chosen dual from Artinian lifting of Picard-zero families -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

/-- If geometric Picard-zero rigidified families lift along elementary Artinian
thickenings, then the chosen dual of an abelian scheme over a noetherian affine base is
smooth. -/
theorem dualScheme_smooth_of_picardZeroArtinianLifting
    (lifting : PicardZeroArtinianLiftingStatement.{u}) {R : Type u} [CommRing R]
    [IsNoetherianRing R] (A : AbelianScheme (Spec (CommRingCat.of R)))
    (hA : HasDualScheme A) : Smooth (dualScheme A hA).hom := by
  have : LocallyOfFiniteType (dualScheme A hA).hom := dualScheme_locallyOfFiniteType A hA
  apply ArtinianLiftingSmooth.smooth_of_liftsArtinian
  intro B' B _ _ _ _ _ _ φ hφ hel α β hαβ _
  let ι : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  let a : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ dualScheme A hA :=
    Over.homMk α hαβ
  let M := (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
    (unitSection_comp A) a).obj (poincareFamily A hA)
  have hM : IsPicardZeroFamily A M :=
    picardZeroPullback _ A _ _ a _ (poincareFamily_universal A hA).1
  obtain ⟨M', hM', ⟨e⟩⟩ := lifting _ A B' B φ hφ hel β M hM
  let c := dualClassify A hA (Over.mk β)
    ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) M', hM'⟩
  have ha : a = dualClassify A hA _ ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A)
      (unitSection_comp A) M, hM⟩ :=
    dualClassify_unique A hA _ _ a rfl
  have hc : ι ≫ c = a := by
    rw [ha, ← dualClassify_pullback A Langlands.SchemeModule.RigidifiedModule.pullbackCoherence
      picardZeroPullback hA]
    congr 1
    exact Subtype.ext (Quotient.sound ⟨e⟩)
  exact ⟨c.left, Over.w c, congrArg CommaMorphism.left hc⟩

/-- If geometric Picard-zero rigidified families lift along elementary Artinian
thickenings, then the chosen dual of an abelian scheme over `Spec R`, for `R` of finite type
over `ℤ`, is smooth. -/
theorem finiteType_dualScheme_smooth_of_picardZeroArtinianLifting
    (lifting : PicardZeroArtinianLiftingStatement.{u}) (R : Type u) [CommRing R]
    [Algebra.FiniteType ℤ R] (A : AbelianScheme (Spec (CommRingCat.of R)))
    (hA : HasDualScheme A) : Smooth (dualScheme A hA).hom := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  exact dualScheme_smooth_of_picardZeroArtinianLifting lifting A hA

end Langlands.AbelianScheme
