import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFinitePresentationBaseChange
import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomCartesian
import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomDescent
import Langlands.AlgebraicGeometry.CoherentSheaves.NoetherianHomFiniteLinearModelsStatement
import Langlands.AlgebraicGeometry.CoherentSheaves.ProperHomRepresentabilityStatement
import Langlands.AlgebraicGeometry.FiniteLinearModelGluing
import Langlands.AlgebraicGeometry.Modules.FinitePresentationPullback
import Langlands.AlgebraicGeometry.Modules.ProperAffineNoetherianModelExistenceStatement
import Langlands.AlgebraicGeometry.Modules.RelativeFlatnessPullback

/-! # Proper Hom representation from two explicit geometric inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

/-- Local finite equations and actual Hom descent give a representative over
a noetherian affine base. The geometric local-model statement is a premise. -/
theorem intrinsicHom_representable_noetherian
    (hNoeth : NoetherianHomFiniteLinearModelsStatement.{u})
    (R : CommRingCat.{u}) (hR : IsNoetherianRing R)
    (Y : Scheme.{u}) (p : Y ⟶ Spec R)
    (hp : IsProper p) (hfp : LocallyOfFinitePresentation p)
    (M N : Y.Modules) (hM : M.IsFinitePresentation) (hN : N.IsFinitePresentation)
    (hFlat : Modules.IsFlatOver p N) :
    AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (intrinsicModuleHomPresheaf p M N) := by
  let : N.IsFinitePresentation := hN
  exact (hNoeth R hR Y p hp hfp M N hM hN hFlat).exists_affine_representation
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_intrinsicModuleHomPresheaf_fppf p M N))

/-- An actual noetherian model transfers a representation to an arbitrary
affine base. Both geometric input statements remain explicit premises. -/
theorem intrinsicHom_representable_affine
    (hNoeth : NoetherianHomFiniteLinearModelsStatement.{u})
    (hApprox : Modules.ProperAffineNoetherianModelExistenceStatement.{u})
    (R : CommRingCat.{u}) (Y : Scheme.{u}) (p : Y ⟶ Spec R)
    (hp : IsProper p) (hfp : LocallyOfFinitePresentation p)
    (M N : Y.Modules) (hM : M.IsFinitePresentation) (hN : N.IsFinitePresentation)
    (hFlat : Modules.IsFlatOver p N) :
    AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (intrinsicModuleHomPresheaf p M N) := by
  obtain ⟨R₀, hR₀, φ, Y₀, p₀, q, M₀, N₀, hp₀, hfp₀, hM₀, hN₀,
    hFlat₀, hCart, ⟨eM⟩, ⟨eN⟩⟩ :=
      hApprox R Y p hp hfp M N hM hN hFlat
  exact ((intrinsicHom_representable_noetherian hNoeth R₀ hR₀ Y₀ p₀ hp₀ hfp₀
    M₀ N₀ hM₀ hN₀ hFlat₀).baseChange (Spec.map φ)).of_iso
      (intrinsicModuleHomCartesianOfIso hCart eM eN)

/-- Affine open charts and full-slice gluing extend the conditional
representation theorem to every base scheme. -/
theorem intrinsicHom_representable
    (hNoeth : NoetherianHomFiniteLinearModelsStatement.{u})
    (hApprox : Modules.ProperAffineNoetherianModelExistenceStatement.{u})
    (B Y : Scheme.{u}) (p : Y ⟶ B)
    (hp : IsProper p) (hfp : LocallyOfFinitePresentation p)
    (M N : Y.Modules) (hM : M.IsFinitePresentation) (hN : N.IsFinitePresentation)
    (hFlat : Modules.IsFlatOver p N) :
    AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (intrinsicModuleHomPresheaf p M N) := by
  let : M.IsFinitePresentation := hM
  let : N.IsFinitePresentation := hN
  let 𝒰 := B.affineOpenCover
  have hLocal : ∀ i : 𝒰.I₀,
      AlgebraicSpace.IsAffineFinitePresentationRepresentable
        ((Over.map (𝒰.f i)).op ⋙ intrinsicModuleHomPresheaf p M N) := by
    intro i
    have hpi : IsProper (pullback.fst (𝒰.f i) p) :=
      MorphismProperty.pullback_fst _ _ hp
    have hfpi : LocallyOfFinitePresentation (pullback.fst (𝒰.f i) p) :=
      MorphismProperty.pullback_fst _ _ hfp
    exact (intrinsicHom_representable_affine hNoeth hApprox (𝒰.X i)
      (pullback (𝒰.f i) p) (pullback.fst (𝒰.f i) p) hpi hfpi
      ((Scheme.Modules.pullback (pullback.snd (𝒰.f i) p)).obj M)
      ((Scheme.Modules.pullback (pullback.snd (𝒰.f i) p)).obj N)
      (Modules.isFinitePresentation_pullback _ M)
      (Modules.isFinitePresentation_pullback _ N)
      (Modules.isFlatOver_pullback_of_isPullback
        (IsPullback.of_hasPullback (𝒰.f i) p).flip N hFlat)).of_iso
          (intrinsicModuleHomBaseChangeIso p (𝒰.f i) M N).symm
  choose H he hAffine hFP using hLocal
  exact AlgebraicSpace.LocalRepresentation.exists_affine_representation
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_intrinsicModuleHomPresheaf_fppf p M N))
    𝒰.openCover H (fun i ↦ (he i).some) hAffine hFP

/-- The two explicit geometric inputs imply the exact actual-family
proper-Hom representability proposition on every scheme slice. -/
theorem properHomRepresentability_of_geometricInputs
    (hNoeth : NoetherianHomFiniteLinearModelsStatement.{u})
    (hApprox : Modules.ProperAffineNoetherianModelExistenceStatement.{u}) :
    ProperHomRepresentabilityStatement.{u} := by
  intro S X f hf hfp T M N
  have hp : IsProper ((Picard.relativeProjection f).app T) :=
    MorphismProperty.pullback_fst _ _ hf
  have hfp' : LocallyOfFinitePresentation ((Picard.relativeProjection f).app T) :=
    MorphismProperty.pullback_fst _ _ hfp
  exact (intrinsicHom_representable hNoeth hApprox T.left
    ((Picard.relativeSpace f).obj T) ((Picard.relativeProjection f).app T)
    hp hfp' M.of.obj N.of.obj inferInstance inferInstance
    (FamilyGroupoid.isFlatOver f T N)).of_iso
      (FamilyGroupoid.homPresheafIntrinsicIso f T M N).symm

/-- Choose an actual affine finitely presented representation, its full
natural comparison, and its map properties, from the two geometric inputs. -/
def properHomRepresentationOfGeometricInputs
    (hNoeth : NoetherianHomFiniteLinearModelsStatement.{u})
    (hApprox : Modules.ProperAffineNoetherianModelExistenceStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hf : IsProper f) (hfp : LocallyOfFinitePresentation f)
    (T : Over S) (M N : FamilyGroupoid f T) :
    Σ H : Over T.left,
      { _e : (AlgebraicSpace.schemeYoneda T.left).obj H ≅
          FamilyGroupoid.homPresheaf f M N //
        IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom } :=
  let h := properHomRepresentability_of_geometricInputs hNoeth hApprox S X f hf hfp T M N
  ⟨h.choose, h.choose_spec.1.some, h.choose_spec.2⟩

end Langlands.AlgebraicGeometry.CoherentSheaves
