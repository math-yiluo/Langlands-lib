import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf
import Langlands.AlgebraicGeometry.Picard.TwoAxisCarrierIsoAbelian
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealLocalFreeness
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement

/-! # The two-axis class presheaf has small values (Murre's condition `SmallValues`) -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace LineBundle

/-- Unit cocycle data indexed by the points of a scheme: an open set for every point and a
unit on every pairwise intersection. This type lives in `Type u`. -/
abbrev PointCocycleData (Z : Scheme.{u}) : Type u :=
  Σ T : Z → Z.Opens, ∀ i j : Z, (Γ(Z, T i ⊓ T j))ˣ

/-- The isomorphism class of the module sheaf glued from point-indexed cocycle data. -/
def gluedModuleClass (Z : Scheme.{u}) (d : PointCocycleData Z) :
    Quotient (isIsomorphicSetoid Z.Modules) :=
  Quotient.mk _ (CocycleGluing.glued d.2)

/-- Every locally free sheaf of rank one is isomorphic to a module sheaf glued from
point-indexed cocycle data. -/
lemma exists_gluedModuleClass_eq {Z : Scheme.{u}} {M : Z.Modules}
    (hM : IsLocallyFreeRankOne M) :
    ∃ d : PointCocycleData Z, gluedModuleClass Z d = Quotient.mk _ M := by
  choose T hxT e he using OpenImmersionIdeal.exists_isFrameOn_of_isLocallyFreeRankOne hM
  have hT : (⨆ x, T x) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxT x⟩
  refine ⟨⟨T, CocycleGluing.frameCocycle e he⟩, ?_⟩
  exact Quotient.sound
    ⟨(CocycleGluing.frameIso he (CocycleGluing.isTransition_frameCocycle he) hT).symm⟩

/-- The isomorphism classes of module sheaves that contain a line bundle form a `u`-small set. -/
lemma small_lineBundleModuleClasses (Z : Scheme.{u}) :
    Small.{u} {c : Quotient (isIsomorphicSetoid Z.Modules) //
      ∃ M : Z.Modules, IsLocallyFreeRankOne M ∧ c = Quotient.mk _ M} := by
  have hsub : ∀ c : {c : Quotient (isIsomorphicSetoid Z.Modules) //
      ∃ M : Z.Modules, IsLocallyFreeRankOne M ∧ c = Quotient.mk _ M},
      c.1 ∈ Set.range (gluedModuleClass Z) := by
    rintro ⟨c, M, hM, rfl⟩
    exact exists_gluedModuleClass_eq hM
  exact small_of_injective (f := fun c ↦ (⟨c.1, hsub c⟩ : Set.range (gluedModuleClass Z)))
    (fun a b hab ↦ Subtype.ext (by have h := congrArg Subtype.val hab; exact h))

end LineBundle

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- The isomorphism classes of two-axis-rigidified line bundles on the self-product of an
abelian scheme form a `u`-small type. -/
lemma small_isoClasses :
    Small.{u} (Quotient (isIsomorphicSetoid (TwoAxisRigidifiedLineBundle (unitSection A)
      (unitSection A) (mumfordSection A) (twoAxisSecond A) (twoAxis_unit_comp A)))) := by
  let Z := (mumfordProduct A).left
  let φ : Quotient (isIsomorphicSetoid (TwoAxisRigidifiedLineBundle (unitSection A)
      (unitSection A) (mumfordSection A) (twoAxisSecond A) (twoAxis_unit_comp A))) →
      {c : Quotient (isIsomorphicSetoid Z.Modules) //
        ∃ M : Z.Modules, IsLocallyFreeRankOne M ∧ c = Quotient.mk _ M} :=
    Quotient.lift (fun L ↦ ⟨Quotient.mk _ L.obj.carrier, L.obj.carrier, L.property, rfl⟩)
      (fun L M ⟨f⟩ ↦ Subtype.ext (Quotient.sound
        ⟨(TwoAxisRigidifiedModule.forget _ _ _ _ _).mapIso
          ((ObjectProperty.ι _).mapIso f)⟩))
  have hφ : Function.Injective φ := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | h L =>
    induction b using Quotient.inductionOn with
    | h M =>
    obtain ⟨f⟩ := Quotient.exact (congrArg Subtype.val hab)
    exact Quotient.sound (nonempty_iso_of_carrierIso A f)
  have := LineBundle.small_lineBundleModuleClasses Z
  exact small_of_injective hφ

/-- Every value of the two-axis class presheaf is `u`-small. -/
lemma small_classPresheaf_obj (T : Over S) :
    Small.{u} ((classPresheaf A).obj (Opposite.op T)) :=
  small_isoClasses (TwoAxisFamily.abelian A T)

end TwoAxisRigidifiedLineBundle

/-- Murre's condition `SmallValues` for the two-axis class presheaf: for every abelian scheme `A`
over the spectrum of a noetherian ring, every value of `TwoAxisRigidifiedLineBundle.classPresheaf A`
is `u`-small. -/
theorem noetherianTwoAxisClassSmallValues : NoetherianTwoAxisClassSmallValuesStatement.{u} :=
  fun _ _ _ A T ↦ TwoAxisRigidifiedLineBundle.small_classPresheaf_obj A T

end Langlands.AlgebraicGeometry.Picard
