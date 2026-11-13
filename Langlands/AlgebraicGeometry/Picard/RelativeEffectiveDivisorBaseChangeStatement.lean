import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # Arbitrary base change of relative effective Cartier divisors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

namespace RelativeEffectiveDivisorBaseChange

variable {S X T : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (g : T ⟶ S)

/-- The actual subscheme of the pulled-back ideal is the base change of the
original closed subscheme over the specified base. -/
def subschemeIso :
    (I.comap (pullback.snd g f)).subscheme ≅ pullback g (I.subschemeι ≫ f) :=
  I.comapIso (pullback.snd g f) ≪≫ pullbackLeftPullbackSndIso g f I.subschemeι

@[reassoc (attr := simp)]
lemma subschemeIso_hom_fst :
    (subschemeIso f I g).hom ≫ pullback.fst g (I.subschemeι ≫ f) =
      (I.comap (pullback.snd g f)).subschemeι ≫ pullback.fst g f := by
  simp [subschemeIso]

/-- Flatness of the closed subscheme over the base survives arbitrary base change;
no flatness of the ambient scheme or of the base-change map is required. -/
lemma flat_toBase [Flat (I.subschemeι ≫ f)] :
    Flat ((I.comap (pullback.snd g f)).subschemeι ≫ pullback.fst g f) := by
  rw [← subschemeIso_hom_fst f I g]
  infer_instance

/-- An actual ideal-kernel pullback isomorphism gives the effective Cartier
condition on the pullback ideal. -/
lemma isRelativeEffectiveCartierIdeal_of_kernelIso
    (hI : IsRelativeEffectiveCartierIdeal f I)
    (e : (Scheme.Modules.pullback (pullback.snd g f)).obj
        (StructureKernelModule.kernelModule I.subschemeι) ≅
      StructureKernelModule.kernelModule (I.comap (pullback.snd g f)).subschemeι) :
    IsRelativeEffectiveCartierIdeal (pullback.fst g f)
      (I.comap (pullback.snd g f)) := by
  have : Flat (I.subschemeι ≫ f) := hI.2
  exact ⟨(hI.1.pullback (pullback.snd g f)).of_iso e, flat_toBase f I g⟩

end RelativeEffectiveDivisorBaseChange

/-- Relative effective Cartier divisors survive every base change, and their
actual ideal kernels are identified by an isomorphism commuting with the actual
inclusions into the structure modules. -/
def RelativeEffectiveDivisorBaseChangeStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S) (I : X.IdealSheafData),
    IsRelativeEffectiveCartierIdeal f I →
      ∀ (T : Scheme.{u}) (g : T ⟶ S),
        IsRelativeEffectiveCartierIdeal (pullback.fst g f)
          (I.comap (pullback.snd g f)) ∧
        ∃ e : (Scheme.Modules.pullback (pullback.snd g f)).obj
              (StructureKernelModule.kernelModule I.subschemeι) ≅
            StructureKernelModule.kernelModule
              (I.comap (pullback.snd g f)).subschemeι,
          e.hom ≫ StructureKernelModule.kernelModuleι
              (I.comap (pullback.snd g f)).subschemeι =
            (Scheme.Modules.pullback (pullback.snd g f)).map
                (StructureKernelModule.kernelModuleι I.subschemeι) ≫
              (Langlands.Scheme.Modules.pullbackUnitIso (pullback.snd g f)).hom

end Langlands.AlgebraicGeometry.Picard
