import Langlands.Geometry.Analytic.FlatTargetDescent
import Langlands.Geometry.Analytic.AffinoidPointwiseBaseChange
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler

/-! # Reflection at prime localizations of an algebraic pushout -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.TensorStalkBaseChange

open TensorProduct
open scoped TensorProduct

variable {R : Type u} {S : Type v} {T : Type w} {D : Type z}
  [CommRing R] [CommRing S] [CommRing T] [CommRing D]
  [Algebra R S] [Algebra R T] [Algebra R D] [Algebra S D] [Algebra T D]
  [IsScalarTower R S D] [IsScalarTower R T D]
  [Algebra.IsPushout R T S D]

/-- In an actual algebraic pushout with flat horizontal structural maps,
flatness and formal unramifiedness at a target prime reflect to the
corresponding prime of the original algebra. -/
theorem etale_atPrime_reflect
    [Module.Flat R T] [Module.Flat S D]
    (p : Ideal D) [p.IsPrime]
    (hflat : Module.Flat T (Localization.AtPrime p))
    (hunr : Algebra.FormallyUnramified T (Localization.AtPrime p)) :
    Module.Flat R (Localization.AtPrime (p.comap (algebraMap S D))) ∧
      Algebra.FormallyUnramified R
        (Localization.AtPrime (p.comap (algebraMap S D))) := by
  let q := p.comap (algebraMap S D)
  let M := Localization.AtPrime q
  let L := Localization.AtPrime p
  let : Algebra M L :=
    (Localization.localRingHom q p (algebraMap S D) rfl).toAlgebra
  have : IsScalarTower S M L := .of_algebraMap_eq fun s =>
    (Localization.localRingHom_to_map q p (algebraMap S D) rfl s).symm
  have : IsScalarTower R M L := IsScalarTower.to₁₃₄ R S M L
  have hf : (algebraMap S D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Module.Flat M L := hf.localRingHom p q rfl
  have : Module.FaithfullyFlat M L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Flat T L := hflat
  have : Module.Flat R L := Module.Flat.trans R T L
  refine ⟨flat_of_faithfullyFlat_target R M L, ?_⟩
  have : Algebra.FormallyUnramified T L := hunr
  have : Subsingleton Ω[L⁄T] := inferInstance
  have : Algebra.FormallyEtale D L :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have : Algebra.FormallyEtale S M :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let eL := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale T D L
  have : Subsingleton (L ⊗[D] Ω[D⁄T]) := eL.injective.subsingleton
  let eBase := KaehlerDifferential.tensorKaehlerEquiv R T S D
  have : Subsingleton (L ⊗[D] (D ⊗[S] Ω[S⁄R])) :=
    (eBase.lTensor L).injective.subsingleton
  have : Subsingleton (L ⊗[S] Ω[S⁄R]) :=
    (AlgebraTensorModule.cancelBaseChange S D D L Ω[S⁄R]).symm.injective.subsingleton
  have : Subsingleton (L ⊗[M] (M ⊗[S] Ω[S⁄R])) :=
    (AlgebraTensorModule.cancelBaseChange S M M L Ω[S⁄R]).injective.subsingleton
  let eM := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S M
  have : Subsingleton (L ⊗[M] Ω[M⁄R]) :=
    (eM.symm.lTensor L).injective.subsingleton
  have : Subsingleton Ω[M⁄R] :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right M L
      (N := Ω[M⁄R])).mp inferInstance
  exact (Algebra.formallyUnramified_iff R M).mpr this

end Langlands.Analytic.TensorStalkBaseChange
