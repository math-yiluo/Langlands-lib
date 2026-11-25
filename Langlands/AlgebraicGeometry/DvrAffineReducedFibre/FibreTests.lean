import Langlands.AlgebraicGeometry.PotentialGeometricReduction
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.BaseChange

/-! # Field tests for the affine reduced fibre theorem -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

private theorem smooth_tensor_of_injective {R A F : Type u} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Field F] [Algebra R F]
    [Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A)]
    (hF : Function.Injective (algebraMap R F)) : Algebra.Smooth F (F ⊗[R] A) := by
  let e : FractionRing R →ₐ[R] F := IsFractionRing.liftAlgHom (g := Algebra.ofId R F) hF
  let : Algebra (FractionRing R) F := e.toRingHom.toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq
    fun r => (e.commutes r).symm
  exact Algebra.Smooth.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (FractionRing R) F F A)

section Generic

variable {R S A : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
  [CommRing A] [Algebra R A] [Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A)]

/-- Smoothness of the generic fibre survives injective change of the base domain. -/
theorem smooth_genericFibre_baseChange (hS : Function.Injective (algebraMap R S)) :
    Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] (S ⊗[R] A)) := by
  have hK : Function.Injective (algebraMap R (FractionRing S)) := by
    rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
    exact (IsFractionRing.injective S (FractionRing S)).comp hS
  have : Algebra.Smooth (FractionRing S) (FractionRing S ⊗[R] A) :=
    smooth_tensor_of_injective hK
  exact Algebra.Smooth.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R S (FractionRing S) (FractionRing S) A).symm

end Generic

section IntegralClosure

variable (S D : Type u) [CommRing S] [CommRing D] [Algebra S D]

local notation "K" => FractionRing S
local notation "G" => D ⊗[S] K
local notation "N" => integralClosure D G
local notation "S₀" => nonZeroDivisors S

/-- Inverting the nonzero scalars in the integral closure in the generic fibre recovers
that generic fibre. -/
theorem isLocalization_integralClosure_genericFibre :
    IsLocalization (Algebra.algebraMapSubmonoid N S₀) G := by
  have : IsLocalization (Algebra.algebraMapSubmonoid D S₀) G := IsLocalization.tensor K S₀
  have : IsScalarTower S N G := Subalgebra.isScalarTower_mid (S := N)
  refine (isLocalization_iff (Algebra.algebraMapSubmonoid N S₀) G).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [← IsScalarTower.algebraMap_apply S N G, IsScalarTower.algebraMap_apply S D G]
    exact IsLocalization.map_units (M := Algebra.algebraMapSubmonoid D S₀) G
      ⟨algebraMap S D m, Algebra.mem_algebraMapSubmonoid_of_mem ⟨m, hm⟩⟩
  · intro z
    obtain ⟨⟨x, ⟨_, m, hm, rfl⟩⟩, hx⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid D S₀) z
    refine ⟨⟨algebraMap D N x,
      ⟨algebraMap S N m, Algebra.mem_algebraMapSubmonoid_of_mem ⟨m, hm⟩⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply] using hx
  · intro x y hxy
    exact ⟨⟨1, Submonoid.one_mem _⟩, by simpa using Subtype.ext hxy⟩

/-- The fraction-field base change of the integral closure is isomorphic over the fraction field
to the generic fibre of the original algebra. -/
def integralClosureGenericFibreEquiv : K ⊗[S] N ≃ₐ[K] K ⊗[S] D := by
  have : IsLocalization (Algebra.algebraMapSubmonoid N S₀) G :=
    isLocalization_integralClosure_genericFibre S D
  letI : Algebra K G := Algebra.TensorProduct.rightAlgebra
  letI : Algebra N (K ⊗[S] N) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid N S₀) (K ⊗[S] N) :=
    IsLocalization.tensorRight K S₀
  let e : K ⊗[S] N ≃ₐ[N] G :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid N S₀) (K ⊗[S] N) G
  have he : e.toRingHom.comp (algebraMap K (K ⊗[S] N)) = algebraMap K G := by
    have : IsScalarTower S N G := Subalgebra.isScalarTower_mid (S := N)
    apply IsLocalization.ringHom_ext S₀
    ext s
    change e (algebraMap K (K ⊗[S] N) (algebraMap S K s)) =
      algebraMap K G (algebraMap S K s)
    rw [← IsScalarTower.algebraMap_apply S K (K ⊗[S] N),
      IsScalarTower.algebraMap_apply S N (K ⊗[S] N), e.commutes,
      ← IsScalarTower.algebraMap_apply S N G, ← IsScalarTower.algebraMap_apply S K G]
  let eK : K ⊗[S] N ≃ₐ[K] G :=
    { e.toRingEquiv with commutes' := fun k => RingHom.congr_fun he k }
  exact eK.trans
    { (Algebra.TensorProduct.comm S D K).toRingEquiv with
      commutes' := fun k => Algebra.TensorProduct.comm_tmul S 1 k }

/-- Over a field reached through the generic point, normalization in a smooth generic fibre
has reduced base change. -/
theorem isReduced_tensor_integralClosure_of_injective [IsDomain S]
    {F : Type u} [Field F] [Algebra S F]
    [Algebra.Smooth K (K ⊗[S] D)] (hF : Function.Injective (algebraMap S F)) :
    IsReduced (F ⊗[S] N) := by
  have : Algebra.Smooth K (K ⊗[S] N) :=
    Algebra.Smooth.of_equiv (integralClosureGenericFibreEquiv S D).symm
  have : Algebra.Smooth F (F ⊗[S] N) := smooth_tensor_of_injective (A := N) hF
  exact SmoothReducedProof.isReduced_of_smooth_of_domain F (F ⊗[S] N)

end IntegralClosure

section Special

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

/-- For a finite-type algebra over a field, a reduced base change to one perfect field
extension implies reduced base change to every field extension. -/
theorem isReduced_tensor_of_isReduced_tensor_perfect {E F : Type u} [Field E] [Field F]
    [PerfectField E] [Algebra k E] [Algebra k F] (hE : IsReduced (E ⊗[k] B)) :
    IsReduced (F ⊗[k] B) := by
  let f := Spec.algebraMap k B
  have : LocallyOfFiniteType f :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hE' : IsReduced (B ⊗[k] E) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k B E).toRingHom
      (Algebra.TensorProduct.comm k B E).injective
  have : AlgebraicGeometry.IsReduced (pullback f (Spec.algebraMap k E)) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k B E).hom
  have : GeometricallyReduced f :=
    PotentialGeometricReduction.geometricallyReduced_of_isReduced_pullback (M := E) f
  have : AlgebraicGeometry.IsReduced (pullback f (Spec.algebraMap k F)) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  have : AlgebraicGeometry.IsReduced (Spec (.of (B ⊗[k] F))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k B F).inv
  have : IsReduced (B ⊗[k] F) := (affine_isReduced_iff _).mp ‹_›
  exact isReduced_of_injective (Algebra.TensorProduct.comm k F B).toRingHom
    (Algebra.TensorProduct.comm k F B).injective

end Special

section DVR

variable (S D : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing D] [Algebra S D] [Algebra.FiniteType S D]
  [Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] D)]

local notation "N" => integralClosure D (D ⊗[S] FractionRing S)
local notation "κ" => ResidueField S

/-- For a finite normalization of a smooth generic fibre over a DVR, it is enough to test
reducedness after one perfect extension of the residue field. -/
theorem isReduced_tensor_integralClosure_of_residue_test [Module.Finite D N]
    {E : Type u} [Field E] [PerfectField E] [Algebra κ E]
    (hE : IsReduced (E ⊗[κ] (κ ⊗[S] N))) :
    ∀ (F : Type u) [Field F] [Algebra S F], IsReduced (F ⊗[S] N) := by
  intro F _ _
  by_cases hF : Function.Injective (algebraMap S F)
  · exact isReduced_tensor_integralClosure_of_injective S D hF
  · let p := RingHom.ker (algebraMap S F)
    have hp : p.IsPrime := RingHom.ker_isPrime _
    have hpne : p ≠ ⊥ := fun h => hF ((RingHom.injective_iff_ker_eq_bot _).mpr h)
    have hpmax : p = maximalIdeal S := IsLocalRing.eq_maximalIdeal (hp.isMaximal hpne)
    let f : κ →ₐ[S] F := Ideal.Quotient.liftₐ _ (Algebra.ofId S F) hpmax.ge
    let : Algebra κ F := f.toRingHom.toAlgebra
    have : IsScalarTower S κ F := IsScalarTower.of_algebraMap_eq fun s => (f.commutes s).symm
    have : Algebra.FiniteType S N :=
      Algebra.FiniteType.trans (S := D) inferInstance inferInstance
    have : Algebra.FiniteType κ (κ ⊗[S] N) :=
      Algebra.FiniteType.baseChange (R := S) (A := N) κ
    have : IsReduced (F ⊗[κ] (κ ⊗[S] N)) :=
      isReduced_tensor_of_isReduced_tensor_perfect (k := κ) (B := κ ⊗[S] N) (F := F) hE
    let e := Algebra.TensorProduct.cancelBaseChange S κ F F N
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end DVR

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
