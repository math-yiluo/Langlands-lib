import Langlands.Geometry.FormalGroup.PDivisibleBaseChangeCoherence
import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeBaseChange
import Langlands.Geometry.FormalGroup.RamifiedSpecialPDivisible

/-! # Compare formal coefficient extension with pullback of the finite towers -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory ValuativeRel

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ] {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {p : ℕ} [Fact p.Prime]

/-- Integral formal isomorphisms identify the actual finite torsion towers. -/
def Iso.pDivisibleIso (f : Iso M N) (hM : M.IsPiDivisible (p : O)) (hN : N.IsPiDivisible (p : O)) :
    hM.pDivisibleGroup ≅ hN.pDivisibleGroup where
  hom := f.hom.pDivisibleMap hM hN
  inv := f.inv.pDivisibleMap hN hM
  hom_inv_id := by rw [← Hom.pDivisibleMap_comp, f.inv_hom, Hom.pDivisibleMap_id]
  inv_hom_id := by rw [← Hom.pDivisibleMap_comp, f.hom_inv, Hom.pDivisibleMap_id]

variable (φ : R →ₐ[O] S) (hM : M.IsPiDivisible (p : O)) (hN : N.IsPiDivisible (p : O))

/-- The actual tower of the coefficient-extended formal law is the pullback tower. -/
def IsPiDivisible.pDivisibleBaseChangeIso :
    letI : Algebra R S := φ.toRingHom.toAlgebra
    (hM.map φ).pDivisibleGroup ≅ (PDivisibleGroup.baseChangeFunctor R S p).obj hM.pDivisibleGroup :=
  letI : Algebra R S := φ.toRingHom.toAlgebra
  PDivisibleGroup.isoOfInclusionDiagrams (G := (hM.map φ).pDivisibleGroup)
    (H := (PDivisibleGroup.baseChangeFunctor R S p).obj hM.pDivisibleGroup)
    (hM.torsionSchemeInclusionsBaseChangeIso φ)

/-- The comparison commutes with actual tower maps of integral formal homomorphisms. -/
theorem Hom.pDivisibleBaseChangeIso_naturality (f : Hom M N) :
    letI : Algebra R S := φ.toRingHom.toAlgebra
    (f.map φ).pDivisibleMap (hM.map φ) (hN.map φ) ≫ (hN.pDivisibleBaseChangeIso φ).hom =
      (hM.pDivisibleBaseChangeIso φ).hom ≫ (PDivisibleGroup.baseChangeFunctor R S p).map
        (f.pDivisibleMap hM hN) := by
  apply PDivisibleGroup.Hom.ext
  intro n
  exact hM.torsionPullbackIso_naturality φ hN f n

/-- The comparison intertwines the order action on the formal law with its tower pullback. -/
theorem OrderAction.pDivisibleBaseChangeIso_order {A : Type w} [Ring A] [Algebra O A]
    (E : OrderAction A M) (a : A) :
    letI : Algebra R S := φ.toRingHom.toAlgebra
    ((E.map φ).pDivisibleAction (hM.map φ) a).asHom ≫ (hM.pDivisibleBaseChangeIso φ).hom =
      (hM.pDivisibleBaseChangeIso φ).hom ≫ (PDivisibleGroup.baseChangeFunctor R S p).map
        (E.pDivisibleAction hM a).asHom :=
  Hom.pDivisibleBaseChangeIso_naturality φ hM hM (E.action a)

end Langlands.FormalGroup.ModuleLaw

namespace Langlands.FormalGroup.LocalDivision.SpecialModule.HeightSquaredModule

open CentralDivision CentralSimple ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type w} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]
variable {π : 𝒪[K]} (X : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := R) π)
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}
variable (hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e) (he : 0 < e) (φ : R →ₐ[𝒪[K]] S)

/-- Coefficient extension of the actual primal tower of a special formal module. -/
def pDivisibleBaseChangeIso :
    letI : Algebra R S := φ.toRingHom.toAlgebra
    (X.mapSameUniverse φ).pDivisibleGroup hp he ≅
      (PDivisibleGroup.baseChangeFunctor R S p).obj (X.pDivisibleGroup hp he) :=
  (X.property.2.piDivisible.unit_mul_pow hp he).pDivisibleBaseChangeIso φ

/-- The primal coefficient comparison respects the full division order. -/
theorem pDivisibleBaseChangeIso_order (a : IntegerRing K D) :
    letI : Algebra R S := φ.toRingHom.toAlgebra
    ((X.mapSameUniverse φ).pDivisibleAction hp he a).asHom ≫ (X.pDivisibleBaseChangeIso hp he φ).hom =
      (X.pDivisibleBaseChangeIso hp he φ).hom ≫ (PDivisibleGroup.baseChangeFunctor R S p).map
        (X.pDivisibleAction hp he a).asHom :=
  X.val.order.pDivisibleBaseChangeIso_order φ (X.property.2.piDivisible.unit_mul_pow hp he) a

end Langlands.FormalGroup.LocalDivision.SpecialModule.HeightSquaredModule
