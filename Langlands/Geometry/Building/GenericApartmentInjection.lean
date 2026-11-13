import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.Geometry.Building.ChamberSharpCore
import Langlands.GroupScheme.Rational.BruhatOppositeCellReduction
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Generic apartment injection without descent dependencies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-- For apartment data over any field and without apartment axioms, an element of
`N(k) ∩ G(k)^♯_x` fixes `x` (KP Proposition 7.6.3, normalizer part). -/
theorem normalizer_smul_eq_self_of_mem_sharpFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (n : normalizerPoints i)
    (hn : (n : rationalPoints G) ∈ D.sharpFixer {x}) : n • x = x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, m, hm, heq⟩ :=
    D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi x ν hν hn
  change v * w * m = (n : rationalPoints G) at heq
  obtain ⟨_, hmN, hmx⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hm
  let m' : normalizerPoints i := ⟨m, hmN⟩
  let q : normalizerPoints i := n * m'⁻¹
  have hq : (q : rationalPoints G) = v * w := by
    change (n : rationalPoints G) * m⁻¹ = v * w
    rw [← heq, mul_inv_cancel_right]
  have hvU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hv).1
  have hwU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hw).1
  have hvopp : v ∈ (Dynamic.unipotent
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).carrier
        (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
    exact hvU
  have hq1 : q = 1 :=
    normalizer_eq_one_of_unipotent_product i ν q ⟨v, hvopp⟩ ⟨w, hwU⟩ hq
  have hnm : n = m' := mul_inv_eq_one.mp hq1
  rw [hnm]
  exact hmx

/-- **The apartment embeds in the reduced building** (KP Proposition 7.6.3 and Remark 7.6.5),
for apartment data of a maximal split torus of a connected reductive group over any field,
without apartment axioms. -/
theorem apartmentMap_injective (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    Function.Injective D.apartmentMap :=
  ApartmentQuotient.apartment_injective D.sharpFixerFamily
    (fun n x hn => D.normalizer_smul_eq_self_of_mem_sharpFixer hG hi x n hn)

end KPApartmentData

end Langlands.Geometry.Building
