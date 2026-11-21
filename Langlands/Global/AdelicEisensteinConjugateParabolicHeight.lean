import Langlands.Global.AdelicEisensteinSeries
import Langlands.Automorphic.GroupSchemeConstantTermConjugation

/-! # Iwasawa height under conjugation of a parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  {p p' : P ⟶ G} {t : AdelicGroupPoints F G} {K : Subgroup (AdelicGroupPoints F G)}

/-- An adelically conjugate parabolic has Iwasawa coverage with the same compact. -/
theorem IsIwasawaCompact.of_conjugate_map (hK : IsIwasawaCompact p K)
    (hp : ∀ a, map F P G p' a = t * map F P G p a * t⁻¹) :
    IsIwasawaCompact p' K := by
  obtain ⟨a, k, hk, hakt⟩ := hK.exists_eq t⁻¹
  have ht : t = k⁻¹ * (map F P G p a)⁻¹ := by rw [← mul_inv_rev, hakt, inv_inv]
  refine ⟨hK.isCompact, eq_univ_of_forall fun x => ?_⟩
  obtain ⟨b, v, hv, hb⟩ := hK.exists_eq (k * x)
  refine ⟨_, ⟨a * b * a⁻¹, rfl⟩, k⁻¹ * v, K.mul_mem (K.inv_mem hk) hv, ?_⟩
  rw [hp]
  simp only [map_mul, map_inv]
  calc
    _ = k⁻¹ * (map F P G p b * v) := by rw [ht]; group
    _ = x := by rw [hb, inv_mul_cancel_left]

variable [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion p'.hom.hom.left]

/-- Under left translation by the conjugating point, the new height is
the original height plus the new height at that point. -/
theorem IsIwasawaCompact.height_mul_of_conjugate_map (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact p' K)
    (hp : ∀ a, map F P G p' a = t * map F P G p a * t⁻¹) (g : AdelicGroupPoints F G) :
    hK'.height (t * g) = hK.height g + hK'.height t := by
  obtain ⟨a, k, hk, rfl⟩ := hK.exists_eq g
  have ht : t * (map F P G p a * k) = map F P G p' a * (t * k) := by rw [hp]; group
  rw [ht, hK'.height_map_mul, hK'.height_mul_right t hk, hK.height_eq hk rfl]

/-- The transported exponential height factor is the old factor times a
scalar independent of the adelic argument. -/
theorem IsIwasawaCompact.heightPower_mul_of_conjugate_map (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact p' K)
    (hp : ∀ a, map F P G p' a = t * map F P G p a * t⁻¹)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK'.heightPower lam (t * g) = hK.heightPower lam g * hK'.heightPower lam t := by
  simp only [heightPower, hK.height_mul_of_conjugate_map hK' hp, map_add, Complex.exp_add]

end AdelicGroupPoints

open AdelicGroupPoints

/-- Conjugating the parabolic map by a rational point retains the Iwasawa
compact and yields an explicit comparison of the two height factors. -/
def EisensteinConjugateParabolicHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K),
    let p' := p ≫ (G.innerIso s).hom
    ∃ hK' : IsIwasawaCompact p' K, ∀ lam g,
      hK'.heightPower lam (innerAdelicPoint F G s * g) =
        hK.heightPower lam g * hK'.heightPower lam (innerAdelicPoint F G s)

theorem eisensteinConjugateParabolicHeight : EisensteinConjugateParabolicHeightStatement.{u} := by
  intro F _ _ G P _ _ p _ s K hK
  let p' := p ≫ (G.innerIso s).hom
  let : IsIso (G.innerIso s).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso (G.innerIso s))).hom)
  let : IsClosedImmersion p'.hom.hom.left := by
    change IsClosedImmersion (p.hom.hom.left ≫ (G.innerIso s).hom.hom.hom.left)
    infer_instance
  let t := innerAdelicPoint F G s
  have hmap (a : AdelicGroupPoints F P) : map F P G p' a = t * map F P G p a * t⁻¹ := by
    dsimp only [p']
    rw [map_comp_apply_of_hom]
    exact affinePointsTarget_innerIso_hom F G s _
  let hK' := hK.of_conjugate_map hmap
  exact ⟨hK', fun lam g => hK.heightPower_mul_of_conjugate_map hK' hmap lam g⟩

end Langlands.Global
