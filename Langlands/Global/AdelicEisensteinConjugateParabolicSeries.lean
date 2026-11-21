import Langlands.Global.AdelicEisensteinConjugateParabolicHeight
import Langlands.Global.AdelicIntertwiningConvergenceReduction
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Rational conjugation of the inducing parabolic of an Eisenstein series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {iU : U ⟶ P}
  (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

private theorem monoidHom_map_conjugate_target {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : H ⟶ G) :
    (map F H G (j ≫ (G.innerIso s).hom)).toMonoidHom =
      (MulAut.conj (innerAdelicPoint F G s)).toMonoidHom.comp (map F H G j).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  change map F H G (j ≫ (G.innerIso s).hom) a =
    innerAdelicPoint F G s * map F H G j a * (innerAdelicPoint F G s)⁻¹
  rw [map_comp_apply_of_hom]
  exact affinePointsTarget_innerIso_hom F G s _

/-- Rational conjugation transports the whole left invariance subgroup
of the inducing function. -/
theorem parabolicQuotientSubgroup_conjugate :
    parabolicQuotientSubgroup F (p ≫ (G.innerIso s).hom) iU l =
      (parabolicQuotientSubgroup F p iU l).map
        (MulAut.conj (innerAdelicPoint F G s)).toMonoidHom := by
  simp only [parabolicQuotientSubgroup, parabolicUnipotentImage, parabolicLeviRationalImage,
    Subgroup.map_sup, MonoidHom.map_range, ← Category.assoc, monoidHom_map_conjugate_target s,
    MonoidHom.comp_assoc]

/-- Left translation of the inducing function retains invariance under the
conjugated parabolic quotient subgroup. -/
theorem isLeftInvariantUnder_conjugate_parabolic {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (p ≫ (G.innerIso s).hom) iU l)
      (fun g => φ ((innerAdelicPoint F G s)⁻¹ * g)) := by
  let t := innerAdelicPoint F G s
  intro x hx g
  rw [parabolicQuotientSubgroup_conjugate s] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change φ (t⁻¹ * ((t * y * t⁻¹) * g)) = φ (t⁻¹ * g)
  rw [show t⁻¹ * ((t * y * t⁻¹) * g) = y * (t⁻¹ * g) by group]
  exact hφ y hy (t⁻¹ * g)

variable [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- In the same compact, conjugating the parabolic and left translating its
inducing function gives the original Eisenstein series times one height scalar. -/
theorem IsIwasawaCompact.eisensteinSeries_conjugate_parabolic (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact (p ≫ (G.innerIso s).hom) K)
    [IsClosedImmersion (p ≫ (G.innerIso s).hom).hom.hom.left]
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK'.eisensteinSeries (fun x => φ ((innerAdelicPoint F G s)⁻¹ * x)) lam g =
      hK'.heightPower lam (innerAdelicPoint F G s) * hK.eisensteinSeries φ lam g := by
  let t := innerAdelicPoint F G s
  let tR : rationalSubgroup F G := ⟨t, ⟨_, (innerAdelicPoint_eq_rational F G s).symm⟩⟩
  let p' := p ≫ (G.innerIso s).hom
  let φ' : AdelicGroupPoints F G → ℂ := fun x => φ (t⁻¹ * x)
  have hφ' : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p' iU l) φ' :=
    isLeftInvariantUnder_conjugate_parabolic s hφ
  have hparabolic (v : rationalSubgroup F G) :
      tR * v * tR⁻¹ ∈ parabolicRationalSubgroup F p' ↔ v ∈ parabolicRationalSubgroup F p := by
    unfold parabolicRationalSubgroup
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change (MulAut.conj t) (v : AdelicGroupPoints F G) ∈
      (rationalSubgroup F P).map (map F P G p').toMonoidHom ↔
      (v : AdelicGroupPoints F G) ∈ (rationalSubgroup F P).map (map F P G p).toMonoidHom
    dsimp only [p']
    rw [monoidHom_map_conjugate_target s, ← Subgroup.map_map, Subgroup.mem_map_equiv]
    simp only [t, MulEquiv.symm_apply_apply]
  let E : ParabolicRationalCosets F p ≃ ParabolicRationalCosets F p' :=
    Quotient.congr (Equiv.mulLeft tR) fun x y => by
      simp only [QuotientGroup.rightRel_apply, Equiv.coe_mulLeft]
      have heq : (tR * y) * (tR * x)⁻¹ = tR * (y * x⁻¹) * tR⁻¹ := by group
      rw [heq, hparabolic]
  have hmap : ∀ x, map F P G p' x = t * map F P G p x * t⁻¹ := by
    intro x
    exact DFunLike.congr_fun (monoidHom_map_conjugate_target s p) x
  have hterm (x : ParabolicRationalCosets F p) :
      hK'.eisensteinTerm φ' lam g (E x) = hK'.heightPower lam t * hK.eisensteinTerm φ lam g x := by
    induction x using Quotient.inductionOn with
    | _ v =>
      change hK'.eisensteinTerm φ' lam g (Quotient.mk _ (tR * v)) =
        hK'.heightPower lam t * hK.eisensteinTerm φ lam g (Quotient.mk _ v)
      rw [hK'.eisensteinTerm_mk hφ' hl hU, hK.eisensteinTerm_mk hφ hl hU]
      change hK'.parameterTwist φ' lam (t * (v : AdelicGroupPoints F G) * g) =
        hK'.heightPower lam t * hK.parameterTwist φ lam ((v : AdelicGroupPoints F G) * g)
      rw [mul_assoc]
      simp only [parameterTwist, φ', inv_mul_cancel_left,
        hK.heightPower_mul_of_conjugate_map hK' hmap]
      ring
  change (∑' x : ParabolicRationalCosets F p', hK'.eisensteinTerm φ' lam g x) =
    hK'.heightPower lam t * ∑' x : ParabolicRationalCosets F p, hK.eisensteinTerm φ lam g x
  calc
    _ = ∑' x : ParabolicRationalCosets F p, hK'.eisensteinTerm φ' lam g (E x) :=
      (E.tsum_eq _).symm
    _ = _ := by simp_rw [hterm]; rw [tsum_mul_left]

end AdelicGroupPoints

open AdelicGroupPoints

/-- Simultaneously conjugating the inducing parabolic and translating the
inducing function transports the actual Eisenstein series. -/
def EisensteinConjugateParabolicSeriesStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X),
    let p' := p ≫ (G.innerIso s).hom
    ∀ [IsClosedImmersion p'.hom.hom.left],
      IsRationalLeviSubgroup l → LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
        (φ : AdelicGroupPoints F G → ℂ),
        IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ →
        ∃ hK' : IsIwasawaCompact p' K, ∀ lam g,
          hK'.eisensteinSeries (fun x => φ ((innerAdelicPoint F G s)⁻¹ * x)) lam g =
            hK'.heightPower lam (innerAdelicPoint F G s) * hK.eisensteinSeries φ lam g

theorem eisensteinConjugateParabolicSeries : EisensteinConjugateParabolicSeriesStatement.{u} := by
  intro F _ _ G P M U _ _ p _ iU l s p' _ hl hU K hK φ hφ
  obtain ⟨hK', _⟩ := eisensteinConjugateParabolicHeight F G P p s K hK
  exact ⟨hK', hK.eisensteinSeries_conjugate_parabolic s hK' hl hU hφ⟩

end Langlands.Global
