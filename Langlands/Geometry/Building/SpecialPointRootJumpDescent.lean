import Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement
import Langlands.Geometry.Building.LeviSpecialPointRestrictionProof
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction

/-! # Specialness from zero root-jump witnesses -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section Geometry

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (iS : S.toGrp ⟶ G) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
  (hS : IsSplitTorus S.toGrp)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "iT_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iT

variable [instUpperAffine : IsAffineHom (baseChanged k K G).X.hom]

private instance upperLft [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (baseChanged k K G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- A character restriction identity gives the identical pulled-back root forms. -/
theorem rootForm_comp_torusFieldTranslationMap
    (a : relativeRoots iS) (β : relativeRoots (T := T_K) iT_K)
    (hres : (CommGroupScheme.baseChange b).map f ≫ β.val =
      characterLattice.baseChange b S a.val) :
    (rootForm (S := T_K) iT_K β).comp (torusFieldTranslationMap k K f iT hS) =
      (rootForm iS a).comp (rootAnnihilator iS).mkQ := by
  apply LinearMap.ext
  intro v
  change eval T_K β.val (descentCocharacterMap k K f hS v) = eval S a.val v
  rw [eval_descentCocharacterMap, hres, eval_splitCocharacterBaseChange]

/-- Equality of pulled-back kernels reflects through the quotient map. -/
theorem ker_eq_of_comp_mkQ {l₁ l₂ : TranslationSpace iS →ₗ[ℝ] ℝ}
    (h : LinearMap.ker (l₁.comp (rootAnnihilator iS).mkQ) =
      LinearMap.ker (l₂.comp (rootAnnihilator iS).mkQ)) :
    LinearMap.ker l₁ = LinearMap.ker l₂ := by
  ext v
  obtain ⟨w, rfl⟩ := (rootAnnihilator iS).mkQ_surjective v
  exact SetLike.ext_iff.mp h w

variable [Mono iS.hom.hom.left]
  [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map iT).hom.hom.left]
  [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
  {ω : kˣ → ℝ} {ωK : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map iT) ωK)
  (DS : KPApartmentData iS ω)

/-- Internal geometric assembly at a chosen pair of apartment points. -/
def SpecialPointRootJumpDescentStatement
    (_hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp) : Prop :=
  ∀ (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (x : D.Apartment) (w : DS.Apartment),
    AffineRootSystem.IsSpecialPoint D.affineRoots x →
    (∀ (ψ : D.affineRoots), ψ.val x = 0 →
      ψ.val.linear.comp (torusFieldTranslationMap k K f iT hS) ≠ 0 →
      ∃ (a : relativeRoots iS) (g : rationalPoints G),
        g ∈ rootGroupPoints iS a ∧ w.val a g = (0 : WithTop ℝ) ∧
          LinearMap.ker ((rootForm iS a).comp (rootAnnihilator iS).mkQ) =
            LinearMap.ker (ψ.val.linear.comp (torusFieldTranslationMap k K f iT hS))) →
    AffineRootSystem.IsSpecialPoint DS.affineRoots w

include hT in
set_option maxHeartbeats 300000 in
/-- The geometric assembly only needs zero root jumps at the chosen pair of points. -/
theorem isSpecialPoint_of_rootJumpDescent :
    SpecialPointRootJumpDescentStatement
      (iS := iS) (iT := iT) (f := f) (hS := hS) (D := D) (DS := DS) hT := by
  intro hf x w hx hJ
  let P := torusFieldTranslationMap k K f iT hS
  let Q := (rootAnnihilator iS).mkQ
  apply (AffineRootSystem.isSpecialPoint_iff_ker
    (fun _ h => Langlands.BruhatTits.SpecialCompact.affineRoot_linear_ne_zero_of_split
      hS iS DS h) w).mpr
  intro θ hθ
  obtain ⟨a, hθlin, hθjump⟩ := hθ
  let a' : relativeRoots (CommGroupScheme.groupHom f ≫ iT) :=
    ⟨a.val, by rw [hf]; exact a.property⟩
  let β := splittingFieldRootLift (K := K) (M := T) hS hT f iT a'
  have hres : (CommGroupScheme.baseChange b).map f ≫ β.val =
      characterLattice.baseChange b S a.val :=
    splittingFieldRootLift_restriction (K := K) (M := T) hS hT f iT a'
  have hform := rootForm_comp_torusFieldTranslationMap iS iT f hS a β hres
  obtain ⟨ψ₀, hψ₀, c, hc, hψ₀lin⟩ :=
    D.exists_affineRoot_linear_eq_smul_rootForm (S := T_K) hT
      (hT.finite_relativeRoots (T := T_K) iT_K) β
  obtain ⟨ψ, hψ, hker⟩ := (AffineRootSystem.isSpecialPoint_iff_ker
    (fun _ h => Langlands.BruhatTits.SpecialCompact.affineRoot_linear_ne_zero_of_split
      (S := T_K) hT iT_K D h) x).mp hx ψ₀ hψ₀
  have hk : LinearMap.ker (θ.linear.comp Q) = LinearMap.ker (ψ.linear.comp P) := by
    calc
      LinearMap.ker (θ.linear.comp Q) =
          LinearMap.ker ((rootForm iS a).comp Q) := by rw [hθlin]
      _ = LinearMap.ker (ψ₀.linear.comp P) := by
        rw [hψ₀lin, LinearMap.smul_comp, hform, LinearMap.ker_smul _ c hc]
      _ = LinearMap.ker (ψ.linear.comp P) := by
        rw [LinearMap.ker_comp, LinearMap.ker_comp, hker]
  have hθQ : θ.linear.comp Q ≠ 0 := by
    intro hz
    have hz' : θ.linear = 0 := by
      apply LinearMap.ext
      intro v
      obtain ⟨v, rfl⟩ := (rootAnnihilator iS).mkQ_surjective v
      exact LinearMap.congr_fun hz v
    exact Langlands.BruhatTits.SpecialCompact.affineRoot_linear_ne_zero_of_split
      hS iS DS ⟨a, hθlin, hθjump⟩ hz'
  have hψP : ψ.linear.comp P ≠ 0 := by
    intro hz
    apply hθQ
    apply LinearMap.ker_eq_top.mp
    rw [hk, hz, LinearMap.ker_zero]
  obtain ⟨a₁, g, hg, hval, hk₁⟩ := hJ ⟨ψ, hψ.1⟩ hψ.2 hψP
  obtain ⟨a₂, hlin, hjump⟩ := DS.affineFunctional_mem_extendedAffineRoots (a := a₁) hg hval
  have ha₂ : a₂ = a₁ := Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split
    hS iS (hlin.symm.trans (DS.affineFunctional_linear a₁ w 0))
  subst a₂
  obtain ⟨n, hn⟩ := KPApartmentData.exists_two_pow_smul_not_mem_relativeRoots
    hS (hS.finite_relativeRoots iS) a₁
  obtain ⟨m, hm⟩ := DS.exists_two_pow_smul_mem_affineRoots n a₁
    (DS.affineFunctional a₁ w 0) hlin hjump hn
  refine ⟨(2 : ℝ) ^ m • DS.affineFunctional a₁ w 0, ⟨hm, by simp⟩, ?_⟩
  rw [AffineMap.smul_linear, DS.affineFunctional_linear,
    LinearMap.ker_smul _ _ (pow_ne_zero _ two_ne_zero)]
  apply ker_eq_of_comp_mkQ iS
  exact hk.trans hk₁.symm

end Geometry

end Langlands.Geometry.Building
