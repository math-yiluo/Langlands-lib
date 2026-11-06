import Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionStatement
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra
import Langlands.AbelianScheme.Tate.ConnectedTorsionDetection

/-! # Integral reflection of rational abelian-scheme isomorphisms -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme.Tate

variable {S : Scheme.{u}}

/-- An integral full Tate action at one geometric point removes every rational
denominator from an actual rationalized homomorphism. -/
theorem exists_ofHom_eq_of_full_image
    (htor : TorsionFiniteEtaleStatement.{u})
    [IsLocallyNoetherian S] [ConnectedSpace S]
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {A B : AbelianScheme S}
    (r : Rationalization.Hom A B)
    (hi : ∀ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
      ∃ y : GroupScheme.Tate.Full B.toGrp (Over.mk s),
        rationalHomMap (Over.mk s) (fun _ => True) r
            (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x) =
          GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) y) :
    ∃ g : A ⟶ B, Rationalization.ofHom g = r := by
  obtain ⟨n, hn, f, hf⟩ := exists_positive_integral_multiple r
  have hmap : ∀ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
      ∃ y : GroupScheme.Tate.Full B.toGrp (Over.mk s),
        GroupScheme.Tate.map (Over.mk s) (fun _ => True) (groupHom f) x = n • y := by
    intro x
    obtain ⟨y, hy⟩ := hi x
    refine ⟨y, GroupScheme.Tate.full_toRational_injective B.toGrp (Over.mk s) ?_⟩
    calc
      GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True)
          (GroupScheme.Tate.map (Over.mk s) (fun _ => True) (groupHom f) x) =
        rationalHomMap (Over.mk s) (fun _ => True) (Rationalization.ofHom f)
          (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x) := by
            rw [rationalHomMap_ofHom]
            rfl
      _ = n • rationalHomMap (Over.mk s) (fun _ => True) r
          (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x) := by
            rw [hf, map_nsmul]
            rfl
      _ = GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) (n • y) := by
            rw [hy, map_nsmul]
  have hz : ∀ z : GroupScheme.Tate.Level A.toGrp (Over.mk s) n,
      GroupScheme.Tate.levelMap (Over.mk s) (groupHom f) n z = 0 := by
    intro z
    obtain ⟨x, hx⟩ := full_evaluation_surjective_at hu A s ⟨n, hn, trivial⟩ z
    obtain ⟨y, hy⟩ := hmap x
    rw [← hx]
    change GroupScheme.Tate.evaluation B.toGrp (Over.mk s) (fun _ => True)
      ⟨n, hn, trivial⟩ (GroupScheme.Tate.map (Over.mk s) (fun _ => True) (groupHom f) x) = 0
    rw [hy, map_nsmul]
    exact GroupScheme.Tate.level_nsmul_eq_zero B.toGrp (Over.mk s) n _
  have hker := kernel_comp_eq_one_of_levelMap_eq_zero
    htor s f n hn (hu ⟨n, hn, trivial⟩) hz
  let hniso := multiplication_isIsogeny_of_isUnit A n (hu ⟨n, hn, trivial⟩)
  let g : A ⟶ B := Additive.ofMul
    (GroupScheme.IsogenyFactorization.lift hniso (groupHom f) hker)
  have hfac : (n • 𝟙 A) ≫ g = f := by
    apply Additive.toMul.injective
    change groupHom (n • 𝟙 A) ≫ groupHom g = groupHom f
    rw [groupHom_nsmul_id]
    exact GroupScheme.IsogenyFactorization.fac hniso (groupHom f) hker
  have hng : n • g = f := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using hfac
  refine ⟨g, ?_⟩
  have hng' : n • Rationalization.ofHom g = n • r := by
    rw [← map_nsmul, hng, hf]
  have hnr : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hc := congrArg (fun t : Rationalization.Hom A B => (n : ℚ)⁻¹ • t) hng'
  simpa only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hnr, one_smul]
    using hc

/-- The exact published connected-base integral Tate reflection proposition. -/
theorem connectedIntegralLatticeReflection :
    ConnectedIntegralLatticeReflectionStatement.{u} := by
  intro htor S _ _ hu Ω _ _ _ s A B e hf hi
  obtain ⟨f, hfr⟩ := exists_ofHom_eq_of_full_image htor hu s e.hom hf
  obtain ⟨g, hgr⟩ := exists_ofHom_eq_of_full_image htor hu s e.inv hi
  have hfg : f ≫ g = 𝟙 A := by
    apply ofHom_injective hu A A
    rw [Rationalization.ofHom_comp, Rationalization.ofHom_id, hfr, hgr]
    exact e.hom_inv_id
  have hgf : g ≫ f = 𝟙 B := by
    apply ofHom_injective hu B B
    rw [Rationalization.ofHom_comp, Rationalization.ofHom_id, hgr, hfr]
    exact e.inv_hom_id
  exact ⟨⟨f, g, hfg, hgf⟩, hfr, hgr⟩

end Langlands.AbelianScheme.Tate
