import Langlands.AbelianScheme.Tate.FullSeparation
import Langlands.AbelianScheme.InvertibleMultiplication
import Langlands.AbelianScheme.IsogenyFactorization
import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Langlands.CategoryTheory.RationalizationDenominators

/-! # Algebraic ingredients for connected integral lattice reflection -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace Langlands.AbelianScheme.Tate

variable {S : Scheme.{u}}

lemma groupHom_nsmul_id (A : AbelianScheme S) (n : ℕ) :
    groupHom (n • 𝟙 A) = GroupScheme.multiplication A.toGrp (n : ℤ) := by
  change (𝟙 A.toGrp) ^ n = (𝟙 A.toGrp) ^ (n : ℤ)
  rw [zpow_natCast]

/-- Positive multiplication is cancellable on actual abelian-scheme Hom groups. -/
theorem hom_nsmul_injective
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {A B : AbelianScheme S} {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun f : A ⟶ B => n • f) := by
  intro f g h
  have h' : (n • 𝟙 A) ≫ f = (n • 𝟙 A) ≫ g := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
  have h'' := congrArg (fun a : A ⟶ B => groupHom a) h'
  change groupHom (n • 𝟙 A) ≫ groupHom f =
    groupHom (n • 𝟙 A) ≫ groupHom g at h''
  rw [groupHom_nsmul_id] at h''
  exact congrArg Additive.ofMul
    (GroupScheme.IsogenyFactorization.hom_ext
      (multiplication_isIsogeny_of_isUnit A n (hu ⟨n, hn, trivial⟩)) _ _ h'')

/-- Actual Hom groups inject into the published rationalized Hom groups. -/
theorem ofHom_injective
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    (A B : AbelianScheme S) :
    Function.Injective (Rationalization.ofHom (X := A) (Y := B)) := by
  intro f g h
  obtain ⟨n, hn, hfg⟩ := (Rationalization.ofHom_eq_iff_exists_zsmul_eq f g).mp h
  apply hom_nsmul_injective hu (Int.natAbs_pos.mpr hn)
  have hzero : n • (f - g) = 0 := by rw [smul_sub, hfg, sub_self]
  have hzero' : n.natAbs • (f - g) = 0 := natAbs_nsmul_eq_zero.mpr hzero
  simpa only [smul_sub, sub_eq_zero] using hzero'

/-- Every rational morphism admits an integral representative with positive denominator. -/
theorem exists_positive_integral_multiple {A B : AbelianScheme S}
    (r : Rationalization.Hom A B) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : A ⟶ B, Rationalization.ofHom f = n • r := by
  induction r using TensorProduct.inductionOn with
  | tmul q f =>
    refine ⟨q.den, q.pos, q.num • f, ?_⟩
    rw [map_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]
    change q.num • ((1 : ℚ) ⊗ₜ[ℤ] f) = (q.den : ℚ) • (q ⊗ₜ[ℤ] f)
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
      zsmul_eq_mul, mul_one, mul_comm, Rat.mul_den_eq_num]
  | add r t hr ht =>
    obtain ⟨n, hn, f, hf⟩ := hr
    obtain ⟨m, hm, g, hg⟩ := ht
    refine ⟨n * m, Nat.mul_pos hn hm, m • f + n • g, ?_⟩
    rw [map_add, map_nsmul, map_nsmul, hf, hg, smul_add]
    simp only [smul_smul, mul_comm m n]

/-- Every full Tate projection at the supplied geometric point is surjective. -/
theorem full_evaluation_surjective_at
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    (A : AbelianScheme S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ S) (n : GroupScheme.Tate.Index (fun _ => True)) :
    Function.Surjective (GroupScheme.Tate.evaluation A.toGrp (Over.mk s) (fun _ => True) n) := by
  apply GroupScheme.Tate.full_evaluation_surjective_of_pow
  intro k hk y
  obtain ⟨x, hx⟩ := (multiplication_isIsogeny_of_isUnit A k
    (hu ⟨k, hk, trivial⟩)).pointsHom_surjective s y
  refine ⟨x, ?_⟩
  change x ≫ (GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom = y at hx
  simpa only [GroupScheme.points_multiplication, zpow_natCast] using hx

end Langlands.AbelianScheme.Tate
