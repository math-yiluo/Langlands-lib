import Langlands.AbelianScheme.ArtinianHodgeFunctionClasses
import Langlands.AbelianScheme.ArtinianHodgeInjectivity
import Langlands.AbelianScheme.StructureCohomologyInversion
import Langlands.Algebra.InvolutionSummands
import Mathlib.RingTheory.Smooth.Flat

/-! # Inversion summands of the function Čech cochains -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.Algebra
open Langlands.AlgebraicGeometry.AffineCechDeRham
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter unitCohomologyPullbackLinear)
open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology (structureCohomology)
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof (secHom smooth_secHom)

section Base

variable {R : Type u} [CommRing R] (B : AbelianScheme (Spec (CommRingCat.of R)))
  (U : Scheme.AffineOpenCover.{u} B.X.left)
  (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ ι[B.X].left ⁻¹ᵁ coverOpens U (β i))

/-- Pullback of the function cochains by inversion and the compatible chart assignment. -/
abbrev functionInversion (p : ℕ) := pullFunctions ι[B.X].left (Over.w ι[B.X]) β hβ p

lemma functionInversion_involutive (h : Function.Involutive β) (p : ℕ) :
    Function.Involutive (functionInversion B U β hβ p) :=
  pullFunctions_involutive ι[B.X].left (Over.w ι[B.X]) β hβ (inversion_left_sq B) h p

/-- The sign summand of the function cochains in a fixed degree. -/
abbrev signedFunctions (s : R) (p : ℕ) := involutionPart (functionInversion B U β hβ p) s

/-- The Čech differential on a sign summand. -/
abbrev signedFunctionD (s : R) (p : ℕ) :
    signedFunctions B U β hβ s p →ₗ[R] signedFunctions B U β hβ s (p + 1) :=
  involutionPartMap _ _ s (cechD U (functions B.X.hom) p) fun c =>
    (cechD_pullFunctions ι[B.X].left (Over.w ι[B.X]) β hβ p c).symm

lemma signedFunctionD_comp (s : R) (p : ℕ) :
    (signedFunctionD B U β hβ s (p + 1)).comp (signedFunctionD B U β hβ s p) = 0 := by
  apply LinearMap.ext
  intro x
  exact Subtype.ext (cechD_cechD U (functions B.X.hom) p x.val)

/-- The actual function cochain modules over a finite cover are flat over the base. -/
lemma functionCochain_flat [Finite U.I₀] (p : ℕ) : Module.Flat R (Cochains U (functions B.X.hom) p) := by
  classical
  let := Fintype.ofFinite U.I₀
  let C (σ : Fin (p + 1) → U.I₀) := (sectionAlgebras B.X.hom).obj (op (inter (coverOpens U) σ))
  let (σ : Fin (p + 1) → U.I₀) : Module.Flat R (C σ) := by
    have h := smooth_secHom (p := B.X.hom) (isAffineOpen_inter B.X.hom U σ)
    exact RingHom.Smooth.flat h
  change Module.Flat R (∀ σ, C σ)
  exact Module.Flat.of_linearEquiv
    (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun σ => C σ)).symm

variable [Algebra ℚ R] (hInv : Function.Involutive β)

/-- The projection to the selected sign of inversion, using the scalar `1/2`. -/
abbrev functionSignProjector (s : R) (hs : s * s = 1) (p : ℕ) :=
  involutionProjector _ (functionInversion_involutive B U β hβ hInv p) s (half R) hs

lemma functionSignProjector_comm (s : R) (hs : s * s = 1) (p : ℕ)
    (x : Cochains U (functions B.X.hom) p) :
    (signedFunctionD B U β hβ s p (functionSignProjector B U β hβ hInv s hs p x)).val =
      (functionSignProjector B U β hβ hInv s hs (p + 1) (cechD U (functions B.X.hom) p x)).val := by
  change cechD U (functions B.X.hom) p (half R • (x + s • functionInversion B U β hβ p x)) =
    half R • (cechD U (functions B.X.hom) p x +
      s • functionInversion B U β hβ (p + 1) (cechD U (functions B.X.hom) p x))
  rw [map_smul, map_add, map_smul, cechD_pullFunctions]

lemma functionSignProjector_on_part (s : R) (hs : s * s = 1) (p : ℕ)
    (x : signedFunctions B U β hβ s p) :
    functionSignProjector B U β hβ hInv s hs p x.val = x :=
  LinearMap.congr_fun (involutionProjector_subtype _
    (functionInversion_involutive B U β hβ hInv p) _ _ hs (half_add_half R)) x

/-- The first differential on the negative sign is injective: its kernel would be
both a constant function cocycle and negated by inversion. -/
lemma signedFunctionD_neg_zero_injective : Function.Injective (signedFunctionD B U β hβ (-1) 0) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hIso : IsIso B.X.hom.appTop := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
    _ _ _ inferInstance inferInstance inferInstance ⊤
  have hz : cechD U (functions B.X.hom) 0 x.val = 0 := congrArg Subtype.val hx
  obtain ⟨r, hr, _⟩ := existsUnique_scalar_of_cechD_zero U B.X.hom x.val hz
  have he : functionInversion B U β hβ 0 x.val = x.val := by
    funext σ
    rw [pullFunctions_apply, hr (β ∘ σ), (tupleAlgHomOver ι[B.X].left (Over.w ι[B.X])
      β hβ σ).commutes, hr σ]
  have hn : functionInversion B U β hβ 0 x.val = -x.val := by
    simpa only [neg_one_smul] using mem_involutionPart.mp x.property
  exact Subtype.ext (eq_zero_of_eq_neg_of_rat (R := R) (he.symm.trans hn))

end Base

section Field

variable {K : Type u} [Field K] [Algebra ℚ K] (B : AbelianScheme (Spec (CommRingCat.of K)))
  (U : Scheme.AffineOpenCover.{u} B.X.left) [Finite U.I₀]
  (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ ι[B.X].left ⁻¹ᵁ coverOpens U (β i))
  (hInv : Function.Involutive β)

include hInv

/-- If the actual cohomology in the indicated degree has the opposite inversion
sign, the sign subcomplex is exact in that degree. -/
lemma signedFunction_exact_of_opposite (s : K) (hs : s * s = 1) (n : ℕ)
    (ho : ∀ x : structureCohomology B.X (n + 1), pullStructure B ι[B.X] (n + 1) x = -(s • x)) :
    Function.Exact (signedFunctionD B U β hβ s n) (signedFunctionD B U β hβ s (n + 1)) := by
  intro z
  constructor
  · intro hz
    let w : (cechD U (functions B.X.hom) (n + 1)).ker := ⟨z.val, congrArg Subtype.val hz⟩
    have hm : pullFunctionCocycles ι[B.X] U U β hβ n w = s • w :=
      Subtype.ext (mem_involutionPart.mp z.property)
    have h := (functionCocycleClass_pull ι[B.X] U U β hβ n w).trans
      (ho (functionCocycleClass B.X.hom U n w))
    rw [hm, map_smul] at h
    have h0 := eq_zero_of_eq_neg_of_rat (R := K) h
    have hw : functionCocycleClass B.X.hom U n w = 0 := by
      calc
        _ = (s * s) • functionCocycleClass B.X.hom U n w := by rw [hs, one_smul]
        _ = 0 := by rw [mul_smul, h0, smul_zero]
    obtain ⟨y, hy⟩ := (functionCocycleClass_eq_zero_iff B.X.hom U n w).mp hw
    refine ⟨functionSignProjector B U β hβ hInv s hs n y, Subtype.ext ?_⟩
    rw [functionSignProjector_comm, hy]
    exact congrArg Subtype.val (functionSignProjector_on_part B U β hβ hInv s hs (n + 1) z)
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun (signedFunctionD_comp B U β hβ s n) x

lemma signedFunction_even_exact_one :
    Function.Exact (signedFunctionD B U β hβ 1 0) (signedFunctionD B U β hβ 1 1) :=
  signedFunction_exact_of_opposite B U β hβ hInv 1 (one_mul 1) 0 fun x => by
    simpa only [one_smul] using pullStructure_inv_one B x

lemma signedFunction_odd_exact_two :
    Function.Exact (signedFunctionD B U β hβ (-1) 1) (signedFunctionD B U β hβ (-1) 2) :=
  signedFunction_exact_of_opposite B U β hβ hInv (-1) (by simp) 1 fun x => by
    simpa only [neg_one_smul, neg_neg] using pullStructure_inv_two B x

end Field

end Langlands.AbelianScheme
