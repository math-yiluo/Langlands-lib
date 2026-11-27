import Langlands.AbelianScheme.ArtinianHodgeSignedFunctions
import Langlands.AbelianScheme.RationalBaseChange
import Langlands.Algebra.ArtinianComplexResidue
import Langlands.AlgebraicGeometry.AffineCechFunctionBaseChange

/-! # Freeness of first function cohomology over an Artinian abelian scheme -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.Algebra
open Langlands.AlgebraicGeometry.AffineCechDeRham
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof (fibreMap)

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [Algebra ℚ R]
  (B : AbelianScheme (Spec (CommRingCat.of R))) (U : Scheme.AffineOpenCover.{u} B.X.left)
  [Finite U.I₀]

local notation "k" => IsLocalRing.ResidueField R

private abbrev residueAbelian := (baseChange (fibreMap (R := CommRingCat.of R) k)).obj B

omit [IsArtinianRing R] [Algebra ℚ R] in
private lemma fibre_inversion_fst : ι[(residueAbelian B).X].left ≫ fibreProjection B.X.hom k =
    fibreProjection B.X.hom k ≫ ι[B.X].left := by
  let b := fibreMap (R := CommRingCat.of R) k
  have eq : (baseChange b).map (-(𝟙 B)) = -(𝟙 (residueAbelian B)) := by
    rw [Functor.map_neg]
    exact congrArg Neg.neg ((baseChange b).map_id B)
  change hom (-(𝟙 (residueAbelian B))) ≫ fibreProjection B.X.hom k =
    fibreProjection B.X.hom k ≫ hom (-(𝟙 B))
  rw [← eq]
  change ((Over.pullback b).map (groupHom (-(𝟙 B))).hom.hom).left ≫ pullback.fst B.X.hom b = _
  exact pullback.lift_fst _ _ _

variable (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ ι[B.X].left ⁻¹ᵁ coverOpens U (β i))
  (hInv : Function.Involutive β)

private abbrev residueCover := fibreAffineCover B.X.hom k U

omit [Finite U.I₀] [IsArtinianRing R] [Algebra ℚ R] in
include hβ in
private lemma residueCover_le_inversion (i : U.I₀) : coverOpens (residueCover B U) i ≤
    ι[(residueAbelian B).X].left ⁻¹ᵁ coverOpens (residueCover B U) (β i) :=
  fibreCover_le_preimage B.X.hom k U ι[B.X].left ι[(residueAbelian B).X].left
    (fibre_inversion_fst B) β hβ i

include hInv in
private def residueSignEquiv (s : R) (hs : s * s = 1) (p : ℕ) :
    k ⊗[R] signedFunctions B U β hβ s p ≃ₗ[k]
    signedFunctions (residueAbelian B) (residueCover B U) β (residueCover_le_inversion B U β hβ)
      (algebraMap R k s) p :=
  involutionPartBaseChange (K := k) _ (functionInversion_involutive B U β hβ hInv p)
    (functionInversion (residueAbelian B) (residueCover B U) β (residueCover_le_inversion B U β hβ) p)
    (functionInversion_involutive (residueAbelian B) (residueCover B U) β
      (residueCover_le_inversion B U β hβ) hInv p) (fibreFunctionCochainEquiv B.X.hom k U p)
    (fibreFunctionCochainEquiv_pullFunctions B.X.hom k U ι[B.X].left (Over.w ι[B.X])
      ι[(residueAbelian B).X].left (Over.w ι[(residueAbelian B).X]) (fibre_inversion_fst B) β hβ p)
    s (half R) hs (half_add_half R)

omit [IsArtinianRing R] in
private lemma residueSignEquiv_d (s : R) (hs : s * s = 1) (p : ℕ)
    (x : k ⊗[R] signedFunctions B U β hβ s p) :
    residueSignEquiv B U β hβ hInv s hs (p + 1) ((signedFunctionD B U β hβ s p).baseChange k x) =
      signedFunctionD (residueAbelian B) (residueCover B U) β (residueCover_le_inversion B U β hβ)
        (algebraMap R k s) p (residueSignEquiv B U β hβ hInv s hs p x) := by
  apply Subtype.ext
  unfold residueSignEquiv
  rw [involutionPartBaseChange_val, involutionPartMap_val, involutionPartBaseChange_val]
  refine .trans ?_ (fibreFunctionCochainEquiv_cechD B.X.hom k U p
    ((signedFunctions B U β hβ s p).subtype.baseChange k x))
  congr 1
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  rfl

omit [IsArtinianRing R] in
include hInv in
private lemma exact_residueSign (s : R) (hs : s * s = 1) (p : ℕ)
    (h : Function.Exact
      (signedFunctionD (residueAbelian B) (residueCover B U) β (residueCover_le_inversion B U β hβ)
        (algebraMap R k s) p)
      (signedFunctionD (residueAbelian B) (residueCover B U) β (residueCover_le_inversion B U β hβ)
        (algebraMap R k s) (p + 1))) :
    Function.Exact ((signedFunctionD B U β hβ s p).baseChange k)
      ((signedFunctionD B U β hβ s (p + 1)).baseChange k) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (h (residueSignEquiv B U β hβ hInv s hs (p + 1) x)).mp (by
      rw [← residueSignEquiv_d, hx, map_zero])
    refine ⟨(residueSignEquiv B U β hβ hInv s hs p).symm y,
      (residueSignEquiv B U β hβ hInv s hs (p + 1)).injective ?_⟩
    rw [residueSignEquiv_d, LinearEquiv.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, signedFunctionD_comp,
      LinearMap.baseChange_zero]
    rfl

omit [IsLocalRing R] [IsArtinianRing R] in
include hInv in
private lemma signedFunctions_flat (s : R) (hs : s * s = 1) (p : ℕ) :
    Module.Flat R (signedFunctions B U β hβ s p) := by
  have := functionCochain_flat B U p
  exact involutionPart_flat _ (functionInversion_involutive B U β hβ hInv p)
    s (half R) hs (half_add_half R)

include hInv in
/-- The positive sign subcomplex is exact in degree one over the Artinian base. -/
theorem signedFunction_even_exact_artinian :
    Function.Exact (signedFunctionD B U β hβ 1 0) (signedFunctionD B U β hβ 1 1) := by
  have (p : ℕ) : Module.Flat R (signedFunctions B U β hβ 1 p) :=
    signedFunctions_flat B U β hβ hInv 1 (one_mul 1) p
  refine exact_of_residue_exact _ _ (signedFunctionD_comp B U β hβ 1 0)
    (exact_residueSign B U β hβ hInv 1 (one_mul 1) 0 ?_)
  rw [map_one]
  exact signedFunction_even_exact_one (residueAbelian B) (residueCover B U)
    β (residueCover_le_inversion B U β hβ) hInv

include hβ hInv in
/-- Every first function cohomology class has an odd function cocycle representative. -/
lemma exists_odd_function_cocycle (z : structureH1 B.X.hom U) :
    ∃ x : structureCocycles B.X.hom U,
      functionInversion B U β hβ 1 x.val = -x.val ∧ (structureBoundaries B.X.hom U).mkQ x = z := by
  let p := structureBoundaries B.X.hom U
  obtain ⟨x, rfl⟩ := p.mkQ_surjective z
  let xm := functionSignProjector B U β hβ hInv (-1) (by simp) 1 x.val
  let xp := functionSignProjector B U β hβ hInv 1 (one_mul 1) 1 x.val
  have hm : cechD U (functions B.X.hom) 1 xm.val = 0 := by
    change (signedFunctionD B U β hβ (-1) 1 (functionSignProjector B U β hβ hInv (-1)
      (by simp) 1 x.val)).val = 0
    rw [functionSignProjector_comm, x.property, map_zero]
    rfl
  have hp : signedFunctionD B U β hβ 1 1 xp = 0 := by
    apply Subtype.ext
    change (signedFunctionD B U β hβ 1 1 (functionSignProjector B U β hβ hInv 1
      (one_mul 1) 1 x.val)).val = 0
    rw [functionSignProjector_comm, x.property, map_zero]
    rfl
  obtain ⟨y, hy⟩ := (signedFunction_even_exact_artinian B U β hβ hInv xp).mp hp
  have hy' : cechD U (functions B.X.hom) 0 y.val = xp.val := congrArg Subtype.val hy
  let w : structureCocycles B.X.hom U := ⟨xm.val, hm⟩
  have hx' : w + structureBoundaryMap B.X.hom U y.val = x := by
    apply Subtype.ext
    change xm.val + cechD U (functions B.X.hom) 0 y.val = x.val
    rw [hy']
    change half R • (x.val + (-1 : R) • functionInversion B U β hβ 1 x.val) +
      half R • (x.val + (1 : R) • functionInversion B U β hβ 1 x.val) = x.val
    rw [one_smul, neg_one_smul, smul_add, smul_add, smul_neg]
    calc
      _ = half R • x.val + half R • x.val := by abel
      _ = x.val := half_smul_add_half_smul (R := R) x.val
  refine ⟨w, ?_, ?_⟩
  · simpa only [neg_one_smul] using mem_involutionPart.mp xm.property
  · change p.mkQ w = p.mkQ x
    have h0 : p.mkQ (structureBoundaryMap B.X.hom U y.val) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr ⟨y.val, rfl⟩
    rw [← hx', map_add, h0, add_zero]

include hβ hInv in
/-- When using an inversion-compatible cover, the function cohomology is free
by the negative sign complex of the residue fibre. -/
theorem structureH1_free_of_inversion_cover : Module.Free R (structureH1 B.X.hom U) := by
  have (p : ℕ) : Module.Flat R (signedFunctions B U β hβ (-1) p) :=
    signedFunctions_flat B U β hβ hInv (-1) (by simp) p
  let d₀ := signedFunctionD B U β hβ (-1) 0
  let d₁ := signedFunctionD B U β hβ (-1) 1
  let d₂ := signedFunctionD B U β hβ (-1) 2
  let j : signedFunctions B U β hβ (-1) 0 →ₗ[R] d₁.ker := d₀.codRestrict d₁.ker (fun x =>
    LinearMap.congr_fun (signedFunctionD_comp B U β hβ (-1) 0) x)
  have hx : Function.Injective (d₀.baseChange k) := by
    let e := residueSignEquiv B U β hβ hInv (-1) (by simp) 0
    intro x y hxy
    apply e.injective
    have h : Function.Injective (signedFunctionD (residueAbelian B) (residueCover B U) β
        (residueCover_le_inversion B U β hβ) (algebraMap R k (-1)) 0) := by
      rw [map_neg, map_one]
      exact signedFunctionD_neg_zero_injective (residueAbelian B)
        (residueCover B U) β (residueCover_le_inversion B U β hβ)
    apply h
    rw [← residueSignEquiv_d, ← residueSignEquiv_d]
    exact congrArg (residueSignEquiv B U β hβ hInv (-1) (by simp) 1) hxy
  have he : Function.Exact (d₁.baseChange k) (d₂.baseChange k) := by
    refine exact_residueSign B U β hβ hInv (-1) (by simp) 1 ?_
    rw [map_neg, map_one]
    exact signedFunction_odd_exact_two (residueAbelian B) (residueCover B U)
      β (residueCover_le_inversion B U β hβ) hInv
  have := free_h1_of_residue d₀ d₁ d₂ (signedFunctionD_comp B U β hβ (-1) 0)
    (signedFunctionD_comp B U β hβ (-1) 1) hx he
  let Z := structureCocycles B.X.hom U
  let I : d₁.ker →ₗ[R] Z := ((signedFunctions B U β hβ (-1) 1).subtype.comp d₁.ker.subtype).codRestrict Z
    (fun z => congrArg Subtype.val z.property)
  let p := structureBoundaries B.X.hom U
  let c : d₁.ker →ₗ[R] structureH1 B.X.hom U := p.mkQ.comp I
  have hker : j.range = c.ker := by
    ext x
    change (∃ y, j y = x) ↔ p.mkQ (I x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, rfl⟩
    · intro hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
      have hy' : cechD U (functions B.X.hom) 0 y = x.val.val := congrArg Subtype.val hy
      refine ⟨functionSignProjector B U β hβ hInv (-1) (by simp) 0 y,
        Subtype.ext (Subtype.ext ?_)⟩
      change (signedFunctionD B U β hβ (-1) 0
        (functionSignProjector B U β hβ hInv (-1) (by simp) 0 y)).val = x.val.val
      rw [functionSignProjector_comm, hy']
      exact congrArg Subtype.val (functionSignProjector_on_part B U β hβ hInv (-1) (by simp) 1 x.val)
  have hc : Function.Surjective c := by
    intro z
    obtain ⟨x, hx, hclass⟩ := exists_odd_function_cocycle B U β hβ hInv z
    have hx' : x.val ∈ signedFunctions B U β hβ (-1) 1 :=
      mem_involutionPart.mpr (by simpa only [neg_one_smul] using hx)
    let w : d₁.ker := ⟨⟨x.val, hx'⟩, Subtype.ext x.property⟩
    exact ⟨w, hclass⟩
  let e := LinearMap.quotKerEquivOfSurjective (R := R) (M := ↥d₁.ker)
    (M₂ := structureH1 B.X.hom U) c hc
  exact Module.Free.of_equiv ((Submodule.quotEquivOfEq _ _ hker).trans e)

/-- The function term of the Hodge sequence on every supplied finite affine cover is free. -/
theorem structureH1_free_artinian : Module.Free R (structureH1 B.X.hom U) := by
  let V := inversionCover B U
  let β := swapChart U ι[B.X].left
  have := structureH1_free_of_inversion_cover B V β
    (doubledCover_le_preimage U ι[B.X].left (inversion_left_sq B))
    (swapChart_swapChart U ι[B.X].left)
  exact Module.Free.of_equiv ((structureH1Equiv B.X.hom V).trans (structureH1Equiv B.X.hom U).symm)

end Langlands.AbelianScheme
