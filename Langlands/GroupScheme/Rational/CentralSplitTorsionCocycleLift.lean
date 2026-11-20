import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Rational.CentralMuCocycleLift
import Langlands.GroupScheme.Rational.CentralWeilTorsionCocycleLift

/-! # Finite Galois lifting through a finite product of roots-of-unity groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry groupCohomology Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section UnitFamilies

variable {F L I : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [Finite I]

/-- A finite family of units has roots of its prescribed positive exponents on
one finite Galois refinement. -/
theorem exists_finiteGalois_unit_roots_family [CharZero F] (n : I → ℕ) (hn : ∀ i, 0 < n i)
    (x : I → Lˣ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (_ : Algebra L E) (_ : IsScalarTower F L E) (y : I → Eˣ),
      ∀ i, y i ^ n i = Units.map (algebraMap L E).toMonoidHom (x i) := by
  let Ω := AlgebraicClosure L
  have hroot (i : I) : ∃ r : Ω, r ^ n i = algebraMap L Ω (x i : L) :=
    IsAlgClosed.exists_pow_nat_eq _ (hn i)
  choose r hr using hroot
  let D := IntermediateField.adjoin L (Set.range r)
  let : FiniteDimensional L D :=
    IntermediateField.finiteDimensional_adjoin fun a _ => Algebra.IsIntegral.isIntegral a
  let : FiniteDimensional F D := FiniteDimensional.trans F L D
  let z (i : I) : D := ⟨r i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  have hz (i : I) : z i ^ n i = algebraMap L D (x i : L) := Subtype.ext (hr i)
  obtain ⟨E, hfin, hgal, ⟨j⟩⟩ := exists_finite_galois_algHom F D
  let iL := j.comp (IsScalarTower.toAlgHom F L D)
  let : Algebra L E := iL.toRingHom.toAlgebra
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun a => (iL.commutes a).symm
  have hy (i : I) : j (z i) ^ n i = algebraMap L E (x i : L) := by rw [← map_pow, hz]; rfl
  have hy₀ (i : I) : j (z i) ≠ 0 := by
    intro h
    have hzero := hy i
    rw [h, zero_pow (hn i).ne'] at hzero
    exact (x i).ne_zero ((algebraMap L E).injective (hzero.symm.trans (map_zero _).symm))
  exact ⟨E, inferInstance, inferInstance, hfin, hgal, inferInstance, inferInstance,
    fun i => Units.mk0 (j (z i)) (hy₀ i), fun i => Units.ext (hy i)⟩

/-- A family of unit primitives for finite-order defects has finite-order primitives
on one common finite Galois refinement. -/
theorem exists_rootsOfUnityPrimitive_family [CharZero F] [IsGalois F L]
    (n : I → ℕ) (hn : ∀ i, 0 < n i) (c : I → Gal(L/F) × Gal(L/F) → Lˣ)
    (hpow : ∀ i q, c i q ^ n i = 1) (hc : ∀ i, IsMulCoboundary₂ (c i)) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (_ : Algebra L E) (_ : IsScalarTower F L E) (a : I → Gal(E/F) → Eˣ),
      (∀ i σ, a i σ ^ n i = 1) ∧ ∀ i σ τ,
        (σ • a i τ) / a i (σ * τ) * a i σ =
          Units.map (algebraMap L E).toMonoidHom (c i (σ.restrictNormal L, τ.restrictNormal L)) := by
  choose b hb using hc
  have hcross (i : I) : IsMulCocycle₁ (fun σ => b i σ ^ n i) := by
    intro σ τ
    have h := congrArg (· ^ n i) (hb i σ τ)
    rw [hpow, mul_pow, div_pow, ← smul_pow', div_mul_eq_mul_div] at h
    exact (div_eq_one.mp h).symm
  have hrad (i : I) : IsMulCoboundary₁ (fun σ => b i σ ^ n i) :=
    isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ (hcross i)
  choose z hz using hrad
  obtain ⟨E, _, _, _, _, _, _, y, hy⟩ := exists_finiteGalois_unit_roots_family (F := F) n hn z
  let j := Units.map (algebraMap L E).toMonoidHom
  let ρ : Gal(E/F) →* Gal(L/F) := AlgEquiv.restrictNormalHom L
  let B (i : I) (σ : Gal(E/F)) := j (b i (ρ σ))
  let D (i : I) (σ : Gal(E/F)) := σ • y i / y i
  have hmap (σ : Gal(E/F)) (a : Lˣ) : σ • j a = j (ρ σ • a) :=
    Units.ext (σ.restrictNormal_commutes L (a : L)).symm
  have hB (i : I) (σ τ : Gal(E/F)) :
      σ • B i τ / B i (σ * τ) * B i σ = j (c i (ρ σ, ρ τ)) := by
    dsimp only [B]
    rw [hmap, map_mul ρ, ← _root_.map_div, ← map_mul, hb]
  have hD (i : I) (σ τ : Gal(E/F)) : D i (σ * τ) = σ • D i τ * D i σ := by
    dsimp only [D]
    rw [mul_smul, smul_div', div_mul_div_cancel]
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, fun i σ => B i σ / D i σ, ?_, ?_⟩
  · intro i σ
    dsimp only [D, B]
    rw [div_pow, div_pow, ← smul_pow', hy, hmap, ← _root_.map_div, hz, map_pow, div_self']
  · intro i σ τ
    rw [smul_div', div_div_div_comm, div_mul_div_comm, hB, hD, div_mul_eq_mul_div,
      div_self', div_one]
    rfl

end UnitFamilies

/-- A finite split product of the given roots-of-unity groups. -/
abbrev splitRootsOfUnityProduct (F : Type u) [Field F] {I : Type u} [Finite I] (n : I → ℕ) :
    GroupScheme (Spec (CommRingCat.of F)) :=
  pi fun i => (mu (Spec (CommRingCat.of F)) (n i)).toGrp

namespace IsCentralIsogeny

open Langlands.ClassFieldTheory.Local

variable {F I : Type u} [Field F] [Finite I] {G H : GroupScheme (Spec (CommRingCat.of F))}
  {f : G ⟶ H} (hf : IsCentralIsogeny f) (n : I → ℕ)
  (e : kernel f ≅ splitRootsOfUnityProduct F n)

local notation "S" => Spec (CommRingCat.of F)
local notation "U" => (fun i : I => CommGroupScheme.toGrp (mu S (n i)))

/-- The character of the kernel coming from one coordinate of the split model. -/
abbrev splitRootsKernelCharacter (i : I) : kernel f ⟶ (Gm S).toGrp :=
  e.hom ≫ Pi.π U i ≫ (mu.incl S (n i)).toMul

/-- The actual coefficient points of a split torsion kernel are coordinate families of roots. -/
def kernelSplitRootsEquiv (R : Type u) [Field R] [Algebra F R] :
    GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F R) ≃*
      ((i : I) → rootsOfUnity (n i) R) :=
  (((yonedaGrp.mapIso e).app (op (GaloisCocycle.cover F R))).groupIsoToMulEquiv).trans
    ((piPointsEquiv U (GaloisCocycle.cover F R)).trans
      (MulEquiv.piCongrRight fun i => mu.affinePointsEquiv (n i) (Spec.algebraMap F R)))

theorem kernelSplitRootsEquiv_val (R : Type u) [Field R] [Algebra F R]
    (x : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F R)) (i : I) :
    (hf.kernelSplitRootsEquiv n e R x i).val =
      hf.kernelUnitMap (splitRootsKernelCharacter n e i) R x := by
  change (mu.affinePointsEquiv (n i) (Spec.algebraMap F R)
    ((x ≫ e.hom.hom.hom) ≫ (Pi.π U i).hom.hom)).val = _
  rw [mu.affinePointsEquiv_val]
  change Gm.affinePointsEquiv (Spec.algebraMap F R)
    (((x ≫ e.hom.hom.hom) ≫ (Pi.π U i).hom.hom) ≫ (mu.incl S (n i)).toMul.hom.hom) =
      Gm.affinePointsEquiv (Spec.algebraMap F R) (x ≫ (splitRootsKernelCharacter n e i).hom.hom)
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, Category.assoc, Category.assoc]

theorem kernelUnitMap_splitRoots_symm (R : Type u) [Field R] [Algebra F R]
    (x : (i : I) → rootsOfUnity (n i) R) (i : I) :
    hf.kernelUnitMap (splitRootsKernelCharacter n e i) R ((hf.kernelSplitRootsEquiv n e R).symm x) =
      (x i).val := by
  rw [← hf.kernelSplitRootsEquiv_val n e, MulEquiv.apply_symm_apply]

theorem kernelUnitMap_splitRoots_jointly_injective (R : Type u) [Field R] [Algebra F R]
    {x y : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F R)}
    (h : ∀ i, hf.kernelUnitMap (splitRootsKernelCharacter n e i) R x =
      hf.kernelUnitMap (splitRootsKernelCharacter n e i) R y) : x = y := by
  apply (hf.kernelSplitRootsEquiv n e R).injective
  funext i
  apply Subtype.ext
  simpa only [hf.kernelSplitRootsEquiv_val n e] using h i

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  [NumberField F]

include e in
private theorem lifts_of_splitRoots_galoisLift [NumberField L] (hn : ∀ i, 0 < n i)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) (h : ξ.LocallyTrivial) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  let χ (i : I) := splitRootsKernelCharacter n e i
  let c (i : I) := hf.kernelUnitDefect (χ i) d
  have hpow (i : I) (p : Gal(L/F) × Gal(L/F)) : c i p ^ n i = 1 := by
    change hf.kernelUnitMap (χ i) L (d.defect p) ^ n i = 1
    rw [← hf.kernelSplitRootsEquiv_val n e]
    exact (mem_rootsOfUnity (n i) _).mp (hf.kernelSplitRootsEquiv n e L (d.defect p) i).property
  have hc (i : I) : IsMulCoboundary₂ (c i) := by
    have hzero := hf.kernelUnitObstruction_eq_zero (χ i) d h
    unfold kernelUnitObstruction relativeUnitsClass₂ at hzero
    obtain ⟨a, ha⟩ := (H2π_eq_zero_iff (A := unitsRepresentation F L) _).mp hzero
    refine ⟨fun σ => (a σ).toMul, fun σ τ => ?_⟩
    have hστ := congrArg (fun q => (q (σ, τ)).toMul) ha
    rw [d₁₂_hom_apply] at hστ
    exact hστ
  obtain ⟨E, _, _, _, _, _, _, a, ha, hδ⟩ := exists_rootsOfUnityPrimitive_family n hn c hpow hc
  let r := GaloisCocycle.coverMap F L E
  let rd := hf.restrictGaloisLift (K := F) (M := E) ξ d
  let d' : hf.GaloisLift (ξ.refine r) :=
    ⟨rd.value, fun σ => by rw [GaloisCocycle.value_refine]; exact rd.project σ,
      rd.defect, rd.defect_spec⟩
  let p (σ : Gal(E/F)) := (hf.kernelSplitRootsEquiv n e E).symm
    (fun i => ⟨a i σ, (mem_rootsOfUnity (n i) _).mpr (ha i σ)⟩)
  have hprim : IsMulCoboundary₂ d'.defect := by
    refine ⟨p, fun σ τ => hf.kernelUnitMap_splitRoots_jointly_injective n e E (fun i => ?_)⟩
    let j := hf.kernelUnitMap (χ i) E
    have hp (υ : Gal(E/F)) : j (p υ) = a i υ := hf.kernelUnitMap_splitRoots_symm n e E _ i
    have hact : j (σ • p τ) = σ • j (p τ) := hf.kernelUnitMap_naturality (χ i) σ.toAlgHom (p τ)
    have hr : j (d'.defect (σ, τ)) = Units.map (algebraMap L E).toMonoidHom
        (c i (σ.restrictNormal L, τ.restrictNormal L)) :=
      hf.kernelUnitMap_naturality (χ i) (IsScalarTower.toAlgHom F L E) _
    change j ((σ • p τ) / p (σ * τ) * p σ) = j (d'.defect (σ, τ))
    rw [map_mul, map_div, hact, hp, hp, hp, hr]
    exact hδ i σ τ
  obtain ⟨ζ, hζ⟩ := (hf.galoisLift_isMulCoboundary₂_iff _ d').mp hprim
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ζ, hζ⟩

include e hf in
/-- A locally trivial target cocycle lifts through a split product of roots-of-unity
kernels on one finite Galois refinement. -/
theorem liftsAfterFiniteGaloisRefinement_of_splitRootsKernel
    (hn : ∀ i, 0 < n i) (ξ : Cocycle H (GaloisCocycle.cover F L)) (h : ξ.LocallyTrivial) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  obtain ⟨E, _, _, _, _, _, _, ⟨d⟩⟩ := hf.exists_finiteGalois_refine_galoisLift ξ
  let : NumberField E := NumberField.of_module_finite F E
  exact (hf.lifts_of_splitRoots_galoisLift n e hn d (h.refine (GaloisCocycle.coverMap F L E))).of_refinement

end IsCentralIsogeny

end Langlands.GroupScheme
