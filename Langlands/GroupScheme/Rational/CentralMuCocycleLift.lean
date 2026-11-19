import Langlands.GroupScheme.Rational.CentralDefectArchimedean

/-! # Global lifting through a central isogeny with roots-of-unity kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- A natural cocycle remains trivial at every place after a refinement of its cover. -/
theorem Cocycle.LocallyTrivial.refine {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {U V : Over (Spec (CommRingCat.of F))}
    {ξ : Cocycle G U} (h : ξ.LocallyTrivial) (r : V ⟶ U) : (ξ.refine r).LocallyTrivial := by
  intro v
  let b := algebraBaseMap F (Global.placeCompletion F v)
  obtain ⟨a, ha⟩ := h v
  refine ⟨(Over.pullback b).map r ≫ a, fun x y => ?_⟩
  rw [Cocycle.baseChange_pullback_refine_toFun, Cocycle.refine_toFun, ha]
  simp only [Category.assoc, b]

namespace IsCentralIsogeny

open Langlands.ClassFieldTheory.Local

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

/-- Coefficient points of a central kernel identified with `μ_n` are the actual roots of unity. -/
def kernelRootsEquiv (n : ℕ) (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)
    (A : Type u) [Field A] [Algebra F A] :
    GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F A) ≃* rootsOfUnity n A :=
  (((yonedaGrp.mapIso e).app (op (GaloisCocycle.cover F A))).groupIsoToMulEquiv).trans
    (mu.affinePointsEquiv n (Spec.algebraMap F A))

theorem kernelRootsEquiv_val (n : ℕ) (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)
    (A : Type u) [Field A] [Algebra F A]
    (x : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F A)) :
    ((hf.kernelRootsEquiv n e A x : rootsOfUnity n A) : Aˣ) =
      hf.kernelUnitMap (e.hom ≫ (mu.incl (Spec (CommRingCat.of F)) n).toMul) A x := by
  let y : Over.mk (Spec.algebraMap F A) ⟶ (mu (Spec (CommRingCat.of F)) n).X := x ≫ e.hom.hom.hom
  change (mu.affinePointsEquiv n (Spec.algebraMap F A) y : (CommRingCat.of A)ˣ) = _
  rw [mu.affinePointsEquiv_val]
  change Gm.affinePointsEquiv (Spec.algebraMap F A)
      ((x ≫ e.hom.hom.hom) ≫ (torsionι (Gm (Spec (CommRingCat.of F))).toGrp n).hom.hom) =
    Gm.affinePointsEquiv (Spec.algebraMap F A)
      (x ≫ (e.hom ≫ (mu.incl (Spec (CommRingCat.of F)) n).toMul).hom.hom)
  rw [Category.assoc, Grp.comp_hom_hom]
  rfl

variable [Normal F L]

private def refineGaloisLift {E : Type u} [Field E] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) :
    hf.GaloisLift (ξ.refine (GaloisCocycle.coverMap F L E)) := by
  let rd := hf.restrictGaloisLift (K := F) (M := E) ξ d
  refine ⟨rd.value, fun σ => ?_, rd.defect, rd.defect_spec⟩
  rw [GaloisCocycle.value_refine]
  exact rd.project σ

variable [NumberField F] [NumberField L] [IsGalois F L]

/-- For a `μ_n` kernel, a locally trivial cocycle with central lift data admits a natural
lift after finite Galois refinement. -/
theorem exists_cocycle_lift_of_mu_kernel_of_galoisLift
    (n : ℕ) (hn : n ≠ 0) (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ)
    (h : ξ.LocallyTrivial) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (_ : Algebra L E) (_ : IsScalarTower F L E)
      (ζ : Cocycle G (GaloisCocycle.cover F E)), ζ.map f = ξ.refine (GaloisCocycle.coverMap F L E) := by
  let χ := e.hom ≫ (mu.incl (Spec (CommRingCat.of F)) n).toMul
  let c := hf.kernelUnitDefect χ d
  have hpow (q : (L ≃ₐ[F] L) × (L ≃ₐ[F] L)) : c q ^ n = 1 := by
    have hx := (hf.kernelRootsEquiv n e L (d.defect q)).property
    apply (mem_rootsOfUnity n (c q)).mp
    rw [show c q = hf.kernelUnitMap χ L (d.defect q) from rfl, ← hf.kernelRootsEquiv_val]
    exact hx
  have hzero := hf.kernelUnitObstruction_eq_zero χ d h
  have hc : IsMulCoboundary₂ c := by
    unfold kernelUnitObstruction relativeUnitsClass₂ at hzero
    obtain ⟨a, ha⟩ := (H2π_eq_zero_iff (A := unitsRepresentation F L) _).mp hzero
    refine ⟨fun σ => (a σ).toMul, fun σ τ => ?_⟩
    have hστ := congrArg (fun z => (z (σ, τ)).toMul) ha
    rw [d₁₂_hom_apply] at hστ
    exact hστ
  obtain ⟨E, _, _, _, _, _, _, a, ha, hprim⟩ :=
    rootsOfUnityPrimitiveAfterRefinement_of_units n hn c hpow hc
  let q (σ : E ≃ₐ[F] E) := (hf.kernelRootsEquiv n e E).symm
    (⟨a σ, (mem_rootsOfUnity n (a σ)).mpr (ha σ)⟩ : rootsOfUnity n E)
  have hq (σ : E ≃ₐ[F] E) : hf.kernelUnitMap χ E (q σ) = a σ := by
    rw [← hf.kernelRootsEquiv_val]
    simp only [q, MulEquiv.apply_symm_apply]
  have hi : Function.Injective (hf.kernelUnitMap χ E) := by
    intro x y hxy
    apply (hf.kernelRootsEquiv n e E).injective
    apply Subtype.ext
    simpa only [hf.kernelRootsEquiv_val] using hxy
  let d' := hf.refineGaloisLift (E := E) d
  have hp : IsMulCoboundary₂ d'.defect := by
    refine ⟨q, fun σ τ => ?_⟩
    apply hi
    have he : hf.kernelUnitMap χ E (σ • q τ) = σ • hf.kernelUnitMap χ E (q τ) :=
      hf.kernelUnitMap_naturality χ σ.toAlgHom (q τ)
    have hd : hf.kernelUnitMap χ E (d'.defect (σ, τ)) =
        Units.map (algebraMap L E) (c (σ.restrictNormal L, τ.restrictNormal L)) :=
      hf.kernelUnitMap_naturality χ (IsScalarTower.toAlgHom F L E) _
    rw [map_mul, map_div, he, hq, hq, hq, hd]
    exact hprim σ τ
  obtain ⟨ζ, hζ⟩ := (hf.galoisLift_isMulCoboundary₂_iff _ d').mp hp
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ζ, hζ⟩

include hf in
omit [Normal F L] in
/-- An everywhere locally trivial cocycle lifts after finite Galois refinement through
a central isogeny with kernel isomorphic to `μ_n`, for positive `n`. -/
theorem exists_cocycle_lift_of_mu_kernel
    (n : ℕ) (hn : n ≠ 0) (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)
    (ξ : Cocycle H (GaloisCocycle.cover F L)) (h : ξ.LocallyTrivial) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra F N) (_ : FiniteDimensional F N) (_ : IsGalois F N)
      (_ : Algebra L N) (_ : IsScalarTower F L N)
      (ζ : Cocycle G (GaloisCocycle.cover F N)), ζ.map f = ξ.refine (GaloisCocycle.coverMap F L N) := by
  obtain ⟨E, _, _, _, _, _, _, ⟨d⟩⟩ := hf.exists_finiteGalois_refine_galoisLift ξ
  let : NumberField E := NumberField.of_module_finite F E
  let r := GaloisCocycle.coverMap F L E
  obtain ⟨N, _, _, _, _, _, _, ζ, hζ⟩ :=
    hf.exists_cocycle_lift_of_mu_kernel_of_galoisLift n hn e d (h.refine r)
  let : Algebra L N := Algebra.compHom N (algebraMap L E)
  let : IsScalarTower L E N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F E N, IsScalarTower.algebraMap_apply L E N,
      ← IsScalarTower.algebraMap_apply F L E]
  let s := GaloisCocycle.coverMap F E N
  have ht : s ≫ r = GaloisCocycle.coverMap F L N := by
    change (algSpec (CommRingCat.of F)).map
          (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E N)).op ≫
        (algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom F L E)).op = _
    rw [← Functor.map_comp]
    rfl
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ζ, hζ.trans ?_⟩
  rw [← ht]
  have hh {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ GaloisCocycle.cover F N) :
      ((ξ.refine r).refine s).toFun a b = (ξ.refine (s ≫ r)).toFun a b := by
    simp only [Cocycle.refine_toFun, Category.assoc]
  generalize ((ξ.refine r).refine s) = ξ₁ at hh ⊢
  generalize (ξ.refine (s ≫ r)) = ξ₂ at hh ⊢
  cases ξ₁
  cases ξ₂
  congr
  funext Z a b
  exact hh a b

end IsCentralIsogeny
end Langlands.GroupScheme
