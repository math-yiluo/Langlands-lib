import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.GaloisCocycleConstruction
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupTheory.CentralCocycleLifting

/-! # The finite Galois obstruction for a central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

set_option backward.isDefEq.respectTransparency false

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

/-- The actual scheme-theoretic kernel of a central isogeny, with its commutative group law. -/
def commutativeKernel : CommGroupScheme (Spec (CommRingCat.of k)) :=
  hf.isCentral_kernelι.commGroupScheme

/-- The inclusion on coefficient points of the actual commutative kernel. -/
abbrev kernelPointInclusion (L : Type u) [Field L] [Algebra k L] :
    GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of k L) →*
      G.affinePoints (CommAlgCat.of k L) :=
  GroupScheme.affinePointsTarget hf.commutativeKernel.toGrp (kernelι f) (CommAlgCat.of k L)

/-- Coefficient lifts and their central defect for a natural cocycle. -/
abbrev GaloisLift (ξ : Cocycle H (GaloisCocycle.cover k L)) :=
  CentralCocycleLift (hf.kernelPointInclusion L) (G.affinePointsTarget f (CommAlgCat.of k L))
    (GaloisCocycle.value ξ)

private theorem kernelPointInclusion_injective : Function.Injective (hf.kernelPointInclusion L) :=
  fun _ _ h => (cancel_mono (kernelι f).hom.hom).mp h

private theorem kernelPointInclusion_commute
    (a : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of k L))
    (b : G.affinePoints (CommAlgCat.of k L)) : Commute (hf.kernelPointInclusion L a) b :=
  commute_of_mem_center (hf.isCentral_kernelι _ a) b

private theorem kernelPointInclusion_smul (σ : L ≃ₐ[k] L)
    (a : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of k L)) :
    hf.kernelPointInclusion L (σ • a) = σ • hf.kernelPointInclusion L a := by
  change (GaloisCocycle.arrow k L σ ≫ a) ≫ (kernelι f).hom.hom =
    GaloisCocycle.arrow k L σ ≫ a ≫ (kernelι f).hom.hom
  exact Category.assoc _ _ _

private theorem project_smul (σ : L ≃ₐ[k] L) (b : G.affinePoints (CommAlgCat.of k L)) :
    G.affinePointsTarget f (CommAlgCat.of k L) (σ • b) =
      σ • G.affinePointsTarget f (CommAlgCat.of k L) b := by
  change (GaloisCocycle.arrow k L σ ≫ b) ≫ f.hom.hom =
    GaloisCocycle.arrow k L σ ≫ b ≫ f.hom.hom
  exact Category.assoc _ _ _

private theorem project_eq_one_iff (b : G.affinePoints (CommAlgCat.of k L)) :
    G.affinePointsTarget f (CommAlgCat.of k L) b = 1 ↔
      ∃ a, hf.kernelPointInclusion L a = b :=
  (mem_range_kernelι_iff f b).symm

/-- Pointwise lifts of all Galois values determine a central multiplication defect. -/
theorem nonempty_galoisLift (ξ : Cocycle H (GaloisCocycle.cover k L))
    (h : ∀ σ, ∃ b : G.affinePoints (CommAlgCat.of k L),
      G.affinePointsTarget f (CommAlgCat.of k L) b = GaloisCocycle.value ξ σ) :
    Nonempty (hf.GaloisLift ξ) := by
  choose b hb using h
  exact CentralCocycleLift.nonempty_of_lifts (project_smul (f := f)) hf.project_eq_one_iff
    (GaloisCocycle.value_mul ξ) b hb

/-- The defect has the degree-two cocycle law in the actual kernel points. -/
theorem galoisLift_isMulCocycle₂ (ξ : Cocycle H (GaloisCocycle.cover k L)) (d : hf.GaloisLift ξ) :
    IsMulCocycle₂ d.defect :=
  d.defect_isMulCocycle₂ hf.kernelPointInclusion_commute hf.kernelPointInclusion_smul
    hf.kernelPointInclusion_injective

variable [FiniteDimensional k L] [IsGalois k L]

private theorem cocycle_eq_of_values_eq {K : GroupScheme (Spec (CommRingCat.of k))}
    {a b : Cocycle K (GaloisCocycle.cover k L)}
    (h : ∀ σ, GaloisCocycle.value a σ = GaloisCocycle.value b σ) : a = b := by
  have hab {Z : Over (Spec (CommRingCat.of k))} (x y : Z ⟶ GaloisCocycle.cover k L) :
      a.toFun x y = b.toFun x y := GaloisCocycle.toFun_eq_of_value_eq a b h x y
  cases a
  cases b
  congr
  funext Z x y
  exact hab x y

/-- The central defect is a coboundary exactly when the entire natural cocycle lifts. -/
theorem galoisLift_isMulCoboundary₂_iff (ξ : Cocycle H (GaloisCocycle.cover k L))
    (d : hf.GaloisLift ξ) : IsMulCoboundary₂ d.defect ↔
      ∃ b : Cocycle G (GaloisCocycle.cover k L), b.map f = ξ := by
  constructor
  · intro hd
    obtain ⟨b, hb, hc⟩ := d.exists_cocycle_lift_of_isMulCoboundary₂
      hf.kernelPointInclusion_commute hf.kernelPointInclusion_smul
      (fun a => (hf.project_eq_one_iff _).mpr ⟨a, rfl⟩) hd
    refine ⟨GaloisCocycle.ofValues b hc, cocycle_eq_of_values_eq fun σ => ?_⟩
    change G.affinePointsTarget f (CommAlgCat.of k L)
      (GaloisCocycle.value (GaloisCocycle.ofValues b hc) σ) = _
    rw [GaloisCocycle.value_ofValues, hb]
  · rintro ⟨b, hb⟩
    apply d.isMulCoboundary₂_of_cocycle_lift hf.kernelPointInclusion_commute
      hf.kernelPointInclusion_smul hf.kernelPointInclusion_injective hf.project_eq_one_iff
      (GaloisCocycle.value b) ?_ (GaloisCocycle.value_mul b)
    intro σ
    exact congrArg (fun z => GaloisCocycle.value z σ) hb

end Langlands.GroupScheme.IsCentralIsogeny
