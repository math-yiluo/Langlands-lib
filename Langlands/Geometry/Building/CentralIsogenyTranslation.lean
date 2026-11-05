import Langlands.Geometry.Building.KPApartment
import Langlands.GroupScheme.CentralIsogeny.RootDatumHomConstruction
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterProof

/-! # Reduced translation spaces in a central-isogeny square -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual character restriction and cocharacter postcomposition are adjoint. -/
theorem eval_cocharacterMapReal (t : S ⟶ T) (a : characterLattice T) (v : V S) :
    eval T a (cocharacterMapReal t v) = eval S (t ≫ a) v := by
  rw [eval_eq_pair, eval_eq_pair, pair_cocharacterMapReal]
  rfl

variable [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  (q : C ⟶ G) (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))

/-- The existing actual root bijection, restricted to the relative-root subtypes. -/
def centralIsogenyRootPullbackEquiv : relativeRoots j ≃ relativeRoots i :=
  Set.BijOn.equiv (fun a : characterLattice T => t ≫ a)
    (hq.roots_bijOn_of_torusRestriction hS hT t h ht)

@[simp] theorem centralIsogenyRootPullbackEquiv_coe (a : relativeRoots j) :
    (centralIsogenyRootPullbackEquiv q hq hS hT t h ht a : characterLattice S) =
      t ≫ a.val := rfl

include q hq hS hT h ht

/-- The actual cocharacter map preserves and reflects the common root kernel. -/
theorem cocharacterMapReal_mem_rootAnnihilator_iff (v : V S) :
    cocharacterMapReal t v ∈ rootAnnihilator j ↔ v ∈ rootAnnihilator i := by
  rw [mem_rootAnnihilator, mem_rootAnnihilator]
  have hb := hq.roots_bijOn_of_torusRestriction hS hT t h ht
  constructor
  · intro hv b hbi
    obtain ⟨a, haj, hab⟩ := hb.2.2 hbi
    rw [← hab, ← eval_cocharacterMapReal]
    exact hv a haj
  · intro hv a haj
    rw [eval_cocharacterMapReal]
    exact hv (t ≫ a) (hb.1 haj)

/-- The common root kernels have exactly the same image under the torus map. -/
theorem map_cocharacterMapReal_rootAnnihilator :
    (rootAnnihilator i).map (cocharacterMapReal t) = rootAnnihilator j := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (cocharacterMapReal_mem_rootAnnihilator_iff q hq hS hT t h ht w).mpr hw
  · intro hv
    obtain ⟨w, rfl⟩ :=
      (splitTorusIsogenyCocharacter k S T t hS hT ht).2.2.2.surjective v
    exact ⟨w,
      (cocharacterMapReal_mem_rootAnnihilator_iff q hq hS hT t h ht w).mp hv, rfl⟩

/-- The quotient of the actual real cocharacter isomorphism by the common root kernels. -/
def centralIsogenyTranslationEquiv : TranslationSpace i ≃ₗ[ℝ] TranslationSpace j :=
  Submodule.Quotient.equiv _ _
    (LinearEquiv.ofBijective (cocharacterMapReal t)
      (splitTorusIsogenyCocharacter k S T t hS hT ht).2.2.2)
    (map_cocharacterMapReal_rootAnnihilator q hq hS hT t h ht)

/-- On representatives the equivalence is the original actual torus map. -/
@[simp] theorem centralIsogenyTranslationEquiv_mk (v : V S) :
    centralIsogenyTranslationEquiv q hq hS hT t h ht (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (cocharacterMapReal t v) := rfl

/-- Corresponding actual relative-root forms agree on the reduced translation spaces. -/
theorem rootForm_centralIsogenyTranslationEquiv (a : relativeRoots j)
    (v : TranslationSpace i) :
    rootForm j a (centralIsogenyTranslationEquiv q hq hS hT t h ht v) =
      rootForm i (centralIsogenyRootPullbackEquiv q hq hS hT t h ht a) v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  exact eval_cocharacterMapReal t a.val w

end Langlands.Geometry.Building
