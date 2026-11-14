import Langlands.Geometry.Building.AffineRootDoubling
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.Geometry.Building.AffineTransitiveRootLengths
import Langlands.Geometry.Building.ChamberExchange
import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Actual apartment roots when the relative roots are reduced -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Geometry.Building.KPApartmentData

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)
  (hNo2 : ∀ a ∈ relativeRoots i, (2 : ℕ) • a ∉ relativeRoots i)

include hNo2

/-- If no relative root is doubled, every actual filtration jump is an
ordinary affine root. -/
theorem affineRoots_eq_extendedAffineRoots_of_no_double :
    D.affineRoots = D.extendedAffineRoots := by
  apply Set.Subset.antisymm D.affineRoots_subset_extendedAffineRoots
  rintro ψ ⟨a, hlin, hjump⟩
  exact D.mem_affineRoots_of_not_double_root (hNo2 a a.property) hlin hjump

/-- V0 supplies a filtration jump in every relative-root direction. If
relative roots have no doubles, all those jumps are ordinary roots. -/
theorem derivativeRoots_affineRoots_of_no_double :
    derivativeRoots D.affineRoots = Set.range (rootForm i) := by
  rw [D.affineRoots_eq_extendedAffineRoots_of_no_double hNo2]
  apply Set.Subset.antisymm
  · rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
    exact ⟨a, hlin.symm⟩
  · rintro f ⟨a, rfl⟩
    let x : D.Apartment := Classical.arbitrary D.Apartment
    obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hgtop
    exact ⟨D.affineFunctional a x r,
      D.affineFunctional_mem_extendedAffineRoots hg hr.symm, rfl⟩

variable (hS : IsSplitTorus S.toGrp)

include hS

/-- No actual affine root is twice another if the relative roots have no
doubles. This uses faithfulness of character evaluation on a split torus. -/
theorem isReduced_affineRoots_of_no_double :
    AffineRootSystem.IsReduced D.affineRoots := by
  rintro ψ ⟨a, ha, _⟩ ⟨b, hb, _⟩
  have hab : b.val = (2 : ℕ) • a.val := by
    apply eval_injective hS
    apply LinearMap.ext
    intro v
    have h := congrArg (fun f : Module.Dual ℝ (TranslationSpace i) =>
      f (Submodule.Quotient.mk v)) hb
    simpa only [AffineMap.smul_linear, ha, LinearMap.smul_apply,
      rootForm_mk, smul_eq_mul, eval_nsmul_char, Nat.cast_ofNat] using h.symm
  exact hNo2 a a.property (hab ▸ b.property)

/-- Every actual affine root is indivisible when the relative roots have no
doubles. -/
theorem nonDivisibleRoots_affineRoots_of_no_double :
    nonDivisibleRoots D.affineRoots = D.affineRoots := by
  apply Set.Subset.antisymm (nonDivisibleRoots_subset _)
  intro ψ hψ
  refine ⟨hψ, fun hh => ?_⟩
  have h := D.isReduced_affineRoots_of_no_double hNo2 hS _ hh
  apply h
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
    using hψ

/-- In particular all full derivative roots have indivisible affine lifts. -/
theorem hasIndivisibleDerivativeLifts_of_no_double :
    HasIndivisibleDerivativeLifts D.affineRoots := by
  rintro ⟨a, ψ, hψ, hlin⟩
  exact ⟨ψ, (D.nonDivisibleRoots_affineRoots_of_no_double hNo2 hS).symm ▸ hψ, hlin⟩

/-- The actual relative roots and all ordinary affine derivatives have the
same indices when the relative roots have no doubles. -/
def relativeRootDerivativeEquivOfNoDouble :
    relativeRoots i ≃ derivativeRoots D.affineRoots :=
  Equiv.ofBijective
    (fun a => ⟨rootForm i a,
      (D.derivativeRoots_affineRoots_of_no_double hNo2).symm ▸ Set.mem_range_self a⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply eval_injective hS
      apply LinearMap.ext
      intro v
      exact congrArg (fun f : derivativeRoots D.affineRoots =>
        f.val (Submodule.Quotient.mk v)) hab,
      by
      intro a
      obtain ⟨b, hb⟩ : ∃ b : relativeRoots i, rootForm i b = a.val := by
        rw [← Set.mem_range, ← D.derivativeRoots_affineRoots_of_no_double hNo2]
        exact a.property
      exact ⟨b, Subtype.ext hb⟩⟩

@[simp] theorem relativeRootDerivativeEquivOfNoDouble_val (a : relativeRoots i) :
    (D.relativeRootDerivativeEquivOfNoDouble hNo2 hS a).val = rootForm i a :=
  rfl

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {J : Type*}
  {P : RootDatum J (characterLattice S) (cocharacterLattice S)}

/-- A reduced actual integral root datum rules out doubled relative roots. -/
theorem IsRootDatumOf.two_nsmul_not_mem_relativeRoots
    (hP : IsRootDatumOf i P) (hS : IsSplitTorus S.toGrp) [P.IsReduced]
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    (2 : ℕ) • a ∉ relativeRoots i := by
  let : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice S) := IsAddTorsionFree.of_module_rat _
  let : IsAddTorsionFree (characterLattice S) :=
    hS.character_toRat_injective.isAddTorsionFree Langlands.LinearAlgebra.RationalSpan.toRat
  change a ∈ roots i at ha
  change (2 : ℕ) • a ∉ roots i
  rw [← hP.2.1] at ha ⊢
  obtain ⟨j, rfl⟩ := ha
  exact P.nsmul_notMem_range_root (n := 2)

end Langlands.GroupScheme
