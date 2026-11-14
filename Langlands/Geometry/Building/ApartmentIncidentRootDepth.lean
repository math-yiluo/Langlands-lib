import Langlands.Geometry.Building.ChamberFiltration
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-! # Actual depth witnesses for incident ordinary affine roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- An actual depth-`r` root point outside positive depth times the full
doubled-root group. -/
def IsRootDepthBoundary (x : D.Apartment) (a : characterLattice S)
    (r : ℝ) (g : rationalPoints G) : Prop :=
  g ∈ D.filtration x a r ∧
    g ∉ (D.filtrationPlus x a r : Set (rationalPoints G)) *
      (doubleRootGroupPoints i a : Set (rationalPoints G))

variable {D}

theorem IsRootDepthBoundary.not_mem_filtrationPlus
    {x : D.Apartment} {a : characterLattice S} {r : ℝ} {g : rationalPoints G}
    (hg : D.IsRootDepthBoundary x a r g) : g ∉ D.filtrationPlus x a r := by
  intro hplus
  exact hg.2 ⟨g, hplus, 1, (doubleRootGroupPoints i a).one_mem, mul_one g⟩

theorem IsRootDepthBoundary.not_mem_doubleRootGroupPoints
    {x : D.Apartment} {a : characterLattice S} {r : ℝ} {g : rationalPoints G}
    (hg : D.IsRootDepthBoundary x a r g) : g ∉ doubleRootGroupPoints i a := by
  intro hdouble
  exact hg.2 ⟨1, (D.filtrationPlus x a r).one_mem, g, hdouble, one_mul g⟩

theorem IsRootDepthBoundary.ne_one
    {x : D.Apartment} {a : characterLattice S} {r : ℝ} {g : rationalPoints G}
    (hg : D.IsRootDepthBoundary x a r g) : g ≠ 1 := by
  intro hg1
  exact hg.not_mem_filtrationPlus (hg1 ▸ (D.filtrationPlus x a r).one_mem)

/-- The witness has exactly the boundary value, rather than just a lower bound. -/
theorem IsRootDepthBoundary.value_eq
    {x : D.Apartment} {a : characterLattice S} {r : ℝ} {g : rationalPoints G}
    (hg : D.IsRootDepthBoundary x a r g) : x.val a g = (r : WithTop ℝ) := by
  apply le_antisymm
  · exact le_of_not_gt fun hlt =>
      hg.not_mem_filtrationPlus (mem_filtrationPlus.mpr ⟨hg.1.1, hlt⟩)
  · exact hg.1.2

variable (D)

/-- Positive-depth affine indexing agrees with point/depth indexing at
every apartment point with the prescribed derivative. -/
theorem affineRootGroupPlus_eq_filtrationPlus
    {a : relativeRoots i} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hlin : ψ.linear = rootForm i a) (x : D.Apartment) :
    D.affineRootGroupPlus a ψ = D.filtrationPlus x a (ψ x) := by
  ext g
  rw [D.mem_affineRootGroupPlus_iff hlin x, mem_filtrationPlus]

/-- One actual root point witnesses the ordinary affine-root boundary at
every point of the apartment, retaining the full doubled-root exclusion. -/
theorem exists_rootDepthBoundary_of_affineRoot
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.affineRoots) :
    ∃ a : relativeRoots i, ψ.linear = rootForm i a ∧
      ∃ g : rationalPoints G, g ≠ 1 ∧
        ∀ x : D.Apartment, D.IsRootDepthBoundary x a (ψ x) g ∧
          x.val a g = ((ψ x : ℝ) : WithTop ℝ) := by
  obtain ⟨a, hlin, hnot⟩ := hψ
  rw [Set.not_subset] at hnot
  obtain ⟨g, hg, hgn⟩ := hnot
  have hboundary (x : D.Apartment) : D.IsRootDepthBoundary x a (ψ x) g := by
    refine ⟨?_, ?_⟩
    · rwa [← D.affineRootGroup_eq_filtration hlin x]
    · rwa [← D.affineRootGroupPlus_eq_filtrationPlus hlin x]
  let x : D.Apartment := Classical.arbitrary _
  exact ⟨a, hlin, g, (hboundary x).ne_one,
    fun y => ⟨hboundary y, (hboundary y).value_eq⟩⟩

/-- A supplied boundary point produces an ordinary affine root with the
same actual derivative and prescribed value. -/
theorem affineFunctional_mem_affineRoots_of_rootDepthBoundary
    {x : D.Apartment} {a : relativeRoots i} {r : ℝ} {g : rationalPoints G}
    (hg : D.IsRootDepthBoundary x a r g) :
    D.affineFunctional a x r ∈ D.affineRoots := by
  refine ⟨a, rfl, ?_⟩
  rw [← D.filtration_eq_affineRootGroup a x r,
    ← D.filtrationPlus_eq_affineRootGroupPlus a x r]
  exact fun hsub => hg.2 (hsub hg.1)

/-- At a split torus, the specified actual derivative identifies the
relative root, so ordinary-root membership is exactly boundary existence. -/
theorem affineFunctional_mem_affineRoots_iff_exists_rootDepthBoundary
    (hS : IsSplitTorus S.toGrp) (x : D.Apartment) (a : relativeRoots i) (r : ℝ) :
    D.affineFunctional a x r ∈ D.affineRoots ↔
      ∃ g : rationalPoints G, D.IsRootDepthBoundary x a r g := by
  constructor
  · intro hψ
    obtain ⟨b, hlin, g, -, hg⟩ := D.exists_rootDepthBoundary_of_affineRoot hψ
    have hba : b = a :=
      Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split hS i hlin.symm
    subst b
    exact ⟨g, by simpa using (hg x).1⟩
  · rintro ⟨g, hg⟩
    exact D.affineFunctional_mem_affineRoots_of_rootDepthBoundary hg

/-- An incident ordinary affine root supplies one nonidentity root point
with exact value zero and doubled-root boundary exclusion on the full facet. -/
theorem exists_rootDepthBoundary_of_incidentAffineRoot
    {x : D.Apartment} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ D.affineRoots) (hx : ψ x = 0) :
    ∃ a : relativeRoots i, ψ.linear = rootForm i a ∧
      ∃ g : rationalPoints G, g ≠ 1 ∧
        ∀ y ∈ AffineRootSystem.facet D.affineRoots x,
          D.IsRootDepthBoundary y a 0 g ∧ y.val a g = 0 := by
  obtain ⟨a, hlin, g, hg1, hg⟩ := D.exists_rootDepthBoundary_of_affineRoot hψ
  refine ⟨a, hlin, g, hg1, fun y hy => ?_⟩
  have hyzero : ψ y = 0 := by
    have hs := hy ψ hψ
    rw [hx, sign_zero] at hs
    exact sign_eq_zero_iff.mp hs.symm
  simpa only [hyzero, WithTop.coe_zero] using hg y

end Langlands.Geometry.Building.KPApartmentData
