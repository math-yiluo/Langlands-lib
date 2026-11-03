import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Actual subgroup factorizations from fixed cosets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H K G : GroupScheme S} {Q : Over S}
variable (i : H ⟶ G) (j : K ⟶ G) (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (x y : T ⟶ G.X),
  x ≫ q = y ≫ q ↔ x⁻¹ * y ∈ (SubgroupFunctor.range j).carrier T)
variable (g : Over.mk (𝟙 S) ⟶ G.X)
variable (hfixed : ∀ (T : Over S) (h : T ⟶ H.X),
  ((h ≫ i.hom.hom) * G.constantPoint g T) ≫ q = G.constantPoint g T ≫ q)

include hfib hfixed

/-- A coset fixed by a subgroup on all tests gives the conjugated range
inclusion on all tests. -/
theorem range_conjugate_le_of_fixed_coset :
    SubgroupFunctor.range (i ≫ (G.innerIso g⁻¹).hom) ≤ SubgroupFunctor.range j := by
  intro T x hx
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hmem := (hfib T (G.constantPoint g T)
    ((h ≫ i.hom.hom) * G.constantPoint g T)).mp (hfixed T h).symm
  rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom,
    G.constantPoint_inv, inv_inv]
  simpa only [mul_assoc] using hmem

variable [Mono i.hom.hom] [Mono j.hom.hom]

/-- The actual group-scheme factorization supplied by a fixed coset. -/
def factorOfFixedCoset : H ⟶ K := by
  have : IsIso (G.innerIso g⁻¹).hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget _).mapIso (G.innerIso g⁻¹)).hom)
  have : Mono (i ≫ (G.innerIso g⁻¹).hom).hom.hom := by
    change Mono (i.hom.hom ≫ (G.innerIso g⁻¹).hom.hom.hom)
    infer_instance
  exact SubgroupFunctor.factorOfRangeLE
    (range_conjugate_le_of_fixed_coset i j q hfib g hfixed)

/-- The constructed homomorphism gives the exact conjugated embedding. -/
theorem factorOfFixedCoset_comp :
    factorOfFixedCoset i j q hfib g hfixed ≫ j = i ≫ (G.innerIso g⁻¹).hom := by
  have : IsIso (G.innerIso g⁻¹).hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget _).mapIso (G.innerIso g⁻¹)).hom)
  have : Mono (i ≫ (G.innerIso g⁻¹).hom).hom.hom := by
    change Mono (i.hom.hom ≫ (G.innerIso g⁻¹).hom.hom.hom)
    infer_instance
  exact SubgroupFunctor.factorOfRangeLE_comp
    (range_conjugate_le_of_fixed_coset i j q hfib g hfixed)

end Langlands.GroupScheme
