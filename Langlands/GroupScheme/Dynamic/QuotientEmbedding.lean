import Langlands.GroupScheme.HomogeneousQuotientMonomorphism
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Actual comparison maps between supplied dynamic quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
  (χ : (Gm S).toGrp ⟶ G)
  {Q R : Over S} (q : G.X ⟶ Q) (r : H.X ⟶ R)
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hq : ∀ (T : Over S) (a b : T ⟶ G.X),
    a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (parabolic χ).carrier T)
  (hr : ∀ (T : Over S) (a b : T ⟶ H.X),
    a ≫ r = b ≫ r ↔ a⁻¹ * b ∈ (parabolic (χ ≫ f)).carrier T)

/-- An actual group homomorphism induces a comparison of the supplied
quotients by the corresponding dynamic parabolics. -/
def suppliedQuotientMap : Q ⟶ R :=
  HomogeneousQuotientComparison.desc q (f.hom.hom ≫ r) (fun T a b hab => by
    have hp := parabolic_le_comap χ f T ((hq T a b).mp hab)
    rw [SubgroupFunctor.mem_comap, MonObj.mul_comp, GrpObj.inv_comp] at hp
    simpa only [Category.assoc] using (hr T (a ≫ f.hom.hom) (b ≫ f.hom.hom)).mpr hp)

@[reassoc]
theorem fac_suppliedQuotientMap :
    q ≫ suppliedQuotientMap f χ q r hq hr = f.hom.hom ≫ r :=
  HomogeneousQuotientComparison.fac_desc _ _ _

/-- Compatibility with the original projections characterizes the map. -/
theorem suppliedQuotientMap_unique (d : Q ⟶ R) (hd : q ≫ d = f.hom.hom ≫ r) :
    d = suppliedQuotientMap f χ q r hq hr :=
  HomogeneousQuotientComparison.desc_unique _ _ _ d hd

include χ hq hr in
omit [Flat q.left] [Surjective q.left] [QuasiCompact q.left] in
/-- For a closed subgroup embedding, the two maps out of `G` have precisely
the same fibers on every relative scheme test. -/
theorem suppliedQuotient_fiber_iff (hf : IsClosedSubgroup f)
    (T : Over S) (a b : T ⟶ G.X) :
    a ≫ q = b ≫ q ↔ a ≫ (f.hom.hom ≫ r) = b ≫ (f.hom.hom ≫ r) := by
  rw [hq, parabolic_eq_comap_of_isClosedSubgroup χ f hf,
    SubgroupFunctor.mem_comap, MonObj.mul_comp, GrpObj.inv_comp]
  exact (hr T (a ≫ f.hom.hom) (b ≫ f.hom.hom)).symm

/-- The actual comparison of supplied dynamic quotients along a closed
subgroup embedding is a monomorphism of schemes. -/
theorem mono_suppliedQuotientMap (hf : IsClosedSubgroup f) :
    Mono (suppliedQuotientMap f χ q r hq hr).left := by
  exact HomogeneousQuotientComparison.mono_desc_of_fiber_iff q (f.hom.hom ≫ r)
    (suppliedQuotient_fiber_iff f χ q r hq hr hf)

/-- Closedness of this actual comparison into a proper quotient suffices
for properness of the original supplied quotient. -/
theorem suppliedQuotient_isProper_of_closed_comparison
    [IsProper R.hom] [IsClosedImmersion (suppliedQuotientMap f χ q r hq hr).left] :
    IsProper Q.hom := by
  rw [← Over.w (suppliedQuotientMap f χ q r hq hr)]
  infer_instance

end Langlands.GroupScheme.Dynamic
