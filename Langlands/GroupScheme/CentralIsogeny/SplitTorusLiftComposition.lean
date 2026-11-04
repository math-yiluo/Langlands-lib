import Langlands.GroupScheme.CentralIsogeny.SplitTorusLiftStatement
import Langlands.GroupScheme.CentralIsogeny.SplitParametrization
import Langlands.GroupScheme.CentralIsogeny.PowerLift
import Langlands.GroupScheme.Torus.FiniteHomMaximalityReduction
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.SplitMultiplication

/-! # Composition from a surjective split parametrization -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A closed split torus that admits a surjective split parametrization lifts
to a split maximal torus when the target torus is maximal. -/
theorem exists_splitMaximalTorus_lift_of_surjective_splitParametrization
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (π : G ⟶ H) (hπ : IsCentralIsogeny π)
    {D S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : D.toGrp ⟶ G) (b : D ⟶ S) (i : S.toGrp ⟶ H)
    (hD : IsSplitTorus D.toGrp) (hi : IsMaximalTorus i)
    (hb : Surjective (CommGroupScheme.groupHom b).hom.hom.left)
    (hcomm : a ≫ π = CommGroupScheme.groupHom b ≫ i) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (f : T ⟶ S),
      IsSplitTorus T.toGrp ∧ IsMaximalTorus j ∧
        j ≫ π = CommGroupScheme.groupHom f ≫ i := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨T, j, f, hj, hsurj, hfac⟩ :=
    exists_splitSubtorus_lift_of_surjective_splitParametrization
      π a b i hD hi.2.1 hb hcomm
  refine ⟨T, j, f, hj.1, ?_, hfac⟩
  exact finiteHomMaximalTorusReflection_of_torusImage
    torusImageClosedTorusStatement k G H hG hH π hπ.isFinite T S j i f
    hj.1.isTorus hj.2 hi hsurj hfac

/-- A parametrization input: a map from the given
split torus to the source covering a surjective endomorphism of that torus. -/
def CentralIsogenySplitParametrizationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (π : G ⟶ H), IsCentralIsogeny π →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ H),
      IsSplitTorus S.toGrp → IsClosedSubgroup i →
      ∃ (a : S.toGrp ⟶ G) (b : S ⟶ S),
        Surjective (CommGroupScheme.groupHom b).hom.hom.left ∧
          a ≫ π = CommGroupScheme.groupHom b ≫ i

/-- The weak parametrization input suffices for the exact maximal-torus target. -/
theorem splitMaximalTorusLift_of_splitParametrization
    (hparam : CentralIsogenySplitParametrizationStatement.{u}) :
    CentralIsogenySplitMaximalTorusLiftStatement.{u} := by
  intro k _ G H hG hH π hπ S i hS hi
  obtain ⟨a, b, hb, hcomm⟩ := hparam k G H hG hH π hπ S i hS hi.2.1
  exact exists_splitMaximalTorus_lift_of_surjective_splitParametrization
    hG hH π hπ a b i hS hi hb hcomm

/-- A positive uniform exponent for the full kernel supplies the parametrization
by descending the `2 * N`-th power map and using surjectivity of split multiplication. -/
theorem exists_splitParametrization_of_kernel_pow_eq_one
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {π : G ⟶ H} (hπ : IsCentralIsogeny π)
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ H) (hS : IsSplitTorus S.toGrp)
    {N : ℕ} (hN0 : 0 < N)
    (hN : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ (kernel π).X),
      x ^ N = 1) :
    ∃ (a : S.toGrp ⟶ G) (b : S ⟶ S),
      Surjective (CommGroupScheme.groupHom b).hom.hom.left ∧
        a ≫ π = CommGroupScheme.groupHom b ≫ i := by
  obtain ⟨a, ha⟩ := hπ.exists_comp_eq_multiplication_comp i hN
  let b : S ⟶ S := Additive.ofMul (multiplication S.toGrp (2 * N : ℕ))
  have hb : Surjective (CommGroupScheme.groupHom b).hom.hom.left :=
    (hS.flat_and_surjective_multiplication (by omega)).2
  exact ⟨a, b, hb, ha⟩

/-- The exact lift target follows from a positive uniform exponent for the full
kernel of each central isogeny. This reduction keeps that input explicit. -/
theorem splitMaximalTorusLift_of_kernel_exponent
    (hExponent : ∀ (k : Type u) [Field k]
      (G H : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → IsConnectedReductive H →
      ∀ (π : G ⟶ H), IsCentralIsogeny π →
        ∃ N : ℕ, 0 < N ∧
          ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ (kernel π).X), x ^ N = 1) :
    CentralIsogenySplitMaximalTorusLiftStatement.{u} := by
  apply splitMaximalTorusLift_of_splitParametrization
  intro k _ G H hG hH π hπ S i hS _
  obtain ⟨N, hN0, hN⟩ := hExponent k G H hG hH π hπ
  exact exists_splitParametrization_of_kernel_pow_eq_one hπ i hS hN0 hN

end Langlands.GroupScheme
