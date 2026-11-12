import Langlands.GroupScheme.Derived.AnnihilationStatement
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly

/-! # Proof: commutative targets annihilate the derived subgroup after scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- After any scalar extension, an actual derived inclusion is again an actual derived
inclusion: its formation commutes with every affine change of base from a field. -/
theorem IsDerivedSubgroup.baseChange_algebra {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) (R : Type u) [CommRing R] [Algebra k R] :
    IsDerivedSubgroup ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).map d) :=
  hd.baseChange_of_eq _ (derivedSubgroup_baseChange_eq_of_field _ G)

/-- Milne 6.19(d), homomorphism form. -/
theorem derivedCommutativeAnnihilation : DerivedCommutativeAnnihilationStatement.{u} := by
  intro k _ G D _ _ d hd H _ _ R _ _ b f
  have : IsAffineHom ((CommGroupScheme.baseChange b).obj H).X.hom := by
    change IsAffineHom (Limits.pullback.snd H.X.hom b)
    infer_instance
  exact (hd.baseChange_algebra R).comp_eq_one f

end Langlands.GroupScheme
