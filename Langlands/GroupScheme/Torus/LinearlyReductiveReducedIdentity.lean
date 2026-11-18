import Langlands.GroupScheme.Absolute.NoUnipotentSubgroupTorusProof
import Langlands.GroupScheme.Dynamic.BaseConnectedProof
import Langlands.GroupScheme.FiniteTypeIdentityComponent
import Langlands.GroupScheme.Torus.LinearlyReductiveUnipotentSubgroups
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.NagataReductionStatements

/-! # The reduced identity component of a linearly reductive group -/

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Reduction

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

/-- In nonzero characteristic the reduced identity component of an affine
linearly reductive algebraic group over an algebraically closed field is a torus. -/
theorem isTorus_reduced_identityComponent_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hG : ∀ n (ρ : MatrixRepresentation G (Fin n)), ρ.IsSemisimple) :
    IsTorus (reducedSubgroup (finiteTypeIdentityComponent G)) := by
  let G₀ := finiteTypeIdentityComponent G
  let T := reducedSubgroup G₀
  let : GrpObj T.X := ReducedSubgroup.grpObj_redOver G₀
  let : Smooth T.X.hom := ReducedSubgroup.smooth_reducedSubgroup G₀
  let : IsAffineHom T.X.hom := ReducedSubgroup.isAffineHom_reducedSubgroup G₀
  let : ConnectedSpace T.X.left := DynamicBaseConnected.connectedSpace_red G₀.X.left
  let j : T ⟶ G := reducedSubgroupι G₀ ≫ finiteTypeIdentityComponentι G
  have hj : IsClosedImmersion j.hom.hom.left := by
    change IsClosedImmersion ((reducedSubgroupι G₀).hom.hom.left ≫
      (finiteTypeIdentityComponentι G).hom.hom.left)
    infer_instance
  apply noUnipotentSubgroupTorus k T
  intro U i hi _ hUc hU
  let : ConnectedSpace U.X.left := hUc
  have hpoints := points_eq_one_closed_connected_unipotent_of_linearlyReductive
    p hp hG (i ≫ j) (hi.comp (show IsClosedSubgroup j from hj)) hU
  apply SubgroupFunctor.ext
  intro S
  rw [SubgroupFunctor.bot_carrier]
  apply eq_bot_iff.mpr
  rintro _ ⟨x, rfl⟩
  erw [Subgroup.mem_bot]
  change x ≫ i.hom.hom = _
  rw [hpoints S x]
  exact map_one (((pointsMap i).app (op S)).hom)

end Reduction

/-- The reduced ambient case of multiplicative-type identity-component necessity. -/
def LinearlyReductiveReducedIdentityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [ExpChar k p], 1 < p →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsReduced G.X.left],
      IsLinearlyReductive G → IsMultiplicativeType (finiteTypeIdentityComponent G)

/-- For a reduced ambient group, the canonical identity component equals its
reduction, so the torus result gives multiplicative type. -/
theorem linearlyReductiveReducedIdentity : LinearlyReductiveReducedIdentityStatement.{u} := by
  intro k _ _ p _ hp G _ _ _ hG
  let G₀ := finiteTypeIdentityComponent G
  let : IsReduced G₀.X.left := isReduced_of_isOpenImmersion (finiteTypeIdentityComponentι G).hom.hom.left
  let j : reducedSubgroup G₀ ⟶ G₀ := reducedSubgroupι G₀
  let : IsClosedImmersion j.hom.hom.left := ReducedSubgroup.isClosedImmersion_reducedSubgroupι G₀
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let r : G₀ ⟶ reducedSubgroup G₀ := ReducedSubgroup.liftHom (𝟙 G₀)
  have hr : r ≫ j = 𝟙 G₀ := ReducedSubgroup.liftHom_fac _
  let e : G₀ ≅ reducedSubgroup G₀ :=
    { hom := r
      inv := j
      hom_inv_id := hr
      inv_hom_id := by
        apply Grp.hom_ext
        apply (cancel_mono j.hom.hom).mp
        change ((j ≫ r) ≫ j).hom.hom = (𝟙 _ ≫ j).hom.hom
        rw [Category.assoc, hr, Category.comp_id, Category.id_comp] }
  have hprime := (expChar_is_prime_or_one k p).resolve_right (by omega : p ≠ 1)
  let : CharP k p := (expChar_prime_iff k hprime).mp inferInstance
  exact IsMultiplicativeType.of_iso e
    (isTorus_reduced_identityComponent_of_linearlyReductive G p (by omega) hG).isMultiplicativeType

end Langlands.GroupScheme
