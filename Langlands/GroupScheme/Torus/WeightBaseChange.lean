import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Actual adjoint weights under scheme base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Ring

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

local notation "b" => algebraBaseMap k K

namespace Lie

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
  (i : G ⟶ H) {A : Type u} [CommRing A] [Algebra k A] [Algebra K A]
  [IsScalarTower k K A]

/-- The actual pullback point comparison commutes with homomorphisms of groups. -/
theorem affineBaseChangeEquiv_target
    (t : AffinePoints ((GroupScheme.baseChange b).obj G) A) :
    affineBaseChangeEquiv k K H A
        (t ≫ ((GroupScheme.baseChange b).map i).hom.hom) =
      affineBaseChangeEquiv k K G A t ≫ i.hom.hom := by
  change (affineBaseTestIso k K A).inv ≫
      (GroupScheme.baseChangePointsEquiv b H _
        (t ≫ ((GroupScheme.baseChange b).map i).hom.hom)) = _
  rw [GroupScheme.baseChangePointsEquiv_comp]
  exact (Category.assoc _ _ _).symm

end Lie

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- A base-changed character has the same value on the corresponding original point. -/
theorem Lie.characterValue_baseChange (χ : characterLattice T)
    (t : Lie.AffinePoints ((CommGroupScheme.baseChange b).obj T).toGrp A) :
    Lie.characterValue (characterLattice.baseChange b T χ) t =
      Lie.characterValue χ (Lie.affineBaseChangeEquiv k K T.toGrp A t) := by
  let q := Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv
  change q (Gm.pointsEquiv _ _ (t ≫
    (CommGroupScheme.groupHom (characterLattice.baseChange b T χ)).hom.hom)) =
      q (Gm.pointsEquiv _ _ (Lie.affineBaseChangeEquiv k K T.toGrp A t ≫
        (CommGroupScheme.groupHom χ).hom.hom))
  congr 1
  rw [characterLattice.baseChange_apply, comp_groupHom_comp]
  change Gm.pointsEquiv _ _ ((t ≫
    ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom χ)).hom.hom) ≫
      (Gm.baseChangeIso b).hom.hom.hom) = _
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    GroupScheme.baseChangePointsEquiv_comp]
  change _ = Gm.pointsEquiv _ _ ((Lie.affineBaseTestIso k K A).inv ≫
    GroupScheme.baseChangePointsEquiv b T.toGrp _ t ≫
      (CommGroupScheme.groupHom χ).hom.hom)
  rw [← Category.assoc, Gm.pointsEquiv_naturality, Gm.pointsEquiv_naturality]
  simp [Lie.affineBaseTestIso]
  rfl

end Ring

section Field

variable {k K : Type u} [Field k] [CommRing K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

namespace Lie

/-- Tensor scalar extension into the actual Lie kernel of the scheme pullback. -/
def schemeScalarExtension :
    K ⊗[k] Additive (lieKernel G k) ≃ₗ[K] Additive (lieKernel G_K K) :=
  (kernelScalarExtension G K).trans (kernelBaseChangeLinearEquiv k K G K).symm

theorem schemeScalarExtension_tmul (c : K) (x : Additive (lieKernel G k)) :
    schemeScalarExtension (K := K) G (c ⊗ₜ[k] x) =
      c • (kernelBaseChangeLinearEquiv k K G K).symm
        (lieKernelMapLinear G (Algebra.ofId k K) x) := by
  simp only [schemeScalarExtension, LinearEquiv.trans_apply,
    kernelScalarExtension_tmul, LinearEquiv.map_smul]

variable {A : Type u} [CommRing A] [Algebra k A] [Algebra K A]
  [IsScalarTower k K A]

/-- A pure extended vector has the expected image over every test algebra. -/
theorem schemeScalarExtension_base_naturality (x : Additive (lieKernel G k)) :
    kernelBaseChangeLinearEquiv k K G A
        (lieKernelMapLinear G_K (Algebra.ofId K A)
          (schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x))) =
      lieKernelMapLinear G (Algebra.ofId k A) x := by
  rw [kernelBaseChangeLinearEquiv_naturality, schemeScalarExtension_tmul,
    one_smul, LinearEquiv.apply_symm_apply, lieKernelMapLinear_base]

end Lie

/-- An actual weight vector extends to the corresponding base-changed weight space. -/
theorem weightSpace_baseChange_mem
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (χ : characterLattice T)
    {x : Additive (lieKernel G k)} (hx : x ∈ weightSpace i χ) :
    Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
      weightSpace ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
        (characterLattice.baseChange (algebraBaseMap k K) T χ) := by
  rw [mem_weightSpace]
  intro A _ _ t
  let : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  apply (Lie.kernelBaseChangeLinearEquiv k K G A).injective
  rw [Lie.kernelBaseChangeLinearEquiv_adjoint,
    Lie.schemeScalarExtension_base_naturality, LinearEquiv.map_smul,
    Lie.schemeScalarExtension_base_naturality, Lie.characterValue_baseChange,
    Lie.affineBaseChangeEquiv_target]
  exact hx A (Lie.affineBaseChangeEquiv k K T.toGrp A t)

end Field

end Langlands.GroupScheme
