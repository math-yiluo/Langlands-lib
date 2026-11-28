import Langlands.CommutativeAlgebra.UnramifiedStrictHenselianDvrExtension
import Langlands.AbelianScheme.UnipotentInertiaSemiabelianReductionStatement
import Langlands.AbelianScheme.StrictHenselianUnipotentInertiaSemiabelianStatement
import Langlands.AbelianScheme.NeronModelRamificationIndexOneBaseChangeStatement
import Langlands.AbelianScheme.GeometricSemiabelianReductionDescent
import Langlands.CommutativeAlgebra.UnramifiedStrictHenselianDvrExtensionStatement

/-! # Reduction of the Galois criterion to a strictly Henselian base

`UnipotentInertiaStrictHenselianReductionStatement` says that the Galois criterion over a
strictly Henselian trait (`StrictHenselianUnipotentInertiaSemiabelianStatement`), the
compatibility of Néron models with extensions of ramification index one
(`NeronModelRamificationIndexOneBaseChangeStatement`) and the existence of an unramified
strictly Henselian extension of a discrete valuation ring
(`UnramifiedStrictHenselianDvrExtensionStatement`) imply
`UnipotentInertiaSemiabelianReductionStatement`, at the same universe.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme

/-- The Galois criterion over strictly Henselian traits, Néron base change along extensions of
ramification index one and the existence of unramified strictly Henselian extensions imply the
Galois criterion over every discrete valuation ring. -/
def UnipotentInertiaStrictHenselianReductionStatement : Prop :=
  StrictHenselianUnipotentInertiaSemiabelianStatement.{u} →
    NeronModelRamificationIndexOneBaseChangeStatement.{u} →
      Langlands.CommutativeAlgebra.UnramifiedStrictHenselianDvrExtensionStatement.{u} →
        UnipotentInertiaSemiabelianReductionStatement.{u}

/-- Proof of the reduction: choose an unramified strictly Henselian extension `W` of `V` with
separable residue extension, take its fraction field `L` with the induced `K`-algebra
structure, give the base change of `N` to `W` the structure of a Néron model of the base change
of `B` to `L`, apply the strictly Henselian Galois criterion there and descend. -/
theorem unipotentInertiaStrictHenselianReduction :
    UnipotentInertiaStrictHenselianReductionStatement.{u} := by
  intro hS hBC hW V K _ _ _ _ _ _ B N ℓ _ hℓ hH
  obtain ⟨W, _, _, _, _, _, _, _, hmax, hsep⟩ := hW V
  let L := FractionRing W
  have hinj : Function.Injective ((algebraMap W L).comp (algebraMap V W)) :=
    (IsFractionRing.injective W L).comp (injective_algebraMap_of_map_maximalIdeal hmax)
  let : Algebra K L := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have hcomm : (algebraMap W L).comp (algebraMap V W) =
      (algebraMap K L).comp (algebraMap V K) := by
    ext x
    exact (IsFractionRing.lift_algebraMap (K := K) hinj x).symm
  let G := (CommGroupScheme.baseChange (Spec.algebraMap V W)).obj N.group
  have hsq : Spec.algebraMap K L ≫ NeronModelInfra.specGenericFibreInclusion V K =
      NeronModelInfra.specGenericFibreInclusion W L ≫ Spec.algebraMap V W := by
    simp only [NeronModelInfra.specGenericFibreInclusion, Spec.algebraMap, ← Spec.map_comp]
    congr 1
    ext x
    exact (DFunLike.congr_fun hcomm x).symm
  let gen : ((baseChange (Spec.algebraMap K L)).obj B).toCommGroupScheme ≅
      (CommGroupScheme.baseChange (NeronModelInfra.specGenericFibreInclusion W L)).obj G :=
    (CommGroupScheme.baseChange (Spec.algebraMap K L)).mapIso N.genericIso ≪≫
      (GeometricSemiabelianDescent.commBaseChangeCompIso _ _ N.group).symm ≪≫
      GeometricSemiabelianDescent.commBaseChangeEqIso hsq N.group ≪≫
      GeometricSemiabelianDescent.commBaseChangeCompIso _ _ N.group
  let N' : NeronModel W L ((baseChange (Spec.algebraMap K L)).obj B) :=
    { group := G
      property := hBC V K W L hmax hsep B N
      genericIso := gen }
  have hℓW : IsUnit (ℓ : W) := by simpa using hℓ.map (algebraMap V W)
  have hN' : N'.HasGeometricSemiabelianReduction :=
    hS W L _ N' ℓ hℓW (hH W hmax L hcomm)
  have : Algebra.IsAlgebraic (ResidueField V) (ResidueField W) := inferInstance
  exact NeronModel.hasGeometricSemiabelianReduction_of_baseChange N N' (Iso.refl _) hN'

end Langlands.AbelianScheme
