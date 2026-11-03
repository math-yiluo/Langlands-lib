import Langlands.GroupScheme.Rational.CocharacterCentralizer

/-! # The actual commutator endomorphism of a normalized torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section ArbitraryBase

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  (i : T.toGrp ⟶ G)

/-- The endomorphism of the commutative group scheme induced by
`t ↦ n t n⁻¹ t⁻¹`, written as the difference of actual homomorphisms. -/
def torusCommutatorEnd (n : normalizerPoints i) : T ⟶ T :=
  (normalizingAut i n).hom - 𝟙 T

/-- Its image in the ambient group is the actual commutator on every test scheme. -/
theorem comp_torusCommutatorEnd (n : normalizerPoints i)
    {U : Over S} (t : U ⟶ T.X) :
    t ≫ (CommGroupScheme.groupHom (torusCommutatorEnd i n)).hom.hom ≫ i.hom.hom =
      G.constantPoint n.val U * (t ≫ i.hom.hom) *
        (G.constantPoint n.val U)⁻¹ * (t ≫ i.hom.hom)⁻¹ := by
  have hsub :
      t ≫ (CommGroupScheme.groupHom (torusCommutatorEnd i n)).hom.hom =
        (t ≫ (CommGroupScheme.groupHom (normalizingAut i n).hom).hom.hom) * t⁻¹ := by
    have h := congrArg Additive.toMul
      ((evalPoint t).map_sub (normalizingAut i n).hom (𝟙 T))
    change t ≫ (CommGroupScheme.groupHom (torusCommutatorEnd i n)).hom.hom =
      (t ≫ (CommGroupScheme.groupHom (normalizingAut i n).hom).hom.hom) /
        (t ≫ (CommGroupScheme.groupHom (𝟙 T)).hom.hom) at h
    have hid : (CommGroupScheme.groupHom (𝟙 T)).hom.hom = 𝟙 T.X := rfl
    simpa only [hid, Category.comp_id, div_eq_mul_inv] using h
  have hn := congrArg (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom)
    (isNormalizingPoint_normalizingAut i n)
  simp only [Grp.comp_hom_hom] at hn
  rw [← Category.assoc, comp_innerIso_hom] at hn
  rw [← Category.assoc, hsub, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ← hn]

/-- Being killed by the commutator endomorphism is exactly being fixed by
the induced torus automorphism. -/
theorem comp_torusCommutatorEnd_eq_zero_iff (n : normalizerPoints i)
    (ν : Gm S ⟶ T) :
    ν ≫ torusCommutatorEnd i n = 0 ↔ ν ≫ (normalizingAut i n).hom = ν := by
  rw [torusCommutatorEnd, Preadditive.comp_sub, Category.comp_id, sub_eq_zero]

end ArbitraryBase

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A commutator-kernel cocharacter is centralized by the original normalizing
point. The equality concerns actual morphisms, hence all test schemes. -/
theorem normalizerPoint_mem_dynamicCentralizer_iff_commutator_eq_zero
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    n.val ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 _)) ↔
      ν ≫ torusCommutatorEnd i n = 0 := by
  rw [normalizerPoint_mem_dynamicCentralizer_iff,
    comp_torusCommutatorEnd_eq_zero_iff, cocharacterAut_apply]

end Langlands.GroupScheme
