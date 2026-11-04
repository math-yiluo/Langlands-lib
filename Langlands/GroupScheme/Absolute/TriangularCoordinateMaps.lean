import Langlands.GroupScheme.Absolute.TriangularCoordinateSubgroups
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Additive coordinate maps and their full scheme kernels -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable (N : ℕ) (R : CommRingCat.{u})

/-- Points of a refined term are the original refined matrices over global
sections, on every test scheme. -/
abbrev refinedPoints (a b : ℕ) (T : Over (Spec R)) :
    (T ⟶ (refinedScheme N R a b).X) ≃* refinedW Γ(T.left, ⊤) N a b :=
  Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_refinedW N R a b)) T

theorem refinedPoints_comp (a b : ℕ) {T : Over (Spec R)}
    (x : T ⟶ (refinedScheme N R a b).X) :
    GeneralLinear.pointsEquiv (Fin N) R T (x ≫ (refinedHom N R a b).hom.hom) =
      (refinedPoints N R a b T x).val :=
  Corepresented.groupSchemeMap_points _ _ _ x

/-- The additive coordinate on the refined matrix functor, with the scalar
written in the unique coordinate of the one-dimensional vector group. -/
def refinedCoordinateNatTrans (a b : ℕ) (i j : Fin N) :
    Corepresented.cutFunctor (isCutOutBy_refinedW N R a b) ⟶ VectorGroup.functor R 1 where
  app A := GrpCat.ofHom
    ({
      toFun := fun g => Multiplicative.ofAdd fun _ =>
        (layerCoordinate A N a i j ⟨g.val, g.property.1⟩).toAdd
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext r
        simp [layerCoordinate]
      map_mul' g h := by
        apply Multiplicative.toAdd.injective
        funext r
        exact congrFun (congrFun (layer_mul g.property.1 h.property.1) i) j } :
      refinedW A N a b →* Multiplicative (Fin 1 → A))
  naturality {A B} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Multiplicative.toAdd.injective
    funext r
    exact layerCoordinate_map a i j g.property.1 f.hom.toRingHom

/-- The actual additive coordinate homomorphism of the closed refined
subgroup scheme. -/
def refinedCoordinate (a b : ℕ) (i j : Fin N) :
    refinedScheme N R a b ⟶ VectorGroup.groupScheme R 1 :=
  Corepresented.groupSchemeMap
    (Corepresented.cutCorepresentableBy (isCutOutBy_refinedW N R a b))
    (VectorGroup.corepresentableBy R 1) (refinedCoordinateNatTrans N R a b i j)

theorem coordinates_refinedCoordinate (a b : ℕ) (i j : Fin N)
    {T : Over (Spec R)} (x : T ⟶ (refinedScheme N R a b).X) (r : Fin 1) :
    (VectorGroup.coordinates R 1 T
      (x ≫ (refinedCoordinate N R a b i j).hom.hom)).toAdd r =
        layer Γ(T.left, ⊤) N a
          (((refinedPoints N R a b T x).val :
            Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) - 1) i j := by
  erw [VectorGroup.coordinates, refinedCoordinate, Corepresented.groupSchemeMap_points]
  rfl

variable {N R} {H : GroupScheme (Spec R)}

/-- The additive coordinate on the full inverse-image term of a representation. -/
def filtrationCoordinate (ρ : MatrixRepresentation H (Fin N))
    (a b : ℕ) (i j : Fin N) :
    filtrationScheme ρ a b ⟶ VectorGroup.groupScheme R 1 :=
  SubgroupPreimage.projection ρ (refinedHom N R a b) ≫ refinedCoordinate N R a b i j

/-- The actual homomorphism evaluates to the original matrix-layer entry
on every test scheme. -/
theorem coordinates_filtrationCoordinate (ρ : MatrixRepresentation H (Fin N))
    (a b : ℕ) (i j : Fin N) {T : Over (Spec R)}
    (x : T ⟶ (filtrationScheme ρ a b).X) (r : Fin 1) :
    (VectorGroup.coordinates R 1 T
      (x ≫ (filtrationCoordinate ρ a b i j).hom.hom)).toAdd r =
        layer Γ(T.left, ⊤) N a
          ((ρ.pointMatrix T (x ≫ (filtrationHom ρ a b).hom.hom) :
            Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) - 1) i j := by
  rw [filtrationCoordinate, Grp.comp_hom_hom, ← Category.assoc,
    coordinates_refinedCoordinate]
  have hm := refinedPoints_comp N R a b
    (x ≫ (SubgroupPreimage.projection ρ (refinedHom N R a b)).hom.hom)
  rw [Category.assoc, ← (SubgroupPreimage.isPullback ρ (refinedHom N R a b)).w,
    ← Category.assoc] at hm
  change ρ.pointMatrix T (x ≫ (filtrationHom ρ a b).hom.hom) = _ at hm
  rw [hm]

/-- On a genuine next-superdiagonal coordinate, the full kernel of the
actual additive homomorphism has exactly the next refined term as its range
in the original group scheme. -/
theorem range_kernel_filtrationCoordinate
    (ρ : MatrixRepresentation H (Fin N)) (a : ℕ) (i j : Fin N)
    (hij : (j : ℕ) = i + a + 1) :
    SubgroupFunctor.range
      (kernelι (filtrationCoordinate ρ a i i j) ≫ filtrationHom ρ a i) =
        SubgroupFunctor.range (filtrationHom ρ a (i + 1)) := by
  ext T x
  constructor
  · rintro ⟨z, rfl⟩
    let y := z ≫ (kernelι (filtrationCoordinate ρ a i i j)).hom.hom
    have hy : y ≫ (filtrationCoordinate ρ a i i j).hom.hom = 1 :=
      (mem_range_kernelι_iff _ y).mp ⟨z, rfl⟩
    change (y ≫ (filtrationHom ρ a i).hom.hom) ∈
      (SubgroupFunctor.range (filtrationHom ρ a (i + 1))).carrier T
    rw [mem_range_filtrationHom]
    have hg := (mem_range_filtrationHom ρ a i
      (y ≫ (filtrationHom ρ a i).hom.hom)).mp ⟨y, rfl⟩
    apply (mem_refinedW_succ_iff i j hij hg).mpr
    apply Multiplicative.toAdd.injective
    have hc := coordinates_filtrationCoordinate ρ a i i j y 0
    rw [hy, map_one] at hc
    exact hc.symm
  · intro hx
    have hx' := filtration_anti ρ a (by omega : (i : ℕ) ≤ i + 1) T hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx'
    have hg := (mem_range_filtrationHom ρ a i
      (y ≫ (filtrationHom ρ a i).hom.hom)).mp ⟨y, rfl⟩
    have hs := (mem_range_filtrationHom ρ a (i + 1) x).mp hx
    rw [← hy] at hs
    have hc := (mem_refinedW_succ_iff i j hij hg).mp hs
    have hy0 : y ≫ (filtrationCoordinate ρ a i i j).hom.hom = 1 := by
      apply (VectorGroup.coordinates R 1 T).injective
      apply Multiplicative.toAdd.injective
      funext r
      rw [map_one, coordinates_filtrationCoordinate]
      exact congrArg Multiplicative.toAdd hc
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff _ y).mpr hy0)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, hy]

end Langlands.GroupScheme.TriangularLayer
