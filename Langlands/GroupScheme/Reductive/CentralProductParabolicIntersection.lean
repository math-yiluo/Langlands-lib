import Langlands.GroupScheme.CentralIsogeny.PowerLift
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.Dynamic.PositiveScaling
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison

/-! # Parabolic intersections with a reductive factor of a central product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {Z D G : GroupScheme S}

/-- A central factor of a product cocharacter does not affect conjugation. -/
theorem orbit_comp_centralProduct (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
    (χ : (Gm S).toGrp ⟶ Z ⊗ D) {T : Over S} (g : T ⟶ G.X) :
    orbit (χ ≫ prodHom z d (hz.commute_values _)) g =
      orbit ((χ ≫ snd Z D) ≫ d) g := by
  let p := snd T (Gm S).X ≫ χ.hom.hom
  let a := (productPointsEquiv Z D _ p).1 ≫ z.hom.hom
  let b := (productPointsEquiv Z D _ p).2 ≫ d.hom.hom
  let x := fst T (Gm S).X ≫ g
  have hχ : snd T (Gm S).X ≫
      (χ ≫ prodHom z d (hz.commute_values _)).hom.hom = a * b := by
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom]
  have hb : snd T (Gm S).X ≫ ((χ ≫ snd Z D) ≫ d).hom.hom = b := by
    rfl
  change _ * x * _⁻¹ = _ * x * _⁻¹
  rw [hχ, hb]
  calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = b * x * b⁻¹ :=
      (commute_of_mem_center (hz _ (productPointsEquiv Z D _ p).1) _).mul_inv_cancel

/-- Removing a central factor preserves the entire dynamic parabolic functor. -/
theorem parabolic_comp_centralProduct (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
    (χ : (Gm S).toGrp ⟶ Z ⊗ D) :
    parabolic (χ ≫ prodHom z d (hz.commute_values _)) =
      parabolic ((χ ≫ snd Z D) ≫ d) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  simp only [mem_parabolic, IsOrbitExtension, orbit_comp_centralProduct z hz d χ]

end Dynamic

namespace CentralProductParabolic

variable {k : Type u} [Field k]
    {Z D G P : GroupScheme (Spec (CommRingCat.of k))}

/-- A parabolic intersection with a closed reductive factor of a central product
is the dynamic parabolic of a cocharacter of that factor. -/
theorem exists_intersection_cocharacter
    (hG : IsConnectedReductive G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D,
      SubgroupFunctor.range (subgroupIntersectionFst d i) = Dynamic.parabolic χ := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨ψ, hψ⟩ :=
    ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup hG i hi
  obtain ⟨N, hN, hkill⟩ := hprod.exists_pow_eq_one_kernel
  obtain ⟨Φ, hΦ⟩ := hprod.exists_comp_eq_multiplication_comp ψ hkill
  have hpow : multiplication (Gm (Spec (CommRingCat.of k))).toGrp (2 * N : ℕ) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (2 * N)) := by
    apply Grp.hom_ext
    rw [multiplication_hom,
      ← Category.id_comp
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (2 * N))).hom.hom,
      Gm.powerHom_apply, Gm.comp_zsmul_id]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hscaled :
      Dynamic.parabolic (Φ ≫ prodHom z d (hz.commute_values _)) =
        Dynamic.parabolic ψ := by
    rw [hΦ, hpow]
    exact Dynamic.parabolic_precomp_power ψ (by omega)
  refine ⟨Φ ≫ snd Z D, ?_⟩
  rw [range_subgroupIntersectionFst_eq_comap, hψ,
    Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ d hd]
  rw [← Dynamic.parabolic_comp_centralProduct z hz d Φ, hscaled]

/-- Choose a cocharacter presenting the actual intersection parabolic over a field. -/
def intersectionCocharacter
    (hG : IsConnectedReductive G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D :=
  Classical.choose (exists_intersection_cocharacter hG d hd z hz hprod i hi)

/-- The chosen cocharacter presents the intersection on every test scheme. -/
theorem range_intersectionCocharacter
    (hG : IsConnectedReductive G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    SubgroupFunctor.range (subgroupIntersectionFst d i) =
      Dynamic.parabolic (intersectionCocharacter hG d hd z hz hprod i hi) :=
  Classical.choose_spec (exists_intersection_cocharacter hG d hd z hz hprod i hi)

/-- Over any field, intersection with a connected reductive closed factor of a
central product isogeny preserves parabolic subgroups. -/
theorem isParabolicSubgroup_intersection
    (hG : IsConnectedReductive G) (hD : IsConnectedReductive D)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    IsParabolicSubgroup (subgroupIntersectionFst d i) := by
  exact (parabolicDynamic k D hD _ _
    (isClosedSubgroup_subgroupIntersectionFst d hi.isClosedSubgroup)).mpr
      (exists_intersection_cocharacter hG d hd z hz hprod i hi)

end CentralProductParabolic

end Langlands.GroupScheme
