import Langlands.GroupScheme.Reductive.LocalSplitCell
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Transport of root parametrizations and Weyl points along group isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

theorem rootPoint_comp (u : Ga R ⟶ G) (f : G ⟶ H) (Z : Over (Spec (CommRingCat.of R)))
    (c : Γ(Z.left, ⊤)) : rootPoint (u ≫ f) Z c = rootPoint u Z c ≫ f.hom.hom := by
  rw [rootPoint, rootPoint, Grp.comp_hom_hom, Category.assoc]

theorem weylPoint_comp (u u' : Ga R ⟶ G) (f : G ⟶ H) :
    weylPoint (u ≫ f) (u' ≫ f) = weylPoint u u' ≫ f.hom.hom := by
  simp only [weylPoint, rootPoint_comp, MonObj.mul_comp]

/-- A root parametrization stays one after an isomorphism of the ambient groups that carries
the torus to the torus. -/
theorem IsRootParametrization.comp_iso {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {m : I → ℤ} {u : Ga R ⟶ G}
    (hu : IsRootParametrization i m u) (Φ : G ≅ H) (h : i ≫ Φ.hom = i') :
    IsRootParametrization i' m (u ≫ Φ.hom) where
  represents := by
    have hr := hu.represents.comp_iso Φ
    have h' : i' ≫ Φ.symm.hom = CommGroupScheme.groupHom
        (Iso.refl (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)).hom ≫ i := by
      rw [← h, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl
    have hs := RelativeRoot.subgroup_comap_of_transport (Iso.refl _) Φ.symm h'
      (splitTorus.exponentCharacter _ I m)
    have hc : characterLattice.congr (Iso.refl _) (splitTorus.exponentCharacter
        (Spec (CommRingCat.of R)) I m) = splitTorus.exponentCharacter _ I m := by
      rw [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp]
    rw [hc, Iso.symm_hom] at hs
    rwa [hs] at hr
  isClosedSubgroup := hu.isClosedSubgroup.comp_iso Φ
  equivariant Z t c := by
    rw [rootPoint_comp, rootPoint_comp, ← h, Grp.comp_hom_hom, ← Category.assoc,
      ← MonObj.mul_comp, ← GrpObj.inv_comp, ← MonObj.mul_comp, hu.equivariant]

theorem toUnit_comp_eq_constantPoint (n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X)
    (Z : Over (Spec (CommRingCat.of R))) : toUnit Z ≫ n = G.constantPoint n Z := by
  rw [GroupScheme.constantPoint]
  congr 1

/-- A Weyl point normalizes the torus through the exponent automorphism. -/
theorem IsWeylPoint.isNormalizingPoint [DecidableEq I]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (hn : IsWeylPoint i n f) :
    IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) i n
      (splitTorus.exponentCommIso _ I f) := by
  apply Grp.hom_ext
  have h := hn _ (𝟙 _)
  rw [toUnit_comp_eq_constantPoint, Category.id_comp, Category.id_comp,
    ← GroupScheme.comp_innerIso_hom] at h
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, h]
  rfl

theorem IsWeylPoint.mem_normalizerPoints [DecidableEq I]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (hn : IsWeylPoint i n f) :
    n ∈ normalizerPoints (T := splitTorus.commGroupScheme _ I) i :=
  ⟨_, hn.isNormalizingPoint⟩

end Langlands.GroupScheme.LocalSplitCell
