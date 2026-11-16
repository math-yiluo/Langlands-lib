import Langlands.GroupScheme.Reductive.RelativeCommutatorDescent
import Langlands.GroupScheme.Reductive.UnitPowerFppfCover
import Langlands.GroupScheme.Torus.Maximal

/-! # Inverted cocharacters are fppf-locally commutators -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeDerived

variable {S : Scheme.{u}} {G : GroupScheme S} {T U : Over S}

/-- An actual normalizing base point acts by inversion on this cocharacter. -/
def IsInvertedByNormalizer {D : CommGroupScheme S} (i : D.toGrp ⟶ G)
    (h : cocharacterLattice D) : Prop :=
  ∃ (n : Over.mk (𝟙 S) ⟶ G.X) (σ : D ≅ D),
    IsNormalizingPoint i n σ ∧ h ≫ σ.hom = -h

/-- Local membership descends along a single surjective fppf morphism. -/
theorem LocallyCommutator.of_surjective {x : T ⟶ G.X} (j : U ⟶ T)
    [Flat j.left] [Surjective j.left] [LocallyOfFinitePresentation j.left]
    (hx : LocallyCommutator (j ≫ x)) : LocallyCommutator x := by
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left :=
    Scheme.Cover.mkOfCovers PUnit (fun _ => U.left) (fun _ => j.left)
      (fun t => by obtain ⟨v, hv⟩ := (show Function.Surjective j.left from Scheme.Hom.surjective j.left) t
                   exact ⟨PUnit.unit, v, hv⟩)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply LocallyCommutator.of_cover 𝒰
  intro i
  let a : Over.mk (j.left ≫ T.hom) ⟶ U := Over.homMk (𝟙 _) (by simp [j.w])
  have h := hx.restrict a
  have he : (Over.homMk j.left rfl : Over.mk (j.left ≫ T.hom) ⟶ T) ≫ x =
      a ≫ (j ≫ x) := by
    apply Over.OverMorphism.ext
    change j.left ≫ x.left = (𝟙 _) ≫ (j.left ≫ x.left)
    simp only [Category.id_comp]
  change LocallyCommutator
    ((Over.homMk j.left rfl : Over.mk (j.left ≫ T.hom) ⟶ T) ≫ x)
  rw [he]
  exact h

/-- An element conjugate to its inverse has its square in the abstract
commutator subgroup. -/
theorem square_mem_commutator_of_conj_inv {A : Type*} [Group A] (n g : A)
    (h : n * g * n⁻¹ = g⁻¹) : g ^ 2 ∈ _root_.commutator A := by
  have hi : n * (g⁻¹ * n⁻¹) = g := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv h
  have he : ⁅g, n⁆ = g ^ 2 := by
    rw [commutatorElement_def, mul_assoc, mul_assoc, hi, pow_two]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)

/-- A point of an inverted cocharacter, once its unit parameter is a square,
belongs to the abstract commutator subgroup. -/
theorem mem_commutator_of_inverted_cocharacter_square
    {D : CommGroupScheme S} (i : D.toGrp ⟶ G) (h : cocharacterLattice D)
    (n : Over.mk (𝟙 S) ⟶ G.X) (σ : D ≅ D)
    (hn : IsNormalizingPoint i n σ) (hinv : h ≫ σ.hom = -h)
    (Z : Over S) (z : Z ⟶ (Gm S).X) :
    (z ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) ^ 2 ∈
      _root_.commutator (Z ⟶ G.X) := by
  apply square_mem_commutator_of_conj_inv (G.constantPoint n Z)
  have he := congrArg (fun f : D.toGrp ⟶ G =>
    (z ≫ (CommGroupScheme.groupHom h).hom.hom) ≫ f.hom.hom) hn
  simp only [Grp.comp_hom_hom] at he
  rw [← Category.assoc (z ≫ (CommGroupScheme.groupHom h).hom.hom) i.hom.hom,
    GroupScheme.comp_innerIso_hom] at he
  have hh : (CommGroupScheme.groupHom h).hom.hom ≫
      (CommGroupScheme.groupHom σ.hom).hom.hom =
      ((CommGroupScheme.groupHom h).hom.hom)⁻¹ := by
    change (CommGroupScheme.groupHom (h ≫ σ.hom)).hom.hom = _
    rw [hinv]
    rfl
  have hr : (z ≫ (CommGroupScheme.groupHom h).hom.hom) ≫
      (CommGroupScheme.groupHom σ.hom).hom.hom ≫ i.hom.hom =
      (z ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom)⁻¹ := by
    calc
      _ = z ≫ ((CommGroupScheme.groupHom h).hom.hom ≫
          (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom := by
        simp only [Category.assoc]
      _ = z ≫ ((CommGroupScheme.groupHom h).hom.hom)⁻¹ ≫ i.hom.hom := by rw [hh]
      _ = _ := by rw [← Category.assoc z, GrpObj.comp_inv, GrpObj.inv_comp, Category.assoc]
  exact he.trans hr

end Langlands.GroupScheme.RelativeDerived

namespace Langlands.GroupScheme.RelativeDerived

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Every point of an inverted cocharacter over an affine test scheme is
fppf-locally an abstract commutator. -/
theorem locallyCommutator_of_inverted_cocharacter_affine
    {D : CommGroupScheme S} (i : D.toGrp ⟶ G) (h : cocharacterLattice D)
    (n : Over.mk (𝟙 S) ⟶ G.X) (σ : D ≅ D)
    (hn : IsNormalizingPoint i n σ) (hinv : h ≫ σ.hom = -h)
    (Z : Over S) [IsAffine Z.left] (t : Z ⟶ (Gm S).X) :
    LocallyCommutator (t ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) := by
  obtain ⟨W, j, hW, hflat, hsurj, hfp, r, hr⟩ :=
    UnitPowerExtension.exists_roots_test Z 2 (by decide)
      (fun _ : Fin 1 => Gm.pointsEquiv S Z t)
  let : Flat j.left := hflat
  let : Surjective j.left := hsurj
  let : LocallyOfFinitePresentation j.left := hfp
  let z : W ⟶ (Gm S).X := (Gm.pointsEquiv S W).symm (r 0)
  have hz : z ^ 2 = j ≫ t := by
    apply (Gm.pointsEquiv S W).injective
    rw [map_pow, MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
    exact hr 0
  apply LocallyCommutator.of_surjective j
  apply LocallyCommutator.of_mem
  have hm := mem_commutator_of_inverted_cocharacter_square i h n σ hn hinv W z
  have he : (z ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) ^ 2 =
      j ≫ (t ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) := by
    rw [← MonObj.pow_comp, hz]
    simp only [Category.assoc]
  rw [he] at hm
  exact hm

/-- Every point of an inverted cocharacter over any test scheme is
fppf-locally an abstract commutator. -/
theorem locallyCommutator_of_inverted_cocharacter
    {D : CommGroupScheme S} (i : D.toGrp ⟶ G) (h : cocharacterLattice D)
    (n : Over.mk (𝟙 S) ⟶ G.X) (σ : D ≅ D)
    (hn : IsNormalizingPoint i n σ) (hinv : h ≫ σ.hom = -h)
    (Z : Over S) (t : Z ⟶ (Gm S).X) :
    LocallyCommutator (t ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) := by
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Z.left :=
    Z.left.affineCover.changeProp (fun j => by
      have := Z.left.affineCover.map_prop j
      exact ⟨inferInstance, inferInstance⟩)
  apply LocallyCommutator.of_cover 𝒰
  intro j
  let U : Over S := Over.mk (𝒰.f j ≫ Z.hom)
  let a : U ⟶ Z := Over.homMk (𝒰.f j) rfl
  have : IsAffine U.left := inferInstanceAs (IsAffine (Z.left.affineCover.X j))
  exact locallyCommutator_of_inverted_cocharacter_affine i h n σ hn hinv U (a ≫ t)

/-- The geometric inversion criterion implies local commutator membership
for every parameter on every test scheme. -/
theorem IsInvertedByNormalizer.locallyCommutator
    {D : CommGroupScheme S} {i : D.toGrp ⟶ G} {h : cocharacterLattice D}
    (hi : IsInvertedByNormalizer i h) (Z : Over S) (t : Z ⟶ (Gm S).X) :
    LocallyCommutator (t ≫ (CommGroupScheme.groupHom h).hom.hom ≫ i.hom.hom) := by
  obtain ⟨n, σ, hn, hinv⟩ := hi
  exact locallyCommutator_of_inverted_cocharacter i h n σ hn hinv Z t

end Langlands.GroupScheme.RelativeDerived
