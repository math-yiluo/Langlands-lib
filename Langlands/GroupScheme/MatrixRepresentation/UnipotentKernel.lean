import Langlands.GroupScheme.MatrixRepresentation.UnipotentFixedLine
import Langlands.GroupScheme.Reductive.UnipotentExtension
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Actual representations with a prescribed unipotent normal kernel -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A point acting trivially in restricted coordinates fixes a coordinate unit
vector in the image of their projection. -/
theorem restrictCoordinates_fix_single (ρ : MatrixRepresentation G n)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hs : ρ.IsStableCoordinates B C) (j : n)
    (hj : (B * C) *ᵥ Pi.single j 1 = Pi.single j 1)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X)
    (hx : (ρ.restrictCoordinates B C hCB hs).pointMatrix T x = 1) :
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      Pi.single j 1 := by
  have hproj : B.map (scalarMap T) *ᵥ
      (C.map (scalarMap T) *ᵥ Pi.single j (1 : Γ(T.left, ⊤))) =
      Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mulVec_single_one]
    simp only [Matrix.mulVec_single_one] at hj
    funext r
    change scalarMap T ((B * C) r j) = (Pi.single j (1 : Γ(T.left, ⊤)) : n → Γ(T.left, ⊤)) r
    have hjr : (B * C) r j = (Pi.single j (1 : k) : n → k) r := by
      exact congrFun hj r
    rw [hjr]
    by_cases h : r = j <;> simp [h]
  calc
    _ = (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
        (B.map (scalarMap T) *ᵥ
          (C.map (scalarMap T) *ᵥ Pi.single j (1 : Γ(T.left, ⊤)))) := by rw [hproj]
    _ = B.map (scalarMap T) *ᵥ
        (C.map (scalarMap T) *ᵥ Pi.single j (1 : Γ(T.left, ⊤))) := by
      rw [Matrix.mulVec_mulVec, ρ.restrictCoordinates_intertwines B C hCB hs,
        hx, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
    _ = _ := hproj

/-- Finite coordinates for an actual representation whose full all-test kernel
is the given represented subgroup. -/
structure KernelCoordinates (i : H ⟶ G) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  kernel_eq : SubgroupFunctor.range (kernelι representation) = SubgroupFunctor.range i

/-- A closed unipotent normal subgroup of an affine finite-type group is the
full kernel of an actual finite-dimensional representation over the same field. -/
def unipotentKernelCoordinates
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (hc : IsClosedSubgroup i) (hH : IsUnipotent H)
    (hN : (SubgroupFunctor.range i).IsNormal) : KernelCoordinates i := Classical.choice (by
  classical
  obtain ⟨a, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G H i hc
  have hj : (ρ.restrict i).IsFixedVector (Pi.single j 1) :=
    (ρ.restrict i).isFixedVector_single_of_isUnipotent hH j (by
      intro T x
      obtain ⟨u, hu⟩ := (hρ T (x ≫ i.hom.hom)).1
        (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩)
      exact ⟨u, hu⟩)
  let W := (ρ.restrict i).fixedSubmodule
  obtain ⟨B, C, hCB, hcols, hproj⟩ := exists_fixed_coordinates W
  have hGa : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hc
  have hHa : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  obtain ⟨A, ⟨jG⟩⟩ := (essImage_algSpec (G := G.X)).mpr hGa
  obtain ⟨D, ⟨jH⟩⟩ := (essImage_algSpec (G := H.X)).mpr hHa
  have hs : ρ.IsStableCoordinates B C :=
    ρ.isStableCoordinates_of_affine_model jG B C
      (ρ.normal_fixed_coordinates_affine i hN jH B C hcols hproj A.unop jG.hom)
  let r := ρ.restrictCoordinates B C hCB hs
  have hri : i ≫ r = 0 := by
    change r.restrict i = trivial H _
    exact ρ.restrictCoordinates_restrict_eq_trivial i B C hCB hs hcols
  refine ⟨⟨Module.finrank k W, r, ?_⟩⟩
  ext T x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_range]
  constructor
  · intro hx
    have hmat : r.pointMatrix T x = 1 := by
      rw [pointMatrix_apply, hx, map_one]
    have he := ρ.restrictCoordinates_fix_single B C hCB hs j
      (hproj _ hj) T x hmat
    apply (hρ T x).2
    refine ⟨1, ?_⟩
    simpa only [Units.val_one, one_smul] using he
  · rintro ⟨y, rfl⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hri]
    exact MonObj.comp_one y)

end Langlands.GroupScheme.MatrixRepresentation
