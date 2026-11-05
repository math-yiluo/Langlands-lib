import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication

/-! # The represented dynamic parabolic as a product of schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

/-- A centralizer point followed by a unipotent point has limit the centralizer point. -/
theorem hasLimit_centralizer_mul_unipotent {T : Over S} {z v : T ⟶ G.X}
    (hz : z ∈ (centralizer χ).carrier T) (hv : v ∈ (unipotent χ).carrier T) :
    HasLimit χ (z * v) z := by
  simpa only [mul_one] using (hasLimit_of_mem_centralizer χ hz).mul χ hv

/-- The left quotient of a parabolic point by its limit is unipotent. -/
theorem inv_limit_mul_mem_unipotent [IsSeparated G.X.hom]
    {T : Over S} (g : (parabolic χ).carrier T) :
    (limit χ g)⁻¹ * (g : T ⟶ G.X) ∈ (unipotent χ).carrier T := by
  rw [mem_unipotent]
  have h := ((hasLimit_of_mem_centralizer χ (limit_mem_centralizer χ g)).inv).mul χ
    (hasLimit_limit χ g)
  simpa only [inv_mul_cancel] using h

variable {Z U P : GroupScheme S} {iZ : Z ⟶ G} {iU : U ⟶ G} {iP : P ⟶ G}

/-- Multiplication, factored through a representative of the dynamic parabolic. -/
def parabolicProductHom
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP) : Z.X ⊗ U.X ⟶ P.X :=
  (hP.pointsEquiv (Z.X ⊗ U.X)).symm
    ⟨SubgroupFunctor.cellMultiplication iZ iU, by
      apply mul_mem
      · apply centralizer_le_parabolic χ
        rw [← hZ.2]
        exact SubgroupFunctor.mem_range.mpr ⟨fst Z.X U.X, rfl⟩
      · apply unipotent_le_parabolic χ
        rw [← hU.2]
        exact SubgroupFunctor.mem_range.mpr ⟨snd Z.X U.X, rfl⟩⟩

@[simp]
theorem parabolicProductHom_comp
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP) :
    parabolicProductHom χ hZ hU hP ≫ iP.hom.hom =
      SubgroupFunctor.cellMultiplication iZ iU :=
  hP.pointsEquiv_symm_comp _

/-- Multiplication `Z(χ) × U(χ) → P(χ)` is an isomorphism of schemes over the base,
for any actual representatives and any separated group scheme. -/
theorem isIso_parabolicProductHom [IsSeparated G.X.hom]
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP) :
    IsIso (parabolicProductHom χ hZ hU hP) := by
  have : Mono iZ.hom.hom := hZ.1
  have : Mono iU.hom.hom := hU.1
  have : Mono iP.hom.hom := hP.1
  have memZ {T : Over S} (a : T ⟶ Z.X) :
      a ≫ iZ.hom.hom ∈ (centralizer χ).carrier T := (hZ.pointsEquiv T a).2
  have memU {T : Over S} (a : T ⟶ U.X) :
      a ≫ iU.hom.hom ∈ (unipotent χ).carrier T := (hU.pointsEquiv T a).2
  apply isIso_of_yoneda_map_bijective
  intro T
  constructor
  · intro a b hab
    have hprod :
        (a ≫ fst Z.X U.X ≫ iZ.hom.hom) * (a ≫ snd Z.X U.X ≫ iU.hom.hom) =
          (b ≫ fst Z.X U.X ≫ iZ.hom.hom) * (b ≫ snd Z.X U.X ≫ iU.hom.hom) := by
      have h := congrArg (fun f => f ≫ iP.hom.hom) hab
      simpa only [Category.assoc, parabolicProductHom_comp,
        SubgroupFunctor.cellMultiplication, MonObj.comp_mul] using h
    have hz :
        a ≫ fst Z.X U.X ≫ iZ.hom.hom = b ≫ fst Z.X U.X ≫ iZ.hom.hom := by
      have ha := hasLimit_centralizer_mul_unipotent χ
        (memZ (a ≫ fst Z.X U.X)) (memU (a ≫ snd Z.X U.X))
      have hb := hasLimit_centralizer_mul_unipotent χ
        (memZ (b ≫ fst Z.X U.X)) (memU (b ≫ snd Z.X U.X))
      simp only [Category.assoc] at ha hb
      rw [← hprod] at hb
      exact ha.unique χ hb
    have hu :
        a ≫ snd Z.X U.X ≫ iU.hom.hom = b ≫ snd Z.X U.X ≫ iU.hom.hom := by
      rw [hz] at hprod
      exact mul_left_cancel hprod
    apply CartesianMonoidalCategory.hom_ext
    · exact (cancel_mono iZ.hom.hom).mp (by simpa only [Category.assoc] using hz)
    · exact (cancel_mono iU.hom.hom).mp (by simpa only [Category.assoc] using hu)
  · intro p
    let g := hP.pointsEquiv T p
    let z : T ⟶ Z.X := (hZ.pointsEquiv T).symm
      ⟨limit χ g, limit_mem_centralizer χ g⟩
    let v : T ⟶ U.X := (hU.pointsEquiv T).symm
      ⟨(limit χ g)⁻¹ * (g : T ⟶ G.X), inv_limit_mul_mem_unipotent χ g⟩
    have hz : z ≫ iZ.hom.hom = limit χ g := hZ.pointsEquiv_symm_comp _
    have hv : v ≫ iU.hom.hom = (limit χ g)⁻¹ * (g : T ⟶ G.X) :=
      hU.pointsEquiv_symm_comp _
    refine ⟨lift z v, (cancel_mono iP.hom.hom).mp ?_⟩
    rw [Category.assoc, parabolicProductHom_comp, SubgroupFunctor.lift_cellMultiplication,
      hz, hv, mul_inv_cancel_left]
    rfl

/-- The scheme isomorphism whose forward map is multiplication `Z(χ) × U(χ) → P(χ)`.
The product is a product of underlying schemes, without a direct-product group law. -/
def parabolicProductIso [IsSeparated G.X.hom]
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP) : Z.X ⊗ U.X ≅ P.X := by
  letI := isIso_parabolicProductHom χ hZ hU hP
  exact asIso (parabolicProductHom χ hZ hU hP)

@[simp]
theorem parabolicProductIso_hom_comp [IsSeparated G.X.hom]
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP) :
    (parabolicProductIso χ hZ hU hP).hom ≫ iP.hom.hom =
      SubgroupFunctor.cellMultiplication iZ iU :=
  parabolicProductHom_comp χ hZ hU hP

end Langlands.GroupScheme.Dynamic
