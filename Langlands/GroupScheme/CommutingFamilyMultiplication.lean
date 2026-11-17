import Langlands.GroupScheme.Products
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductFactors
import Mathlib.GroupTheory.NoncommPiCoprod

/-! # Multiplication of finite commuting families of group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.CommutingFamily

variable {S : Scheme.{u}} {I : Type u} [Finite I]
    (H : I → GroupScheme S) {G : GroupScheme S} (j : ∀ i, H i ⟶ G)
    (hc : ∀ (T : Over S), Pairwise fun a b =>
      ∀ (x : T ⟶ (H a).X) (y : T ⟶ (H b).X),
        Commute (x ≫ (j a).hom.hom) (y ≫ (j b).hom.hom))

/-- Multiply the images of the finitely many factor points. -/
def pointsHom (T : Over S) : (∀ i, T ⟶ (H i).X) →* (T ⟶ G.X) := by
  letI := Fintype.ofFinite I
  exact MonoidHom.noncommPiCoprod
    (fun i => ((pointsMap (j i)).app (op T)).hom) (hc T)

@[simp] theorem pointsHom_mulSingle [DecidableEq I] (T : Over S) (i : I) (x : T ⟶ (H i).X) :
    pointsHom H j hc T (Pi.mulSingle i x) = x ≫ (j i).hom.hom := by
  classical
  let := Fintype.ofFinite I
  exact MonoidHom.noncommPiCoprod_mulSingle
    (fun z : I => ((GroupScheme.pointsMap (j z)).app (op T)).hom)
    (hcomm := hc T) i x

/-- The finite product multiplication is natural in every relative test scheme. -/
theorem pointsHom_naturality {T T' : Over S} (a : T' ⟶ T)
    (x : ∀ i, T ⟶ (H i).X) :
    pointsHom H j hc T' (fun i => a ≫ x i) = a ≫ pointsHom H j hc T x := by
  classical
  let f : (∀ i, T ⟶ (H i).X) →* (T' ⟶ G.X) :=
    (pointsHom H j hc T').comp ((familyPoints H).map a.op).hom
  let g : (∀ i, T ⟶ (H i).X) →* (T' ⟶ G.X) :=
    ((points G).map a.op).hom.comp (pointsHom H j hc T)
  have he : f = g := by
    apply MonoidHom.pi_ext
    intro i y
    have ha : (fun z : I => a ≫ (Pi.mulSingle i y : ∀ z, T ⟶ (H z).X) z) =
        (Pi.mulSingle i (a ≫ y) : ∀ z, T' ⟶ (H z).X) := by
      funext z
      by_cases hz : z = i
      · subst z
        simp
      · simp [Pi.mulSingle_eq_of_ne hz, MonObj.comp_one]
    change pointsHom H j hc T'
        (fun z : I => a ≫ (Pi.mulSingle i y : ∀ z, T ⟶ (H z).X) z) =
      a ≫ pointsHom H j hc T (Pi.mulSingle i y : ∀ z, T ⟶ (H z).X)
    rw [ha, pointsHom_mulSingle, pointsHom_mulSingle, Category.assoc]
  exact congrArg (fun h : (∀ z, T ⟶ (H z).X) →* (T' ⟶ G.X) => h x) he

/-- Multiplication of the family as a natural transformation of group presheaves. -/
def pointsMap : familyPoints H ⟶ points G where
  app T := GrpCat.ofHom (pointsHom H j hc T.unop)
  naturality {T T'} a := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact pointsHom_naturality H j hc a.unop x

/-- The actual group-scheme homomorphism multiplying the commuting factors. -/
def multiplication : pi H ⟶ G :=
  yonedaGrpFullyFaithful.preimage ((piPointsIso H).hom ≫ pointsMap H j hc)

/-- The actual multiplication homomorphism realizes the prescribed point map. -/
theorem multiplication_points (T : Over S) (x : T ⟶ (pi H).X) :
    x ≫ (multiplication H j hc).hom.hom =
      pointsHom H j hc T (piPointsEquiv H T x) := by
  exact congrArg (fun f => f.app (op T) x)
    (yonedaGrpFullyFaithful.map_preimage ((piPointsIso H).hom ≫ pointsMap H j hc))

/-- Restriction of multiplication to a single factor is the original homomorphism. -/
@[reassoc (attr := simp)] theorem inclusion_multiplication (i : I) :
    piFactorInclusionHom H i ≫ multiplication H j hc = j i := by
  classical
  apply Grp.hom_ext
  change (piFactorInclusionHom H i).hom.hom ≫
    (multiplication H j hc).hom.hom = (j i).hom.hom
  rw [multiplication_points]
  have hcoord : piPointsEquiv H (H i).X (piFactorInclusionHom H i).hom.hom =
      Pi.mulSingle i (𝟙 (H i).X) := by
    funext z
    by_cases hz : i = z
    · subst z
      simpa only [Category.id_comp, Pi.mulSingle_eq_same, piPointsEquiv_apply] using
        piFactorInclusionHom_points_self H i (𝟙 (H i).X)
    · simpa only [Category.id_comp, piPointsEquiv_apply,
        Pi.mulSingle_eq_of_ne (Ne.symm hz)] using
        piFactorInclusionHom_points_ne H i z hz (𝟙 (H i).X)
  rw [hcoord, pointsHom_mulSingle, Category.id_comp]

/-- Each prescribed factor image is contained in the multiplication image. -/
theorem range_le_multiplication (i : I) :
    SubgroupFunctor.range (j i) ≤ SubgroupFunctor.range (multiplication H j hc) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ (piFactorInclusionHom H i).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, inclusion_multiplication]

end Langlands.GroupScheme.CommutingFamily
