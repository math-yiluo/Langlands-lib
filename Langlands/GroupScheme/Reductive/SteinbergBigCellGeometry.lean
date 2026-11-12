import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination
import Langlands.GroupScheme.Dynamic.PositiveWeightParabolicDistinction
import Langlands.GroupScheme.HomogeneousCharacterCoordinates

/-! # All-test geometric steps for Steinberg big-cell data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance instIsAffineLeft_steinbergBigCellGeometry :
    IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- If a coordinate evaluates to a global unit, the entire test-scheme image
lies in its principal open, including for nonaffine and nonreduced tests. -/
theorem range_point_subset_basicOpen_of_isUnit {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (d : algebra G) (hd : IsUnit (pointAlgebraHom G T g d)) :
    Set.range g.left ⊆ (G.X.left.basicOpen (globalAlgHom G d) : Set G.X.left) := by
  have hpull : g.left.appTop (globalAlgHom G d) = pointAlgebraHom G T g d :=
    (pointAlgebraHom_apply_eq G T g d).symm
  have hpre : g.left ⁻¹ᵁ G.X.left.basicOpen (globalAlgHom G d) = ⊤ := by
    rw [Scheme.preimage_basicOpen_top, hpull, T.left.basicOpen_of_isUnit hd]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ g.left ⁻¹ᵁ G.X.left.basicOpen (globalAlgHom G d) := by
    rw [hpre]
    trivial
  exact hx

end AffineCoordinates

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G U P : GroupScheme S}

/-- The global lift of a test-scheme point into an actual open multiplication
cell, constructed from containment of its entire image. -/
def cellPointLift (iU : U ⟶ G) (iP : P ⟶ G)
    [IsOpenImmersion (cellMultiplication iU iP).left]
    {T : Over S} (g : T ⟶ G.X)
    (hg : Set.range g.left ⊆ Set.range (cellMultiplication iU iP).left) :
    T ⟶ U.X ⊗ P.X := by
  let f := cellMultiplication iU iP
  let l := IsOpenImmersion.lift f.left g.left hg
  have hl : l ≫ f.left = g.left := IsOpenImmersion.lift_fac f.left g.left hg
  exact Over.homMk l (by
    calc
      l ≫ (U.X ⊗ P.X).hom = l ≫ (f.left ≫ G.X.hom) := by rw [Over.w]
      _ = g.left ≫ G.X.hom := by rw [← Category.assoc, hl]
      _ = T.hom := g.w)

/-- The constructed lift recovers the original point under multiplication. -/
theorem cellPointLift_comp (iU : U ⟶ G) (iP : P ⟶ G)
    [IsOpenImmersion (cellMultiplication iU iP).left]
    {T : Over S} (g : T ⟶ G.X)
    (hg : Set.range g.left ⊆ Set.range (cellMultiplication iU iP).left) :
    cellPointLift iU iP g hg ≫ cellMultiplication iU iP = g := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- An all-test factorization follows from topological image containment in
an actual open cell. The factors are global points of the original test scheme. -/
theorem exists_cell_factors_of_range_subset (iU : U ⟶ G) (iP : P ⟶ G)
    [IsOpenImmersion (cellMultiplication iU iP).left]
    {T : Over S} (g : T ⟶ G.X)
    (hg : Set.range g.left ⊆ Set.range (cellMultiplication iU iP).left) :
    ∃ (a : T ⟶ U.X) (b : T ⟶ P.X),
      g = (a ≫ iU.hom.hom) * (b ≫ iP.hom.hom) := by
  let a := cellPointLift iU iP g hg
  have ha : a ≫ cellMultiplication iU iP = g := cellPointLift_comp iU iP g hg
  refine ⟨a ≫ fst U.X P.X, a ≫ snd U.X P.X, ?_⟩
  rw [← ha]
  simp only [cellMultiplication, MonObj.comp_mul, Category.assoc]

end SubgroupFunctor

namespace Dynamic

section OppositeCentralizer

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Reversing a cocharacter does not change its all-test centralizer. -/
theorem centralizer_oppositeCocharacter (χ : (Gm S).toGrp ⟶ G) :
    centralizer (oppositeCocharacter χ) = centralizer χ := by
  apply le_antisymm
  · have h := centralizer_le_precomp (oppositeCocharacter χ)
      (CommGroupScheme.groupHom (Gm.powerHom S (-1)))
    change centralizer (oppositeCocharacter χ) ≤
      centralizer (oppositeCocharacter (oppositeCocharacter χ)) at h
    simpa only [oppositeCocharacter_oppositeCocharacter] using h
  · exact centralizer_le_precomp χ (CommGroupScheme.groupHom (Gm.powerHom S (-1)))

end OppositeCentralizer

section AffineBase

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- Opposite dynamic parabolics meet in the full centralizer functor, on
arbitrary test schemes and without smoothness or reductivity assumptions. -/
theorem parabolic_inf_opposite_eq_centralizer :
    parabolic χ ⊓ parabolic (oppositeCocharacter χ) = centralizer χ := by
  apply le_antisymm
  · intro T g hg
    let z := limit χ ⟨g, hg.1⟩
    have hz : z ∈ (centralizer χ).carrier T := limit_mem_centralizer χ ⟨g, hg.1⟩
    have hzp : z ∈ (parabolic (oppositeCocharacter χ)).carrier T := by
      apply centralizer_le_parabolic (oppositeCocharacter χ) T
      rwa [centralizer_oppositeCocharacter]
    have hu : g * z⁻¹ ∈ (unipotent χ).carrier T :=
      mul_inv_limit_mem_unipotent χ ⟨g, hg.1⟩
    have hp : g * z⁻¹ ∈ (parabolic (oppositeCocharacter χ)).carrier T :=
      mul_mem hg.2 (inv_mem hzp)
    have he : g * z⁻¹ = 1 :=
      eq_one_of_mem_opposite_unipotent_of_mem_parabolic (oppositeCocharacter χ)
        (by simpa only [oppositeCocharacter_oppositeCocharacter] using hu) hp
    have hgz : g = z := mul_inv_eq_one.mp he
    rwa [hgz]
  · intro T g hg
    refine ⟨centralizer_le_parabolic χ T hg, ?_⟩
    apply centralizer_le_parabolic (oppositeCocharacter χ) T
    rwa [centralizer_oppositeCocharacter]

/-- Equality of points in represented opposite parabolics gives a point in
the supplied representative of their centralizer. -/
theorem exists_centralizer_point_of_opposite_parabolic_eq
    {P Q Z : GroupScheme (Spec R)} {iP : P ⟶ G} {iQ : Q ⟶ G} {iZ : Z ⟶ G}
    (hP : (parabolic χ).IsRepresentedBy iP)
    (hQ : (parabolic (oppositeCocharacter χ)).IsRepresentedBy iQ)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    {T : Over (Spec R)} (a : T ⟶ P.X) (b : T ⟶ Q.X)
    (he : a ≫ iP.hom.hom = b ≫ iQ.hom.hom) :
    ∃ z : T ⟶ Z.X, a ≫ iP.hom.hom = z ≫ iZ.hom.hom := by
  have hp : a ≫ iP.hom.hom ∈ (parabolic χ).carrier T :=
    (hP.pointsEquiv T a).2
  have hq : a ≫ iP.hom.hom ∈ (parabolic (oppositeCocharacter χ)).carrier T := by
    rw [he]
    exact (hQ.pointsEquiv T b).2
  have hz : a ≫ iP.hom.hom ∈ (centralizer χ).carrier T := by
    rw [← parabolic_inf_opposite_eq_centralizer χ]
    exact ⟨hp, hq⟩
  rw [← hZ.2] at hz
  obtain ⟨z, hez⟩ := SubgroupFunctor.mem_range.mp hz
  exact ⟨z, hez.symm⟩

end AffineBase

section Field

open AffineCoordinates

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Containment of the principal open in the opposite cell implies the
factorization required by Steinberg big-cell data on every scheme test. -/
theorem exists_opposite_parabolic_factors_of_unit
    {P Q U : GroupScheme (Spec (CommRingCat.of k))}
    {iP : P ⟶ G} {iQ : Q ⟶ G} {iU : U ⟶ G}
    (hP : (parabolic χ).IsRepresentedBy iP)
    (hQ : (parabolic (oppositeCocharacter χ)).IsRepresentedBy iQ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (d : algebra G)
    (hopen : (G.X.left.basicOpen (globalAlgHom G d) : Set G.X.left) ⊆
      Set.range (SubgroupFunctor.cellMultiplication iU iQ).left)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X)
    (hd : IsUnit (pointAlgebraHom G T g d)) :
    ∃ (b : T ⟶ P.X) (b' : T ⟶ Q.X),
      g = (b ≫ iP.hom.hom) * (b' ≫ iQ.hom.hom)⁻¹ := by
  let : IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iQ).left :=
    oppositeCellStatement k G (oppositeCocharacter χ) U Q iU iQ
      (by
        change (unipotent (oppositeCocharacter (oppositeCocharacter χ))).IsRepresentedBy iU
        simpa only [oppositeCocharacter_oppositeCocharacter] using hU) hQ
  obtain ⟨a, q, he⟩ := SubgroupFunctor.exists_cell_factors_of_range_subset iU iQ g
    ((range_point_subset_basicOpen_of_isUnit G g d hd).trans hopen)
  have ha : a ≫ iU.hom.hom ∈ (parabolic χ).carrier T :=
    unipotent_le_parabolic χ T (hU.pointsEquiv T a).2
  rw [← hP.2] at ha
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp ha
  refine ⟨b, q⁻¹, ?_⟩
  rw [GrpObj.inv_comp, inv_inv, hb]
  exact he

end Field

end Dynamic

end Langlands.GroupScheme
