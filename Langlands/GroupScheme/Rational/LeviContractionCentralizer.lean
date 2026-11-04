import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Dynamic.Uniqueness

/-! # Identifying the original Levi from contraction and containment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G P L U M : GroupScheme S}
    (l : L ⟶ P) (r : U ⟶ P) (j : P ⟶ G)
    [IsIso (subgroupMultiplication l r)]

/-- A subgroup containing both factors of an actual multiplication
isomorphism contains the full image of the product group. -/
theorem SubgroupFunctor.range_le_of_subgroupMultiplication
    (F : SubgroupFunctor G)
    (hL : range (l ≫ j) ≤ F) (hU : range (r ≫ j) ≤ F) :
    range j ≤ F := by
  intro T x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  have hdecomp := congrArg (fun z : T ⟶ P.X => z ≫ j.hom.hom)
    (leviComponent_mul_radicalComponent l r y)
  have hmem := (F.carrier T).mul_mem
    (hL T (mem_range.mpr ⟨leviComponent l r y, rfl⟩))
    (hU T (mem_range.mpr ⟨radicalComponent l r y, rfl⟩))
  simpa only [Grp.comp_hom_hom, ← Category.assoc, ← MonObj.mul_comp, hdecomp] using hmem

namespace Dynamic

variable (χ : (Gm S).toGrp ⟶ G)

/-- Fixing the first multiplication factor and contracting the second
puts the entire product image in the dynamic parabolic. -/
theorem range_le_parabolic_of_subgroupMultiplication
    (hL : SubgroupFunctor.range (l ≫ j) ≤ centralizer χ)
    (hU : SubgroupFunctor.range (r ≫ j) ≤ unipotent χ) :
    SubgroupFunctor.range j ≤ parabolic χ :=
  SubgroupFunctor.range_le_of_subgroupMultiplication l r j _
    (hL.trans (centralizer_le_parabolic χ)) (hU.trans (unipotent_le_parabolic χ))

variable [IsSeparated G.X.hom]

/-- The fixed part of a multiplication decomposition with contracted
second factor is precisely the original first-factor image. -/
theorem range_inf_centralizer_eq_of_subgroupMultiplication
    (hL : SubgroupFunctor.range (l ≫ j) ≤ centralizer χ)
    (hU : SubgroupFunctor.range (r ≫ j) ≤ unipotent χ) :
    SubgroupFunctor.range j ⊓ centralizer χ = SubgroupFunctor.range (l ≫ j) := by
  apply le_antisymm
  · intro T x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx.1
    let a := leviComponent l r y
    let n := radicalComponent l r y
    have ha : a ≫ (l ≫ j).hom.hom ∈ (centralizer χ).carrier T :=
      hL T (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩)
    have hn : n ≫ (r ≫ j).hom.hom ∈ (unipotent χ).carrier T :=
      hU T (SubgroupFunctor.mem_range.mpr ⟨n, rfl⟩)
    have hdecomp : (a ≫ (l ≫ j).hom.hom) * (n ≫ (r ≫ j).hom.hom) = x := by
      have h := congrArg (fun z : T ⟶ P.X => z ≫ j.hom.hom)
        (leviComponent_mul_radicalComponent l r y)
      simpa only [Grp.comp_hom_hom, ← Category.assoc, MonObj.mul_comp, hy] using h
    have hfixed : n ≫ (r ≫ j).hom.hom ∈ (centralizer χ).carrier T := by
      have he : n ≫ (r ≫ j).hom.hom = (a ≫ (l ≫ j).hom.hom)⁻¹ * x := by
        rw [← hdecomp, inv_mul_cancel_left]
      rw [he]
      exact (centralizer χ).carrier T |>.mul_mem (inv_mem ha) hx.2
    have hn1 : n ≫ (r ≫ j).hom.hom = 1 :=
      (hasLimit_of_mem_centralizer χ hfixed).unique χ hn
    rw [hn1, mul_one] at hdecomp
    exact SubgroupFunctor.mem_range.mpr ⟨a, hdecomp⟩
  · intro T x hx
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine ⟨SubgroupFunctor.mem_range.mpr ⟨a ≫ l.hom.hom, ?_⟩,
      hL T (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩)⟩
    exact Category.assoc _ _ _

/-- Ambient centralizer containment identifies the full centralizer
with the original first factor, with no second Levi presentation. -/
theorem centralizer_eq_of_subgroupMultiplication
    (hL : SubgroupFunctor.range (l ≫ j) ≤ centralizer χ)
    (hU : SubgroupFunctor.range (r ≫ j) ≤ unipotent χ)
    (hZ : centralizer χ ≤ SubgroupFunctor.range j) :
    centralizer χ = SubgroupFunctor.range (l ≫ j) := by
  calc
    centralizer χ = SubgroupFunctor.range j ⊓ centralizer χ := by
      apply SubgroupFunctor.ext
      intro T
      exact (inf_eq_right.mpr (hZ T)).symm
    _ = SubgroupFunctor.range (l ≫ j) :=
      range_inf_centralizer_eq_of_subgroupMultiplication l r j χ hL hU

end Dynamic

variable [IsSeparated G.X.hom]
    {A : CommGroupScheme S} (a : A.toGrp ⟶ G)
    (ν : (Gm S).toGrp ⟶ A.toGrp)
    (hL : SubgroupFunctor.range (l ≫ j) ≤ torusCentralizer a)
    (hU : SubgroupFunctor.range (r ≫ j) ≤ Dynamic.unipotent (ν ≫ a))
    (hZ : torusCentralizer a ≤ SubgroupFunctor.range j)

include r ν hL hU hZ

/-- A cocharacter through a commutative group suffices to identify its
whole-group centralizer with the original first multiplication factor. -/
theorem torusCentralizer_eq_of_subgroupMultiplication :
    torusCentralizer a = SubgroupFunctor.range (l ≫ j) := by
  have hfixed := hL.trans (torusCentralizer_le_dynamicCentralizer a ν)
  have heq := Dynamic.range_inf_centralizer_eq_of_subgroupMultiplication
    l r j (ν ≫ a) hfixed hU
  apply le_antisymm
  · intro T x hx
    have hmem : x ∈ (SubgroupFunctor.range j ⊓ Dynamic.centralizer (ν ≫ a)).carrier T :=
      ⟨hZ T hx, torusCentralizer_le_dynamicCentralizer a ν T hx⟩
    rwa [heq] at hmem
  · exact hL

/-- The original first factor is canonically isomorphic to any supplied
representative of the whole-group centralizer, compatibly with its ambient map. -/
def torusCentralizerIsoOfMultiplication
    [Mono (l ≫ j).hom.hom] {m : M ⟶ G}
    (hm : (torusCentralizer a).IsRepresentedBy m) : L ≅ M :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (show (torusCentralizer a).IsRepresentedBy (l ≫ j) from
      ⟨inferInstance, (torusCentralizer_eq_of_subgroupMultiplication l r j a ν hL hU hZ).symm⟩)
    hm

@[simp]
theorem torusCentralizerIsoOfMultiplication_hom_comp
    [Mono (l ≫ j).hom.hom] {m : M ⟶ G}
    (hm : (torusCentralizer a).IsRepresentedBy m) :
    (torusCentralizerIsoOfMultiplication l r j a ν hL hU hZ hm).hom ≫ m = l ≫ j :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[simp]
theorem torusCentralizerIsoOfMultiplication_inv_comp
    [Mono (l ≫ j).hom.hom] {m : M ⟶ G}
    (hm : (torusCentralizer a).IsRepresentedBy m) :
    (torusCentralizerIsoOfMultiplication l r j a ν hL hU hZ hm).inv ≫ l ≫ j = m := by
  have h := congrArg
    (fun f : L ⟶ G =>
      (torusCentralizerIsoOfMultiplication l r j a ν hL hU hZ hm).inv ≫ f)
    (torusCentralizerIsoOfMultiplication_hom_comp l r j a ν hL hU hZ hm)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

end Langlands.GroupScheme
