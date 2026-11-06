import Langlands.BruhatTits.Cartan.ActualCentralizerStructureStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.Statement

/-! # The split component of the represented centralizer of a maximal split torus -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} {j : Z ⟶ G}

/-- A homomorphism whose composite with a closed subgroup is a closed subgroup is itself a
closed subgroup. -/
theorem IsClosedSubgroup.of_comp {H : GroupScheme (Spec (CommRingCat.of F))} {f : H ⟶ Z}
    (hj : IsClosedSubgroup j) (hf : IsClosedSubgroup (f ≫ j)) : IsClosedSubgroup f := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion (f.hom.hom.left ≫ j.hom.hom.left) := hf
  exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left j.hom.hom.left

/-- The composite of two closed subgroups is a closed subgroup. -/
theorem IsClosedSubgroup.comp' {H : GroupScheme (Spec (CommRingCat.of F))} {f : H ⟶ Z}
    (hf : IsClosedSubgroup f) (hj : IsClosedSubgroup j) : IsClosedSubgroup (f ≫ j) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion f.hom.hom.left := hf
  change IsClosedImmersion (f.hom.hom.left ≫ j.hom.hom.left)
  infer_instance

/-- Every point of a representative of the torus centralizer commutes, inside that
representative, with every point of a torus factorization through it. -/
theorem isCentral_of_torusCentralizer (hZ : (torusCentralizer i).IsRepresentedBy j)
    {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) : IsCentral s := by
  intro T x T' a h
  have hmono : Mono j.hom.hom := hZ.1
  have hh : h ≫ j.hom.hom ∈ (torusCentralizer i).carrier T' := by
    rw [← hZ.2]
    exact ⟨h, rfl⟩
  have hc := hh T' (𝟙 T') (a ≫ x)
  rw [Category.id_comp, ← hs, Grp.comp_hom_hom, ← Category.assoc] at hc
  apply hmono.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp, ← Category.assoc]
  exact hc.symm.eq

variable (hi : IsMaximalSplitTorus i)
include hi

/-- A torus factorization through the closed representative of the torus centralizer is a
split subtorus of that representative. -/
theorem isSplitSubtorus_of_torusCentralizer (hj : IsClosedSubgroup j)
    {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) : IsSplitSubtorus s := by
  refine ⟨hi.1.1, IsClosedSubgroup.of_comp hj ?_⟩
  rw [hs]
  exact hi.1.2

/-- The factorization of a maximal split torus through the closed representative of its
whole torus centralizer is a split component of that representative. -/
theorem isSplitComponent_of_torusCentralizer (hj : IsClosedSubgroup j)
    (hZ : (torusCentralizer i).IsRepresentedBy j) {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) :
    IsSplitComponent s := by
  refine ⟨⟨isSplitSubtorus_of_torusCentralizer hi hj hs, isCentral_of_torusCentralizer hZ hs⟩,
    ?_⟩
  intro A' i' hi' f hf
  refine hi.2 A' (i' ≫ j) ⟨hi'.1.1, IsClosedSubgroup.comp' hi'.1.2 hj⟩ f ?_
  rw [← Category.assoc, hf, hs]

/-- The represented torus centralizer is connected reductive, given generic centralizers and
connected reductivity of represented dynamic centralizers. -/
theorem isConnectedReductive_of_torusCentralizer
    (hgen : GenericCentralizerStatement.{u}) (hdyn : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (hj : IsClosedSubgroup j)
    (hZ : (torusCentralizer i).IsRepresentedBy j) : IsConnectedReductive Z := by
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨ν, hν⟩ := hi.1.1.exists_genericCocharacter i
  refine hdyn F G hG (CommGroupScheme.groupHom ν ≫ i) Z j hj ?_
  rw [hgen F G hG S i hi ν hν]
  exact hZ

omit hi in
/-- The structural target, given generic centralizers and connected reductivity of
represented dynamic centralizers. -/
theorem actualCentralizerStructure_of
    (hgen : GenericCentralizerStatement.{u}) (hdyn : DynamicCentralizerReductiveStatement.{u}) :
    ActualCentralizerStructureStatement.{u} :=
  fun _ _ _ hG _ _ hi _ _ hj hZ _ hs =>
    ⟨isConnectedReductive_of_torusCentralizer hi hgen hdyn hG hj hZ,
      isSplitComponent_of_torusCentralizer hi hj hZ hs⟩

end Langlands.BruhatTits.Cartan
