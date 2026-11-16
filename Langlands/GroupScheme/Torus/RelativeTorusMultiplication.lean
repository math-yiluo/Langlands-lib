import Langlands.GroupScheme.Torus.SplitMultiplication
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.FppfHomLocality

/-! # Nonzero multiplication and torsion targets for relative tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Nonzero multiplication on a split torus is flat and surjective over
every base scheme, including the empty scheme. -/
theorem IsSplitTorus.flat_surjective_multiplication_overScheme
    {S : Scheme.{u}} {T : GroupScheme S} [IsCommMonObj T.X]
    (hT : IsSplitTorus T) {n : ℤ} (hn : n ≠ 0) :
    Flat (multiplication T n).hom.hom.left ∧
      Surjective (multiplication T n).hom.hom.left := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let Z := CommRingCat.of (ULift.{u} ℤ)
  let T₀ := splitTorus.commGroupScheme (Spec Z) I
  let b := Gm.toSpecZ S
  let F := GroupScheme.baseChange b
  let E : T ≅ F.obj T₀.toGrp :=
    e ≪≫ (splitTorus.baseChangeIso b I).symm
  obtain ⟨hf, hs⟩ :=
    (isSplitTorus_splitTorus I (S := Spec Z)).flat_and_surjective_multiplication
      (S := T₀) hn
  have hflat : Flat (F.map (multiplication T₀.toGrp n)).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Flat)
      (baseChange_map_isPullback b (multiplication T₀.toGrp n)).flip hf
  have hsurj : Surjective (F.map (multiplication T₀.toGrp n)).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (baseChange_map_isPullback b (multiplication T₀.toGrp n)).flip hs
  have hmul : multiplication T n =
      E.hom ≫ F.map (multiplication T₀.toGrp n) ≫ E.inv := by
    rw [multiplication_baseChange, ← Category.assoc, ← multiplication_naturality, Category.assoc,
      E.hom_inv_id, Category.comp_id]
  have : IsIso E.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso E.hom
  have : IsIso E.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso E.inv
  rw [hmul]
  change Flat (E.hom.hom.hom.left ≫
      (F.map (multiplication T₀.toGrp n)).hom.hom.left ≫ E.inv.hom.hom.left) ∧
    Surjective (E.hom.hom.hom.left ≫
      (F.map (multiplication T₀.toGrp n)).hom.hom.left ≫ E.inv.hom.hom.left)
  exact ⟨inferInstance, inferInstance⟩

/-- Multiplication by a nonzero integer detects equality of homomorphisms
out of any relative torus. -/
theorem RelativeTorus.IsTorus.cancel_multiplication
    {S : Scheme.{u}} {T H : GroupScheme S} [IsCommMonObj T.X]
    (hT : RelativeTorus.IsTorus T) {n : ℤ} (hn : n ≠ 0)
    {f g : T ⟶ H}
    (h : multiplication T n ≫ f = multiplication T n ≫ g) : f = g := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  let 𝒱 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun i => ⟨inferInstance, inferInstance⟩)
  apply hom_ext_of_baseChange_fppfCover 𝒱
  intro i
  let b := 𝒰.f i
  let F := GroupScheme.baseChange b
  obtain ⟨hf, hs⟩ := (h𝒰 i).flat_surjective_multiplication_overScheme hn
  have : Flat (multiplication (F.obj T) n).hom.hom.left := hf
  have : Surjective (multiplication (F.obj T) n).hom.hom.left := hs
  have : Epi (multiplication (F.obj T) n).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hh : multiplication (F.obj T) n ≫ F.map f =
      multiplication (F.obj T) n ≫ F.map g := by
    have hh := congrArg F.map h
    dsimp only [F] at hh
    simpa only [Functor.map_comp, multiplication_baseChange] using hh
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi (multiplication (F.obj T) n).hom.hom.left).mp
  exact congrArg (fun a => a.hom.hom.left) hh

/-- Every map from a relative torus to a group annihilated by a nonzero
integer is trivial. -/
theorem RelativeTorus.IsTorus.hom_eq_one_of_multiplication_eq_one
    {S : Scheme.{u}} {T H : GroupScheme S}
    [IsCommMonObj T.X] [IsCommMonObj H.X]
    (hT : RelativeTorus.IsTorus T) {n : ℤ} (hn : n ≠ 0)
    (hH : multiplication H n = 1) (f : T ⟶ H) : f = 1 := by
  apply hT.cancel_multiplication hn
  rw [multiplication_naturality, hH]
  simp

end Langlands.GroupScheme
