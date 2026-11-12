import Langlands.GroupScheme.Rational.SplitTorusRankComparison
import Langlands.GroupScheme.CentralIsogeny.SplitTorusLiftComposition
import Langlands.GroupScheme.CentralIsogeny.TorusLift

/-! # Split rank under finite homomorphisms and central isogenies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A finite homomorphism into an affine group cannot decrease split rank. -/
theorem splitRank_le_of_isFinite [IsAffineHom H.X.hom] (f : G ⟶ H)
    [IsFinite f.hom.hom.left] : splitRank G ≤ splitRank H := by
  refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
  let hD := isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I
  let d := hD.dominantFactorization
    (D := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) (i ≫ f)
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion d.inclusion.hom.hom.left := d.isSplitSubtorus.2
  have : IsFinite (d.factor.hom.hom.left ≫ d.inclusion.hom.hom.left) := by
    change IsFinite (d.factor ≫ d.inclusion).hom.hom.left
    rw [d.factor_comp]
    change IsFinite (i.hom.hom.left ≫ f.hom.hom.left)
    infer_instance
  have : IsFinite d.factor.hom.hom.left :=
    IsFinite.of_comp _ d.inclusion.hom.hom.left
  calc
    (Nat.card I : ℕ∞) = splitRank (splitTorus (Spec (CommRingCat.of k)) I) :=
      (splitRank_splitTorus I).symm
    _ ≤ splitRank d.image.toGrp :=
      hD.splitRank_le_of_isFinite d.isSplitSubtorus.1 d.factor
    _ ≤ splitRank H :=
      splitRank_le_of_isClosedSubgroup d.inclusion d.isSplitSubtorus.2

/-- An affine-source central isogeny lifts every closed split torus to a closed split
torus mapping surjectively onto it. -/
theorem IsCentralIsogeny.exists_surjective_splitSubtorus_lift
    [IsAffineHom G.X.hom] {π : G ⟶ H} (hπ : IsCentralIsogeny π)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ H)
    (hS : IsSplitTorus S.toGrp) (hi : IsClosedSubgroup i) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (f : T ⟶ S),
      IsSplitSubtorus j ∧
        Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
        j ≫ π = CommGroupScheme.groupHom f ≫ i := by
  obtain ⟨N, hN0, hN⟩ := hπ.exists_pow_eq_one_kernel
  obtain ⟨a, b, hb, hcomm⟩ :=
    exists_splitParametrization_of_kernel_pow_eq_one hπ i hS hN0 hN
  exact exists_splitSubtorus_lift_of_surjective_splitParametrization
    π a b i hS hi hb hcomm

/-- A central isogeny with affine source cannot increase split rank. -/
theorem IsCentralIsogeny.splitRank_target_le
    [IsAffineHom G.X.hom] {π : G ⟶ H} (hπ : IsCentralIsogeny π) :
    splitRank H ≤ splitRank G := by
  refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
  let S := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  let hS := isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I
  obtain ⟨T, j, f, hj, hf, _⟩ :=
    hπ.exists_surjective_splitSubtorus_lift S i hS hi
  have : Surjective (CommGroupScheme.groupHom f).hom.hom.left := hf
  have : Flat (CommGroupScheme.groupHom f).hom.hom.left :=
    hj.1.isTorus.flat_of_surjective_hom hS.isTorus (CommGroupScheme.groupHom f) hf
  have : Epi (CommGroupScheme.groupHom f).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  calc
    (Nat.card I : ℕ∞) = splitRank S.toGrp := (splitRank_splitTorus I).symm
    _ ≤ splitRank T.toGrp :=
      hj.1.splitRank_le_of_epi hS (CommGroupScheme.groupHom f)
    _ ≤ splitRank G := splitRank_le_of_isClosedSubgroup j hj.2

/-- Central isogenies between affine group schemes preserve split rank over every field. -/
theorem IsCentralIsogeny.splitRank_eq
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {π : G ⟶ H} (hπ : IsCentralIsogeny π) : splitRank G = splitRank H := by
  have : IsFinite π.hom.hom.left := hπ.isFinite
  exact le_antisymm (splitRank_le_of_isFinite π) hπ.splitRank_target_le

/-- The internal arbitrary-universe interface used to transport the quaternionic rank
calculation to a spin cover. -/
def CentralIsogenySplitRankStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (π : G ⟶ H), IsCentralIsogeny π → splitRank G = splitRank H

theorem centralIsogenySplitRankStatement : CentralIsogenySplitRankStatement.{u} := by
  intro k _ G H _ _ π hπ
  exact hπ.splitRank_eq

end Langlands.GroupScheme
