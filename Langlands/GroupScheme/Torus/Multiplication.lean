import Langlands.GroupScheme.Torus.SplitMultiplication
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection

/-! # Nonzero multiplication on an arbitrary torus over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Multiplication by a nonzero integer on an actual torus is flat and
surjective, with no splitting or separability hypothesis over the ground field. -/
theorem IsTorus.flat_and_surjective_multiplication
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T.toGrp) {n : ℤ} (hn : n ≠ 0) :
    Flat (multiplication T.toGrp n).hom.hom.left ∧
      Surjective (multiplication T.toGrp n).hom.hom.left := by
  let E := hT.splittingExtension
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E.carrier))
  have : Surjective b := (fieldExtension_fpqc k E.carrier).1
  have : Flat b := (fieldExtension_fpqc k E.carrier).2.1
  have : QuasiCompact b := (fieldExtension_fpqc k E.carrier).2.2
  let T' : CommGroupScheme (Spec (CommRingCat.of E.carrier)) :=
    { (GroupScheme.baseChange b).obj T.toGrp with comm := inferInstance }
  have hs : IsSplitTorus T'.toGrp := E.isSplitTorus
  obtain ⟨hf, he⟩ := hs.flat_and_surjective_multiplication hn
  have hmul : (GroupScheme.baseChange b).map (multiplication T.toGrp n) =
      multiplication T'.toGrp n := multiplication_baseChange b T.toGrp n
  have hf' : Flat ((GroupScheme.baseChange b).map
      (multiplication T.toGrp n)).hom.hom.left := by rw [hmul]; exact hf
  have he' : Surjective ((GroupScheme.baseChange b).map
      (multiplication T.toGrp n)).hom.hom.left := by rw [hmul]; exact he
  have hp := baseChange_map_isPullback b (multiplication T.toGrp n)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst T.toGrp.X.hom b) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf',
    MorphismProperty.of_isPullback_of_descendsAlong hp hQ he'⟩

/-- The universe-general nonzero multiplication assertion for all field tori. -/
def TorusMultiplicationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsTorus T.toGrp → ∀ (n : ℤ), n ≠ 0 →
      Flat (multiplication T.toGrp n).hom.hom.left ∧
      Surjective (multiplication T.toGrp n).hom.hom.left

theorem torusMultiplicationStatement : TorusMultiplicationStatement.{u} := by
  intro k _ T hT n hn
  exact hT.flat_and_surjective_multiplication hn

end Langlands.GroupScheme
