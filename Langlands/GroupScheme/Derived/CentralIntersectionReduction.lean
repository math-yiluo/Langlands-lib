import Langlands.GroupScheme.Derived.CentralIntersectionPullback
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Reduction of the central-intersection finiteness to an algebraic closure -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Preimages of subgroup functors commute with arbitrary base change. -/
theorem SubgroupFunctor.comap_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {H G : GroupScheme S} (f : H ⟶ G) (F : SubgroupFunctor G) :
    (F.comap f).baseChange b = (F.baseChange b).comap ((GroupScheme.baseChange b).map f) := by
  ext T x
  rw [SubgroupFunctor.mem_baseChange, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_comap,
    SubgroupFunctor.mem_baseChange, baseChangePointsEquiv_comp]

variable {k : Type u} [Field k]

/-- A scheme over a field whose base change to an algebraic closure has finitely many points has
finitely many points. -/
theorem finite_left_of_finite_pullback (X : Over (Spec (CommRingCat.of k)))
    (h : Finite (pullback X.hom (toAlgebraicClosure k)).carrier) : Finite X.left := by
  have : Surjective (toAlgebraicClosure k) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint (AlgebraicClosure k), Subsingleton.elim _ _⟩⟩
  have hsurj : Surjective (pullback.fst X.hom (toAlgebraicClosure k)) := inferInstance
  exact Finite.of_surjective _ hsurj.surj

/-- A quasi-compact scheme locally of finite type over a field with finitely many points is
finite over the field. -/
theorem isFinite_hom_of_finite_left (X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (h : Finite X.left) : IsFinite X.hom := by
  have : LocallyQuasiFinite X.hom :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have : IsLocallyArtinian (Spec (CommRingCat.of k)) := by
    rw [Scheme.isLocallyArtinianScheme_Spec]
    change IsArtinianRing k
    infer_instance
  exact IsFinite.of_locallyQuasiFinite X.hom

/-- A closed subgroup of a closed subgroup of a quasi-compact group locally of finite type over a
field is finite as soon as its base change to an algebraic closure has finitely many points. -/
theorem isFinite_of_finite_pullback {G D C : GroupScheme (Spec (CommRingCat.of k))}
    (d : D ⟶ G) (c : C ⟶ D) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hd : IsClosedSubgroup d) (hc : IsClosedSubgroup c)
    (h : Finite (pullback C.X.hom (toAlgebraicClosure k)).carrier) : IsFinite C.X.hom := by
  have : IsClosedImmersion c.hom.hom.left := hc
  have : IsClosedImmersion d.hom.hom.left := hd
  have : LocallyOfFiniteType C.X.hom := by
    rw [← Over.w c.hom.hom, ← Over.w d.hom.hom]
    infer_instance
  have : QuasiCompact C.X.hom := by
    rw [← Over.w c.hom.hom, ← Over.w d.hom.hom]
    infer_instance
  exact isFinite_hom_of_finite_left C.X (finite_left_of_finite_pullback C.X h)

/-- The finiteness statement follows from finiteness, over algebraically closed fields, of every
closed subgroup of an actual derived subgroup whose points are central in the ambient group. -/
theorem derivedCentralIntersectionFiniteness_of_algClosed
    (hfin : ∀ {K : Type u} [Field K] [IsAlgClosed K]
      {G D S : GroupScheme (Spec (CommRingCat.of K))} (d : D ⟶ G) (s : S ⟶ D)
      [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
      HasTrivialUnipotentRadical G → IsDerivedSubgroup d → IsClosedSubgroup s →
        SubgroupFunctor.range s ≤ (center G).comap d → Finite S.X.left) :
    DerivedCentralIntersectionFinitenessStatement.{u} := by
  apply derivedCentralIntersectionFiniteness_of_isFinite_subgroupIntersection
  intro k _ G D Z d z hG hd hz
  let b := toAlgebraicClosure k
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  let GK := (GroupScheme.baseChange b).obj G
  have : IsAffine GK.X.left := by
    change IsAffine (pullback G.X.hom b)
    exact isAffine_of_isAffineHom (pullback.snd G.X.hom b)
  have : LocallyOfFiniteType GK.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have hdK : IsDerivedSubgroup ((GroupScheme.baseChange b).map d) :=
    (derivedSubgroupFieldBaseChange k (AlgebraicClosure k) G D d hd).1
  have hc := isClosedSubgroup_subgroupIntersectionFst d hz.1
  have hrange :
      SubgroupFunctor.range ((GroupScheme.baseChange b).map (subgroupIntersectionFst d z)) =
        (center GK).comap ((GroupScheme.baseChange b).map d) := by
    rw [SubgroupFunctor.range_baseChangeHom,
      range_subgroupIntersectionFst_of_isSchemeTheoreticCenter d hz,
      SubgroupFunctor.comap_baseChange, center_baseChange]
  have hK : Finite ((GroupScheme.baseChange b).obj (subgroupIntersection d z)).X.left :=
    hfin ((GroupScheme.baseChange b).map d)
      ((GroupScheme.baseChange b).map (subgroupIntersectionFst d z))
      hG.hasTrivialGeometricUnipotentRadical hdK (hc.baseChange b) hrange.le
  exact isFinite_of_finite_pullback d (subgroupIntersectionFst d z) hd.1 hc hK

end Langlands.GroupScheme
