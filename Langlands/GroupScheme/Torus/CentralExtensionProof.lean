import Langlands.GroupScheme.Torus.CentralExtensionStatement
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.FppfQuotientComparison

/-! # A central extension of a torus by a torus is a torus

This proves `CentralTorusExtensionStatement`. All hypotheses are stable under base change of
the ground field. After passing to a field extension splitting `Z` and then to one splitting
`T`, the quotient `T` is affine, so `E` is affine, and the split case
`CentralExtensionHopfSpec.isSplitTorus_of_split` applies. Tori descend along field
extensions by `IsTorus.of_baseChange`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S}

/-- A property of morphisms of schemes stable under base change passes from a homomorphism
to its base change. -/
theorem baseChange_map_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (f : H ⟶ G) (hf : P f.hom.hom.left) :
    P ((GroupScheme.baseChange b).map f).hom.hom.left :=
  MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip hf

open RelativeRoot in
/-- The hypotheses of `CentralTorusExtensionStatement` on `z` and `p` survive base change. -/
theorem centralExtension_baseChange {E Z T : GroupScheme S} (z : Z ⟶ E) (p : E ⟶ T)
    (hz : IsClosedSubgroup z) (hc : IsCentral z) (hp : IsAffineHom p.hom.hom.left)
    (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    IsClosedSubgroup ((GroupScheme.baseChange b).map z) ∧
      IsCentral ((GroupScheme.baseChange b).map z) ∧
      IsAffineHom ((GroupScheme.baseChange b).map p).hom.hom.left ∧
      IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map z))
        ((GroupScheme.baseChange b).map p) := by
  refine ⟨hz.baseChange b, hc.baseChange b,
    baseChange_map_of_isStableUnderBaseChange b @IsAffineHom p hp, ?_⟩
  rw [SubgroupFunctor.range_baseChangeHom]
  exact hq.baseChange b

end BaseChange

/-- A central extension of a torus by a torus is a torus (Milne 12.41 and 12.22). -/
theorem centralTorusExtensionStatement : CentralTorusExtensionStatement.{u} := by
  intro k _ E Z z hZ hz hc T p hT hp hq
  obtain ⟨K1, hK1, a1, hZ1⟩ := hZ
  let : Field K1 := hK1
  let : Algebra k K1 := a1
  obtain ⟨K2, hK2, a2, hT2⟩ := hT.baseChange (K := K1)
  let : Field K2 := hK2
  let : Algebra K1 K2 := a2
  let b1 := Spec.map (CommRingCat.ofHom (algebraMap k K1))
  let b2 := Spec.map (CommRingCat.ofHom (algebraMap K1 K2))
  obtain ⟨hz1, hc1, hp1, hq1⟩ := centralExtension_baseChange b1 z p hz hc hp hq
  obtain ⟨hz2, hc2, hp2, hq2⟩ := centralExtension_baseChange b2 _ _ hz1 hc1 hp1 hq1
  obtain ⟨J, _, ⟨eZ⟩⟩ := hZ1.baseChange b2
  obtain ⟨I, _, ⟨eT⟩⟩ := hT2
  have : IsAffineHom (splitTorus (Spec (CommRingCat.of K2)) I).X.hom :=
    isAffineHom_splitTorus _ I
  have : IsAffine (splitTorus (Spec (CommRingCat.of K2)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of K2)) I).X.hom
  have : IsIso eT.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eT)).hom)
  have : IsAffine ((GroupScheme.baseChange b2).obj
      ((GroupScheme.baseChange b1).obj T.toGrp)).X.left :=
    IsAffine.of_isIso eT.hom.hom.hom.left
  have : IsAffine ((GroupScheme.baseChange b2).obj
      ((GroupScheme.baseChange b1).obj E)).X.left := by
    have := hp2
    exact isAffine_of_isAffineHom
      ((GroupScheme.baseChange b2).map ((GroupScheme.baseChange b1).map p)).hom.hom.left
  apply IsTorus.of_baseChange (K := K1)
  apply IsTorus.of_baseChange (K := K2)
  exact (CentralExtensionHopfSpec.isSplitTorus_of_split eZ eT _ hz2 hc2 _ hq2).isTorus

end Langlands.GroupScheme
