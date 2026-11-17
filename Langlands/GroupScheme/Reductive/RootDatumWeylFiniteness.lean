import Langlands.GroupScheme.Torus.WeylGroupSchemeFibreCardinality
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Reductive.LocalSplitBigCellProof
import Langlands.LinearAlgebra.RootDatumWeylChambers

/-! # Finiteness of the full Weyl groups of supplied fibrewise root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.IsRootDatumOf

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hP : IsRootDatumOf i P)

/-- The full abstract integral Weyl group maps into the actual normalizer
image by its action on the whole character lattice. -/
def weylGroupImageHom : P.weylGroup →* weylImage i where
  toFun w := ⟨w.val.weightEquiv, hP.abstractWeylImage_le ⟨w.val, w.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (RootPairing.Equiv.weightHom P))
  map_mul' a b := Subtype.ext (map_mul (RootPairing.Equiv.weightHom P) a.val b.val)

/-- The full-lattice Weyl image map is injective, including central directions. -/
theorem weylGroupImageHom_injective : Function.Injective hP.weylGroupImageHom := by
  intro a b h
  apply Subtype.ext
  exact RootPairing.Equiv.weightHom_injective P (congrArg Subtype.val h)

include hP in
/-- Actual root data of a closed split torus in an affine algebraic group
have finite full integral Weyl group. -/
theorem finite_weylGroup_of_closed_split [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i) : Finite P.weylGroup := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi
  exact Finite.of_injective hP.weylGroupImageHom hP.weylGroupImageHom_injective

end Langlands.GroupScheme.IsRootDatumOf

namespace Langlands.GroupScheme.IsFibrewiseRootDatumOf

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P)

include hP in
/-- Any supplied field fibre proves finiteness of the original full
coordinate root datum's Weyl group. -/
theorem finite_weylGroup_of_field (hG : IsReductive G)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (k : Type u) [Field k] [Algebra R k] : Finite P.weylGroup := by
  have := hG.smooth
  let GK := (baseChange (algebraBaseMap R k)).obj G
  let iK := splitTorus.baseChangeHom (K := k) G I i
  have hGK : IsConnectedReductive GK := hG.isConnectedReductive_baseChange _
  let := hGK.isAffineHom
  have hiK : IsMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) iK :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k
  let : IsClosedImmersion iK.hom.hom.left := hiK.2.1
  have := hGK.smooth
  let Q := CoordinateRootDatum.fieldRealization k P
  let : Finite Q.weylGroup := (hP.field k).finite_weylGroup_of_closed_split
    (isSplitTorus_splitTorus I) hiK.2.1
  let e := rootDatumWeylGroupEquiv (CoordinateRootDatum.fieldRealizationEquiv k P)
  exact Finite.of_injective e e.injective

include hP in
/-- A nontrivial base ring supplies a field fibre, so no abstract Weyl
finiteness hypothesis is needed for its actual fibrewise coordinate datum. -/
theorem finite_weylGroup [Nontrivial R] (hG : IsReductive G)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i) :
    Finite P.weylGroup := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let : m.IsMaximal := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  exact hP.finite_weylGroup_of_field hG hi (R ⧸ m)

include hP in
/-- Every zero-root reflection subgroup of an actual fibrewise datum over a
nontrivial ring is finite. -/
theorem finite_zeroReflectionSubgroup [Nontrivial R] (hG : IsReductive G)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (cv : I → ℤ) :
    Finite (Langlands.LinearAlgebra.RootDatumWeylChambers.reflectionSubgroup
      P {a | P.root' a cv = 0}) := by
  let := hP.finite_weylGroup hG hi
  infer_instance

end Langlands.GroupScheme.IsFibrewiseRootDatumOf
