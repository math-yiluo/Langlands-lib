import Langlands.GroupScheme.Rational.UnipotentTorsionCenter
import Langlands.GroupScheme.Rational.VectorActionCharZero
import Langlands.GroupScheme.Rational.VectorCoordinateGeometry
import Langlands.GroupScheme.Rational.CommutativeVectorClassificationStatement
import Langlands.GroupScheme.Rational.SplitTorusVectorLinearizationStatement
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Mathlib.Algebra.CharP.Defs

/-! # Central vector subgroups from explicit classification inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Actual central vector-subgroup data, retaining the restricted action,
commutativity and geometric connectedness of the constructed subgroup. -/
structure CentralStableVectorSubgroupData
    {k : Type u} [Field k] {H G : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction H G) where
  subgroup : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : subgroup.toGrp ⟶ G
  action : AutomorphicAction H subgroup.toGrp
  dimension : ℕ
  coordinates : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ subgroup.X) ≃* Multiplicative (Fin dimension → Γ(T.left, ⊤))
  closed : IsClosedSubgroup inclusion
  smooth : Smooth subgroup.X.hom
  affine : IsAffineHom subgroup.X.hom
  geometricallyConnected : GeometricallyConnected subgroup.X.hom
  connected : ConnectedSpace subgroup.X.left
  unipotent : IsUnipotent subgroup.toGrp
  central : IsCentral inclusion
  stable : b.IsStable (SubgroupFunctor.range inclusion)
  nontrivial : SubgroupFunctor.range inclusion ≠ ⊥
  positive_dimension : 0 < dimension
  smoothDimension : SmoothOfRelativeDimension dimension subgroup.X.hom
  linear : IsLinearVectorCoordinates action coordinates
  equivariant : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
    (v : T ⟶ subgroup.X),
    action.act h v ≫ inclusion.hom.hom = b.act h (v ≫ inclusion.hom.hom)

section CharacteristicZero

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- In characteristic zero, classification and closed-subgroup unipotence
suffice for any affine acting group, without a torus linearization premise. -/
theorem nonempty_centralStableVectorSubgroupData_of_charZero
    (hclass : CommutativeUnipotentVectorCharZeroStatement.{u})
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (b : AutomorphicAction H G) (hH : IsAffineHom H.X.hom)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    Nonempty (CentralStableVectorSubgroupData b) := by
  obtain ⟨Z, z, bZ, hc, hs, ha, hgc, hco, hcent, hstable, hnt, heq⟩ :=
    hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent b hH hG hU
  let : IsClosedImmersion z.hom.hom.left := hc
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  have hZU : IsUnipotent Z := hsub k G Z z hc hU
  obtain ⟨n, e, he⟩ := hclass k hcent.commGroupScheme hs ha hco hZU
  have hvec : IsVectorGroupOfDimension Z n := ⟨e, he⟩
  let : IsAffineHom H.X.hom := hH
  exact ⟨{
    subgroup := hcent.commGroupScheme
    inclusion := z
    action := bZ
    dimension := n
    coordinates := e
    closed := hc
    smooth := hs
    affine := ha
    geometricallyConnected := hgc
    connected := hco
    unipotent := hZU
    central := hcent
    stable := hstable
    nontrivial := hnt
    positive_dimension := hvec.pos_of_range_ne_bot_overRing z hnt
    smoothDimension := hvec.smoothOfRelativeDimension_overRing
    linear := isLinearVectorCoordinates_of_charZero he
    equivariant := heq }⟩

end CharacteristicZero

section PositiveCharacteristic

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- In prime characteristic, use the constructed torsion centre, the supplied
commutative p-torsion classification and whole-vector torus linearization. -/
theorem nonempty_centralStableVectorSubgroupData_of_charP
    (hclass : SmoothCommutativePTorsionVectorStatement.{u})
    (hlin : SplitTorusVectorLinearizationStatement.{u})
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    Nonempty (CentralStableVectorSubgroupData b) := by
  obtain ⟨Z, z, bZ, hc, hs, ha, hgc, hco, hcent, hstable, hnt, hexp, heq⟩ :=
    hasNontrivialSmoothStableTorsionCentralSubgroup_of_isUnipotent p b hS.isAffineHom hG hU
  have hZU : IsUnipotent Z.toGrp := hsub k G Z.toGrp z hc hU
  have hvec : IsVectorGroup Z.toGrp := hclass k p Z hs ha hco hexp
  obtain ⟨n, e, he⟩ := hlin k Z.toGrp hvec S hS bZ
  have hdim : IsVectorGroupOfDimension Z.toGrp n := ⟨e, he.1⟩
  exact ⟨{
    subgroup := Z
    inclusion := z
    action := bZ
    dimension := n
    coordinates := e
    closed := hc
    smooth := hs
    affine := ha
    geometricallyConnected := hgc
    connected := hco
    unipotent := hZU
    central := hcent
    stable := hstable
    nontrivial := hnt
    positive_dimension := hdim.pos_of_range_ne_bot_overRing z hnt
    smoothDimension := hdim.smoothOfRelativeDimension_overRing
    linear := he
    equivariant := heq }⟩

end PositiveCharacteristic

/-- Characteristic splitting combines the two constructions. -/
theorem nonempty_centralStableVectorSubgroupData_of_classification
    (hclass : CommutativeVectorClassificationStatement.{u})
    (hlin : SplitTorusVectorLinearizationStatement.{u})
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    Nonempty (CentralStableVectorSubgroupData b) := by
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let : CharZero k := hzero
    exact nonempty_centralStableVectorSubgroupData_of_charZero
      hclass.1 hsub b hS.isAffineHom hG hU
  · let : Fact p.Prime := hp
    let : CharP k p := hchar
    exact nonempty_centralStableVectorSubgroupData_of_charP
      hclass.2 hlin hsub p S hS b hG hU

/-- Choose actual central vector-subgroup data from the explicitly supplied
classification, torus-linearization and closed-subgroup-unipotence results. -/
def centralStableVectorSubgroupOfClassification
    (hclass : CommutativeVectorClassificationStatement.{u})
    (hlin : SplitTorusVectorLinearizationStatement.{u})
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    CentralStableVectorSubgroupData b :=
  Classical.choice (nonempty_centralStableVectorSubgroupData_of_classification
    hclass hlin hsub k G S hS b hG hU)

/-- The exact existing central-vector target follows from the three explicit
structural inputs at every universe. -/
theorem centralStableVectorSubgroup_of_classification
    (hclass : CommutativeVectorClassificationStatement.{u})
    (hlin : SplitTorusVectorLinearizationStatement.{u})
    (hsub : UnipotentClosedSubgroupStatement.{u}) :
    CentralStableVectorSubgroupStatement.{u} := by
  intro k _ _ G hs ha hco hU hG S hS b
  let : Smooth G.X.hom := hs
  let : IsAffineHom G.X.hom := ha
  let : ConnectedSpace G.X.left := hco
  let D := centralStableVectorSubgroupOfClassification hclass hlin hsub k G S hS b hG hU
  exact ⟨D.subgroup.toGrp, D.inclusion, D.action, D.dimension, D.coordinates,
    D.closed, D.smooth, D.affine, D.connected, D.unipotent, D.central, D.stable,
    D.nontrivial, D.positive_dimension, D.smoothDimension, D.linear, D.equivariant⟩

end Langlands.GroupScheme.RelativeRoot
