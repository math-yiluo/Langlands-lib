import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityStatement
import Langlands.GroupScheme.Derived.NormalizedProductDifferential
import Langlands.GroupScheme.Derived.TorusTangent
import Langlands.GroupScheme.Derived.SmoothnessProof
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Derived multiplication from maximal-torus selfcentralization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

section Split

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A supplied full derived subgroup and a closed split selfcentralizing torus
multiply smoothly and surjectively in a smooth connected affine group. -/
theorem IsDerivedSubgroup.smoothSurjective_product_of_split_selfCentralizing
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    Smooth (subgroupProductMap d i).left ∧
      Surjective (subgroupProductMap d i).left := by
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : Mono d.hom.hom := hd.isRepresentedBy.1
  let : IsAffineHom D.X.hom := hd.1.isAffineHom
  let : Smooth D.X.hom := derivedSubgroupSmoothness k G D d hd inferInstance
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : Smooth T.toGrp.X.hom := hT.smooth
  apply smoothSurjective_subgroupProductMap_of_normal_of_tangentSpan d i hd.isNormal
  rw [← RelativeRoot.tangentSubmodule_range d,
    ← RelativeRoot.tangentSubmodule_range i]
  exact hd.tangentSubmodule_range_sup_selfCentralizing_torus_eq_top i hT hself

end Split

section Descent

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Splitting-field descent removes splitness from the smooth-surjectivity
criterion for a supplied derived subgroup and closed selfcentralizing torus. -/
theorem IsDerivedSubgroup.smoothSurjective_product_of_selfCentralizing
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (i : T.toGrp ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    Smooth (subgroupProductMap d i).left ∧
      Surjective (subgroupProductMap d i).left := by
  obtain ⟨K, hK, aK, hsplit⟩ := hT
  let : Field K := hK
  let : Algebra k K := aK
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let bc := GroupScheme.baseChange b
  let TK := (CommGroupScheme.baseChange b).obj T
  have hdK : IsDerivedSubgroup (bc.map d) :=
    (derivedSubgroupFieldBaseChange k K G D d hd).1
  have hiK : IsClosedSubgroup (bc.map i) := hi.baseChange b
  have hselfK : torusCentralizer (T := TK) (bc.map i) =
      SubgroupFunctor.range (bc.map i) := by
    rw [torusCentralizer_baseChange, hself]
    exact (SubgroupFunctor.range_baseChangeHom b i).symm
  let : Smooth (bc.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom (bc.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : ConnectedSpace (bc.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have h := hdK.smoothSurjective_product_of_split_selfCentralizing
    (T := TK) (bc.map i) hsplit hiK hselfK
  exact smooth_surjective_subgroupMultiplication_of_fieldExtension
    (K := K) d i h.1 h.2

end Descent

/-- The all-field maximal-torus centralizer theorem is sufficient for the
exact derived/maximal-torus product surjectivity proposition. -/
def DerivedMaximalTorusProductCentralizerReductionStatement : Prop :=
  MaximalTorusCentralizerStatement.{u} →
    DerivedMaximalTorusProductSurjectivityStatement.{u}

/-- Conditional assembly, retaining the maximal-torus selfcentralization
statement as the sole structural input. -/
theorem derivedMaximalTorusProductSurjectivity_of_maximalTorusCentralizer :
    DerivedMaximalTorusProductCentralizerReductionStatement.{u} := by
  intro hcent k _ G D T d i hG hd hi
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  exact (hd.smoothSurjective_product_of_selfCentralizing i hi.1 hi.2.1
    (hcent k G hG T i hi)).2

end Langlands.GroupScheme
