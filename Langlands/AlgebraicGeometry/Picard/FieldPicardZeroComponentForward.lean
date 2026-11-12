import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroComponentAssembly
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleNormalization
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # The Picard-zero-to-origin-component direction -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

section Transport

variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (C : Over T.left)

/-- The abelian scheme over `T.left` on which a geometric smooth-family witness lives. -/
abbrev witnessScheme : AbelianScheme T.left :=
  (baseChange (𝟙 T.left)).obj ((baseChange T.hom).obj A)

/-- The comparison map from `C ×_S A` to the witness product `C ×_{T} B`. -/
def witnessSpaceMap :
    (relativeSpace A.X.hom).obj ((Over.map T.hom).obj C) ⟶
      (relativeSpace (witnessScheme A T).X.hom).obj C :=
  pullback.lift (pullback.fst (C.hom ≫ T.hom) A.X.hom)
    (pullback.lift
      (pullback.lift (pullback.snd (C.hom ≫ T.hom) A.X.hom)
        (pullback.fst (C.hom ≫ T.hom) A.X.hom ≫ C.hom)
        (by rw [Category.assoc]; exact pullback.condition.symm))
      (pullback.fst (C.hom ≫ T.hom) A.X.hom ≫ C.hom)
      (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _))
    (pullback.lift_snd _ _ _).symm

/-- The identification of `T ×_S A` with the witness abelian scheme. -/
def witnessSymmetry :
    (relativeSpace A.X.hom).obj T ⟶ (witnessScheme A T).X.left :=
  pullback.lift (relativeSpaceSymmetry A.X.hom T).hom (pullback.fst T.hom A.X.hom)
    (by rw [Category.comp_id]; exact pullbackSymmetry_hom_comp_snd _ _)

/-- A rational point of `C` as a morphism of `S`-schemes from `T`. -/
def witnessPoint (c : Over.mk (𝟙 T.left) ⟶ C) : T ⟶ (Over.map T.hom).obj C :=
  Over.homMk c.left (by
    rw [Over.map_obj_hom, ← Category.assoc, Over.w c]
    exact Category.id_comp _)

lemma witnessPoint_projection (c : Over.mk (𝟙 T.left) ⟶ C) :
    (relativeSpace A.X.hom).map (witnessPoint T C c) ≫
        (relativeProjection A.X.hom).app ((Over.map T.hom).obj C) =
      pullback.fst T.hom A.X.hom ≫ c.left :=
  (relativeProjection A.X.hom).naturality (witnessPoint T C c)

lemma witnessPoint_fst (c : Over.mk (𝟙 T.left) ⟶ C) :
    (relativeSpace A.X.hom).map (witnessPoint T C c) ≫ pullback.fst (C.hom ≫ T.hom) A.X.hom =
      pullback.fst T.hom A.X.hom ≫ c.left :=
  witnessPoint_projection A T C c

lemma witnessPoint_snd (c : Over.mk (𝟙 T.left) ⟶ C) :
    (relativeSpace A.X.hom).map (witnessPoint T C c) ≫ pullback.snd (C.hom ≫ T.hom) A.X.hom =
      pullback.snd T.hom A.X.hom :=
  pullback.lift_snd _ _ _

lemma witnessSymmetry_fst :
    witnessSymmetry A T ≫ pullback.fst _ (𝟙 T.left) = (relativeSpaceSymmetry A.X.hom T).hom :=
  pullback.lift_fst _ _ _

lemma witnessSymmetry_snd :
    witnessSymmetry A T ≫ pullback.snd _ (𝟙 T.left) = pullback.fst T.hom A.X.hom :=
  pullback.lift_snd _ _ _

lemma witnessSymmetry_hom :
    witnessSymmetry A T ≫ (witnessScheme A T).X.hom = pullback.fst T.hom A.X.hom :=
  pullback.lift_snd _ _ _

lemma witnessPoint_spaceMap (c : Over.mk (𝟙 T.left) ⟶ C) :
    (relativeSpace A.X.hom).map (witnessPoint T C c) ≫ witnessSpaceMap A T C =
      witnessSymmetry A T ≫ smoothFamilyPointMap (witnessScheme A T) C c := by
  have hc : c.left ≫ C.hom = 𝟙 T.left := Over.w c
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, smoothFamilyPointMap_fst, ← Category.assoc
      (witnessSymmetry A T), witnessSymmetry_hom, witnessSpaceMap, pullback.lift_fst,
      witnessPoint_fst]
  · rw [Category.assoc, Category.assoc, smoothFamilyPointMap_snd, Category.comp_id,
      witnessSpaceMap, pullback.lift_snd]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, witnessSymmetry_fst]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, witnessPoint_snd]
        exact (pullbackSymmetry_hom_comp_fst _ _).symm
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, witnessPoint_fst,
          Category.assoc, hc, Category.comp_id]
        exact (pullbackSymmetry_hom_comp_snd _ _).symm
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, witnessPoint_fst,
        Category.assoc, hc, Category.comp_id, witnessSymmetry_snd]

lemma witnessSymmetry_comp :
    witnessSymmetry A T ≫ pullback.fst _ (𝟙 T.left) ≫
        (relativeSpaceSymmetry A.X.hom T).inv = 𝟙 _ := by
  rw [← Category.assoc, witnessSymmetry_fst]
  exact Iso.hom_inv_id _

end Transport

section Witness

variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (C : Over T.left)
  (N : LineBundle ((relativeSpace (witnessScheme A T).X.hom).obj C))
  (M : LineBundle C.left)
  (ev : Langlands.Scheme.Modules.tensorObj
      ((Scheme.Modules.pullback ((relativeSection A.X.hom (unitSection A)
        (unitSection_comp A)).app ((Over.map T.hom).obj C))).obj
          ((LineBundle.pullback (witnessSpaceMap A T C)).obj N).obj) M.obj ≅
    Langlands.Scheme.Modules.structureSheaf C.left)

/-- The witness bundle `N`, transported to `C ×_S A` and normalized along the unit section. -/
def witnessFamily : RigidifiedFamily A ((Over.map T.hom).obj C) :=
  LineBundle.normalize Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
    ((relativeProjection A.X.hom).app ((Over.map T.hom).obj C))
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app ((Over.map T.hom).obj C))
    (relativeSection_projection _ _ _ _) ((LineBundle.pullback (witnessSpaceMap A T C)).obj N) M ev

/-- At a rational point of `C` over which the normalizing factor is trivial, the witness family
restricts to the transported fibre of `N`. -/
def witnessRestrictionIso (c : Over.mk (𝟙 T.left) ⟶ C)
    (hM : (LineBundle.pullback c.left).obj M ≅ LineBundle.trivial T.left) :
    (RigidifiedLineBundle.forget _).obj
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          (witnessPoint T C c)).obj (witnessFamily A T C N M ev)) ≅
      (LineBundle.pullback (witnessSymmetry A T)).obj
        ((LineBundle.pullback (smoothFamilyPointMap (witnessScheme A T) C c)).obj N) :=
  LineBundle.pullbackTensorObjIso Langlands.Scheme.Modules.pullbackTensorComparisonIsIso _ _ _ ≪≫
    LineBundle.tensorIsoTrivialIso Langlands.Scheme.Modules.pullbackTensorComparisonIsIso _
      (LineBundle.pullbackCompEqIso _ _ (witnessPoint_projection A T C c) M ≪≫
        ((LineBundle.pullbackComp _ _).app M).symm ≪≫
        (LineBundle.pullback _).mapIso hM ≪≫ LineBundle.pullbackTrivialIso _) ≪≫
    LineBundle.pullbackCompEqIso _ _ (witnessPoint_spaceMap A T C c) N ≪≫
    ((LineBundle.pullbackComp _ _).app N).symm

/-- The first endpoint of a witness gives the trivial family. -/
lemma witnessFamily_trivial (c : Over.mk (𝟙 T.left) ⟶ C)
    (hM : (LineBundle.pullback c.left).obj M ≅ LineBundle.trivial T.left)
    (h : (LineBundle.pullback (smoothFamilyPointMap (witnessScheme A T) C c)).obj N ≅
      LineBundle.trivial _) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          (witnessPoint T C c)).obj (witnessFamily A T C N M ev) ≅
      RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A) T) :=
  RigidifiedLineBundle.nonempty_iso_of_forget_iso
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
    ((relativeProjection A.X.hom).app T) (relativeSection_projection _ _ _ _)
    (witnessRestrictionIso A T C N M ev c hM ≪≫ (LineBundle.pullback _).mapIso h ≪≫
      LineBundle.pullbackTrivialIso _)

/-- The second endpoint of a witness for the family `Lt` gives `Lt`. -/
lemma witnessFamily_endpoint (Lt : RigidifiedFamily A T) (c : Over.mk (𝟙 T.left) ⟶ C)
    (hM : (LineBundle.pullback c.left).obj M ≅ LineBundle.trivial T.left)
    (h : (LineBundle.pullback (smoothFamilyPointMap (witnessScheme A T) C c)).obj N ≅
      fibreLineBundle ((baseChange T.hom).obj A) (familyLineBundle A Lt) (𝟙 T.left)) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          (witnessPoint T C c)).obj (witnessFamily A T C N M ev) ≅ Lt) :=
  RigidifiedLineBundle.nonempty_iso_of_forget_iso
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
    ((relativeProjection A.X.hom).app T) (relativeSection_projection _ _ _ _)
    (witnessRestrictionIso A T C N M ev c hM ≪≫ (LineBundle.pullback _).mapIso h ≪≫
      (LineBundle.pullbackComp _ _).app _ ≪≫
      LineBundle.pullbackCompEqIso _ _ (by rw [Category.assoc]; exact witnessSymmetry_comp A T)
        _ ≪≫
      (LineBundle.pullbackId _).app _)

end Witness

section Main

variable {k : Type u} [Field k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  {P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (L : RigidifiedFamily A P)
  (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)

/-- The Picard-zero direction, from the rigidified-family smooth-family comparison. -/
theorem mem_originComponent_of_isPicardZeroFamily
    (comparison : SmoothFamilyPicardZeroComparisonStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ P.left)
    (hs : IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom
        (unitSection A) (unitSection_comp A)
        (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L)) :
    Set.range s ⊆ connectedComponent (fullPicardOriginPoint k A L hL) := by
  let T : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) := Over.mk (s ≫ P.hom)
  let σ : T ⟶ P := Over.homMk s rfl
  obtain ⟨C, -, -, -, -, hInt, c0, c1, N, ⟨h0⟩, ⟨h1⟩⟩ :=
    (comparison.2.2.1 _ A T _).2 hs K (𝟙 T.left)
  obtain ⟨M, ⟨ev⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback ((relativeSection A.X.hom (unitSection A)
      (unitSection_comp A)).app ((Over.map T.hom).obj C))).obj
        ((LineBundle.pullback (witnessSpaceMap A T C)).obj N))
  have hM (c : Over.mk (𝟙 T.left) ⟶ C) :
      (LineBundle.pullback c.left).obj M ≅ LineBundle.trivial T.left :=
    ObjectProperty.isoMk _ (fieldLineBundleTriviality K ((LineBundle.pullback c.left).obj M)).some
  let tp := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) L hL
  let g := RigidifiedLineBundle.classifyFamily A.X.hom (unitSection A) (unitSection_comp A) L hL
    (witnessFamily A T C N M ev)
  have hg0 : witnessPoint T C c0 ≫ g = Over.mkIdTerminal.from T ≫ tp := by
    obtain ⟨e⟩ := witnessFamily_trivial A T C N M ev c0 (hM c0) h0
    rw [← RigidifiedLineBundle.classifyFamily_pullback,
      RigidifiedLineBundle.classifyFamily_eq_of_iso _ _ _ _ _ e,
      RigidifiedLineBundle.classifyFamily_trivial]
  have hg1 : witnessPoint T C c1 ≫ g = σ := by
    obtain ⟨e⟩ := witnessFamily_endpoint A T C N M ev _ c1 (hM c1) h1
    rw [← RigidifiedLineBundle.classifyFamily_pullback,
      RigidifiedLineBundle.classifyFamily_eq_of_iso _ _ _ _ _ e,
      RigidifiedLineBundle.classifyFamily_pullback, RigidifiedLineBundle.classifyFamily_self,
      Category.comp_id]
  have : IrreducibleSpace C.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton C.hom
  have hconn : _root_.IsPreconnected (Set.range g.left) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ C.left).2.isPreconnected.image _
      g.left.continuous.continuousOn
  have horigin : fullPicardOriginPoint k A L hL ∈ Set.range g.left := by
    let y : T.left := IsLocalRing.closedPoint K
    refine ⟨(witnessPoint T C c0).left y, ?_⟩
    have := congrArg (fun h ↦ h.left y) hg0
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at this
    exact this.trans (trivialParameter_apply L hL _)
  rintro _ ⟨x, rfl⟩
  refine hconn.subset_connectedComponent horigin ⟨(witnessPoint T C c1).left x, ?_⟩
  have := congrArg (fun h ↦ h.left x) hg1
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at this
  exact this

end Main

/-- The origin-component comparison, given the smooth-family Picard-zero comparison. -/
theorem fieldPicardZeroGeometricComponentComparison_of
    (comparison : SmoothFamilyPicardZeroComparisonStatement.{u}) :
    FieldPicardZeroGeometricComponentComparisonStatement.{u} := by
  intro k _ A P L hP hL K _ _ s
  exact ⟨mem_originComponent_of_isPicardZeroFamily L hL comparison K s,
    isPicardZeroFamily_of_mem_originComponent L hL hP K s⟩

end Langlands.AbelianScheme
