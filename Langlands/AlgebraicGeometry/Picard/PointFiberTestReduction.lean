import Langlands.AlgebraicGeometry.OverMorphismPropertyTransport
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberTestChange
import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Langlands.AlgebraicGeometry.Picard.PointFiberGeometry

/-! # Point-fibre properties from finite-type affine tests -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory

section Yoneda

variable {C D : Type*} [Category C] [Category D]

/-- The lifted Yoneda presheaf of a right adjoint value is the lifted Yoneda
presheaf restricted along the left adjoint. -/
def uliftYonedaAdjunctionIso {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (P : D) :
    uliftYoneda.{u}.obj (G.obj P) ≅ F.op ⋙ uliftYoneda.{u}.obj P :=
  NatIso.ofComponents
    (fun Z ↦ (Equiv.ulift.trans ((adj.homEquiv Z.unop P).symm.trans Equiv.ulift.symm)).toIso)
    (by
      intro Z Z' q
      apply ConcreteCategory.hom_ext
      intro x
      change ULift.up ((adj.homEquiv _ P).symm (q.unop ≫ x.down)) =
        ULift.up (F.map q.unop ≫ (adj.homEquiv _ P).symm x.down)
      rw [adj.homEquiv_naturality_left_symm])

end Yoneda

/-- The scheme Yoneda presheaf of a pullback is the original scheme Yoneda
presheaf restricted along `Over.map`. -/
def schemeYonedaPullbackIso {T T' : Scheme.{u}} (h : T' ⟶ T) (P : Over T) :
    (AlgebraicSpace.schemeYoneda T').obj ((Over.pullback h).obj P) ≅
      (Over.map h).op ⋙ (AlgebraicSpace.schemeYoneda T).obj P :=
  uliftYonedaAdjunctionIso (Over.mapPullbackAdj h) P

/-- Two schemes representing the same presheaf are isomorphic over the base. -/
lemma nonempty_iso_of_schemeYoneda {T : Scheme.{u}} {P P' : Over T}
    {G : AlgebraicSpace.Presheaf T} (e : (AlgebraicSpace.schemeYoneda T).obj P ≅ G)
    (e' : (AlgebraicSpace.schemeYoneda T).obj P' ≅ G) : Nonempty (P ≅ P') :=
  ⟨(ULiftYoneda.fullyFaithful.{u + 1} (Over T)).preimageIso (e ≪≫ e'.symm)⟩

/-- A property respecting isomorphisms transfers between isomorphic schemes over a base. -/
lemma prop_hom_of_iso (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso] {T : Scheme.{u}}
    {P P' : Over T} (i : P ≅ P') (hP : Q P.hom) : Q P'.hom :=
  Langlands.AlgebraicGeometry.prop_hom_of_overIso Q i.symm hP

/-- The slice of the iterated slice changes along a base map by `Over.map`. -/
def iteratedSliceMapIso {S : Scheme.{u}} {T T' : Over S} (g : T' ⟶ T) :
    T'.iteratedSliceBackward ⋙ Over.map g ≅ Over.map g.left ⋙ T.iteratedSliceBackward :=
  NatIso.ofComponents
    (fun Z ↦ Over.isoMk (Over.isoMk (Iso.refl _) (by simp [Over.w g])) (by ext; simp))
    (by intros; ext; simp)

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- The ordinary pullback of a test line bundle along a map of test schemes. -/
abbrev testPullback {T T' : Over S} (g : T' ⟶ T) (M : LineBundle ((relativeSpace f).obj T)) :
    LineBundle ((relativeSpace f).obj T') :=
  Core.of (C := LineBundle ((relativeSpace f).obj T'))
    (((relative f).map g.op.toLoc).toFunctor.obj (Core.mk M))

/-- Isomorphic test bundles have isomorphic actual point fibres. -/
def pointFiberPresheafIsoOfIso {T : Over S} {M M' : LineBundle ((relativeSpace f).obj T)}
    (e : (Core.mk M : (relative f).obj (.mk (op T))) ≅ Core.mk M') :
    pointFiberPresheaf f L M ≅ pointFiberPresheaf f L M' :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (PseudofunctorPointFiberTestChange.isoPresheafIso (relative f) (Core.mk L) e)) _

/-- Pulling back the test bundle restricts the actual point fibre along `Over.map`. -/
def pointFiberPresheafBaseChangeIso {T T' : Over S} (g : T' ⟶ T)
    (M : LineBundle ((relativeSpace f).obj T)) :
    pointFiberPresheaf f L (testPullback f g M) ≅
      (Over.map g.left).op ⋙ pointFiberPresheaf f L M :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft T'.iteratedSliceBackward.op
      (PseudofunctorPointFiberTestChange.basePresheafIso (relative f) (Core.mk L)
        (Core.mk M) g) ≪≫
    Functor.isoWhiskerRight (NatIso.op (iteratedSliceMapIso g)).symm
      (PseudofunctorPointFiber.presheaf (relative f) (Core.mk L) (Core.mk M))) _

/-- The pullback of a representing scheme represents the pulled-back test bundle. -/
def pullbackRepresentationIso {T T' : Over S} (g : T' ⟶ T)
    {M : LineBundle ((relativeSpace f).obj T)} {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf f L M) :
    (AlgebraicSpace.schemeYoneda T'.left).obj ((Over.pullback g.left).obj P) ≅
      pointFiberPresheaf f L (testPullback f g M) :=
  schemeYonedaPullbackIso g.left P ≪≫ Functor.isoWhiskerLeft (Over.map g.left).op e ≪≫
    (pointFiberPresheafBaseChangeIso f L g M).symm

variable (Q : MorphismProperty Scheme.{u})

/-- Every scheme representing the actual point fibre has property `Q` over the test. -/
def PointFiberProperty (T : Over S) (M : LineBundle ((relativeSpace f).obj T)) : Prop :=
  ∀ P : Over T.left,
    Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf f L M) →
      Q P.hom

variable {f L Q}

/-- One representing scheme with property `Q` gives property `Q` for all of them. -/
lemma PointFiberProperty.of_exists [Q.RespectsIso] {T : Over S}
    {M : LineBundle ((relativeSpace f).obj T)} {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf f L M)
    (hP : Q P.hom) : PointFiberProperty f L Q T M := by
  rintro P' ⟨e'⟩
  obtain ⟨i⟩ := nonempty_iso_of_schemeYoneda e e'
  exact prop_hom_of_iso Q i hP

/-- The point-fibre property is invariant under isomorphism of the test bundle. -/
lemma PointFiberProperty.of_iso {T : Over S} {M M' : LineBundle ((relativeSpace f).obj T)}
    (e : (Core.mk M : (relative f).obj (.mk (op T))) ≅ Core.mk M')
    (h : PointFiberProperty f L Q T M) : PointFiberProperty f L Q T M' := by
  rintro P ⟨e'⟩
  exact h P ⟨e' ≪≫ (pointFiberPresheafIsoOfIso f L e).symm⟩

/-- The point-fibre property is stable under pulling back the test bundle. -/
lemma PointFiberProperty.baseChange [Q.IsStableUnderBaseChange] {T T' : Over S}
    (g : T' ⟶ T) {M : LineBundle ((relativeSpace f).obj T)} {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf f L M)
    (h : PointFiberProperty f L Q T M) :
    PointFiberProperty f L Q T' (testPullback f g M) :=
  PointFiberProperty.of_exists (pullbackRepresentationIso f L g e)
    (Q.pullback_snd P.hom g.left (h P ⟨e⟩))

section FiniteType

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {U : Over (Spec (CommRingCat.of R))}
  {L : LineBundle ((relativeSpace f).obj U)} {Q : MorphismProperty Scheme.{u}}

/-- The finite-type affine hypothesis: every finite-type affine test bundle has a
representing scheme with property `Q`. -/
def FiniteTypeAffinePointFiberProperty (f : X ⟶ Spec (CommRingCat.of R))
    (L : LineBundle ((relativeSpace f).obj U)) (Q : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (M : LineBundle ((relativeSpace f).obj (affineBase R B))),
    ∃ P : Over (affineBase R B).left,
      Nonempty ((AlgebraicSpace.schemeYoneda (affineBase R B).left).obj P ≅
        pointFiberPresheaf f L M) ∧ Q P.hom

/-- Finite-type affine tests control every affine test. -/
theorem PointFiberProperty.affineBase [Q.IsStableUnderBaseChange]
    [QuasiCompact f] [QuasiSeparated f] (hQ : FiniteTypeAffinePointFiberProperty f L Q)
    (A : Type u) [CommRing A] [Algebra R A]
    (M : LineBundle ((relativeSpace f).obj (affineBase R A))) :
    PointFiberProperty f L Q (affineBase R A) M := by
  obtain ⟨B, hB, -, M₀, ⟨e⟩⟩ := exists_affineFamily_subalgebra f M ∅
  have : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp hB
  obtain ⟨P, ⟨eP⟩, hP⟩ := hQ B M₀
  exact PointFiberProperty.of_iso e
    (PointFiberProperty.baseChange (affineSubalgebraMap B) eP
      (PointFiberProperty.of_exists eP hP))

/-- The ring of a member of the chosen affine open cover of a test, as an algebra
over the base ring. -/
abbrev coverAlgebra (T : Over (Spec (CommRingCat.of R))) (i : T.left.affineOpenCover.I₀) :
    Algebra R (T.left.affineOpenCover.X i) :=
  (Spec.preimage (T.left.affineOpenCover.f i ≫ T.hom)).hom.toAlgebra

/-- The inclusion of a member of the chosen affine open cover as a map of tests. -/
def coverMap (T : Over (Spec (CommRingCat.of R))) (i : T.left.affineOpenCover.I₀) :
    letI := coverAlgebra T i
    affineBase R (T.left.affineOpenCover.X i) ⟶ T :=
  letI := coverAlgebra T i
  Over.homMk (T.left.affineOpenCover.f i) (by
    dsimp only [affineBase, Over.mk_hom]
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage])

/-- Finite-type affine tests control every test, for a property local on the target. -/
theorem PointFiberProperty.of_finiteTypeAffine [Q.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget Q] [QuasiCompact f] [QuasiSeparated f]
    (hQ : FiniteTypeAffinePointFiberProperty f L Q)
    (T : Over (Spec (CommRingCat.of R))) (M : LineBundle ((relativeSpace f).obj T)) :
    PointFiberProperty f L Q T M := by
  rintro P ⟨e⟩
  refine IsZariskiLocalAtTarget.of_openCover T.left.affineOpenCover.openCover
    (fun i ↦ ?_)
  let := coverAlgebra T i
  exact PointFiberProperty.affineBase hQ _ _ _
    ⟨pullbackRepresentationIso f L (coverMap T i) e⟩

end FiniteType

/-- Smooth surjective presentations of actual point fibres need only be checked
on finite-type affine tests. -/
theorem isSmoothSurjectivePresentation_of_finiteTypeAffine {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    {U : Over (Spec (CommRingCat.of R))} (L : LineBundle ((relativeSpace f).obj U))
    (h : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
      (M : LineBundle ((relativeSpace f).obj (affineBase R B))),
      PointFiberProperty f L @Smooth (affineBase R B) M ∧
        PointFiberProperty f L @Surjective (affineBase R B) M) :
    IsSmoothSurjectivePresentation f L := by
  have hrep := hasAffinePointFiberSchemes f
  have hS : FiniteTypeAffinePointFiberProperty f L @Smooth := by
    intro B _ _ _ M
    obtain ⟨I, ⟨e⟩, -, -⟩ := hrep U (affineBase R B) L M
    exact ⟨_, ⟨e⟩, (h B M).1 _ ⟨e⟩⟩
  have hU : FiniteTypeAffinePointFiberProperty f L @Surjective := by
    intro B _ _ _ M
    obtain ⟨I, ⟨e⟩, -, -⟩ := hrep U (affineBase R B) L M
    exact ⟨_, ⟨e⟩, (h B M).2 _ ⟨e⟩⟩
  intro T M
  obtain ⟨I, ⟨e⟩, -, -⟩ := hrep U T L M
  exact ⟨_, ⟨e⟩, PointFiberProperty.of_finiteTypeAffine hS T M _ ⟨e⟩,
    PointFiberProperty.of_finiteTypeAffine hU T M _ ⟨e⟩⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
