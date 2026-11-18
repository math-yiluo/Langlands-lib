import Langlands.GroupScheme.SchemeActionQuotientDescent
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientFinitenessProof

/-! # Geometry of represented free-action quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {A : GroupScheme S} {X Q : Over S}
  (b : SchemeAction A X)

/-- Invariance and unique all-test differences identify the pullback along
any family of representatives with the product by the acting group. -/
theorem isPullback_of_point_of_exact_orbits (q : X ⟶ Q)
    (hinvariant : ∀ (T : Over S) (d : T ⟶ A.X) (x : T ⟶ X),
      b.act d x ≫ q = x ≫ q)
    (horbit : ∀ (T : Over S) (x y : T ⟶ X), x ≫ q = y ≫ q →
      ∃! d : T ⟶ A.X, b.act d x = y)
    {U : Over S} (p : U ⟶ X) :
    IsPullback (b.act prod.fst (prod.snd ≫ p) : A.X ⨯ U ⟶ X)
      prod.snd q (p ≫ q) := by
  have hw : (b.act prod.fst (prod.snd ≫ p) : A.X ⨯ U ⟶ X) ≫ q =
      prod.snd ≫ (p ≫ q) := by
    rw [hinvariant, Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.isLimitAux' _ (fun s => ?_)⟩⟩
  let h := horbit _ (s.snd ≫ p) s.fst
    (by simpa only [Category.assoc] using s.condition.symm)
  let d := h.choose
  have hd := h.choose_spec.1
  have huniq := h.choose_spec.2
  refine ⟨prod.lift d s.snd, ?_, prod.lift_snd _ _, ?_⟩
  · change prod.lift d s.snd ≫ b.act prod.fst (prod.snd ≫ p) = s.fst
    rw [b.naturality, prod.lift_fst, prod.lift_snd_assoc, hd]
  · change ∀ {m : s.pt ⟶ A.X ⨯ U},
      m ≫ b.act prod.fst (prod.snd ≫ p) = s.fst →
      m ≫ prod.snd = s.snd → m = prod.lift d s.snd
    intro m hm₁ hm₂
    apply prod.hom_ext (X := A.X) (Y := U)
    · rw [prod.lift_fst]
      apply huniq
      calc
        b.act (m ≫ prod.fst) (s.snd ≫ p) =
            b.act (m ≫ prod.fst) (m ≫ (prod.snd ≫ p)) := by
          rw [← Category.assoc, hm₂]
        _ = m ≫ b.act prod.fst (prod.snd ≫ p) :=
          (b.naturality m prod.fst (prod.snd ≫ p)).symm
        _ = s.fst := hm₁
    · exact hm₂.trans (prod.lift_snd d s.snd).symm

end Langlands.GroupScheme.SchemeAction

namespace Langlands.GroupScheme.SchemeAction.QuotientRepresentation

open Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {A : GroupScheme S} {X : Over S}
  {b : SchemeAction A X} (R : b.QuotientRepresentation)

/-- The represented class morphism evaluates to the canonical quotient map. -/
theorem classMap_app {T : Over S} (p : T ⟶ X) :
    R.iso.hom.app (op T) ⟨p ≫ R.classMap⟩ =
      b.quotientMap.hom.app (op T) ⟨p⟩ :=
  congrArg (fun f => f.app (op T) ⟨p⟩) R.comm

/-- Equality of represented classes is equality in the canonical quotient. -/
theorem classMap_eq_iff {T : Over S} (p q : T ⟶ X) :
    p ≫ R.classMap = q ≫ R.classMap ↔
      b.quotientMap.hom.app (op T) ⟨p⟩ =
        b.quotientMap.hom.app (op T) ⟨q⟩ := by
  rw [← R.classMap_app p, ← R.classMap_app q]
  constructor
  · intro h
    rw [h]
  · intro h
    exact congrArg ULift.down ((R.iso.app (op T)).toEquiv.injective h)

/-- The represented class morphism is invariant on every relative test. -/
theorem invariant {T : Over S} (d : T ⟶ A.X) (p : T ⟶ X) :
    b.act d p ≫ R.classMap = p ≫ R.classMap :=
  (R.classMap_eq_iff _ _).2 (b.quotientMap_act d p)

/-- A free action has a unique actual difference point for equal classes. -/
theorem existsUnique_act
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    {T : Over S} (p q : T ⟶ X)
    (hpq : p ≫ R.classMap = q ≫ R.classMap) :
    ∃! d : T ⟶ A.X, b.act d p = q :=
  b.existsUnique_act_of_isFppfActionQuotient hfree
    b.quotientMap_isFppfActionQuotient p q ((R.classMap_eq_iff p q).1 hpq)

/-- Over any class admitting a representative, the class morphism is the
projection from the product with the acting group. -/
theorem isPullback_of_point
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    {U : Over S} (p : U ⟶ X) :
    IsPullback (b.act prod.fst (prod.snd ≫ p) : A.X ⨯ U ⟶ X)
      prod.snd R.classMap (p ≫ R.classMap) :=
  b.isPullback_of_point_of_exact_orbits R.classMap (fun _ => R.invariant)
    (fun _ => R.existsUnique_act hfree) p

/-- The represented quotient map is locally surjective in the fppf topology. -/
theorem classMap_isLocallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map R.classMap) := by
  apply (CategoryTheory.Presheaf.isLocallySurjective_comp_iff
    (fppfTopology S) ((schemeYoneda S).map R.classMap) R.iso.hom).1
  rw [R.comm]
  exact b.quotientMap_isLocallySurjective

/-- Local representatives make the actual class morphism surjective. -/
instance surjective : Surjective R.classMap.left := by
  let := R.classMap_isLocallySurjective
  let J := CategoryTheory.Presheaf.imageSieve ((schemeYoneda S).map R.classMap)
    (⟨𝟙 R.parameter⟩ : ((schemeYoneda S).obj R.parameter).obj (op R.parameter))
  have hJ : J ∈ fppfTopology S R.parameter :=
    CategoryTheory.Presheaf.imageSieve_mem (fppfTopology S)
      ((schemeYoneda S).map R.classMap)
      (⟨𝟙 R.parameter⟩ : ((schemeYoneda S).obj R.parameter).obj (op R.parameter))
  constructor
  intro y
  obtain ⟨U, f, ⟨⟨p⟩, hp⟩, u, hu⟩ :=
    ActionQuotientOrbitRelation.exists_mem_range_of_mem hJ y
  have hpf : p ≫ R.classMap = f := by
    change (ULift.up (p ≫ R.classMap) : ULift.{u+1} (U ⟶ R.parameter)) =
      ULift.up (f ≫ 𝟙 R.parameter) at hp
    simpa only [Category.comp_id] using congrArg ULift.down hp
  refine ⟨p.left u, ?_⟩
  rw [← hu]
  change (p ≫ R.classMap).left u = f.left u
  rw [hpf]

/-- Any scheme property local on the fppf target descends from the acting
group's structure map to the class morphism of a represented free action. -/
theorem classMap_property
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hA : P A.X.hom) :
    P R.classMap.left := by
  let := R.classMap_isLocallySurjective
  let J := CategoryTheory.Presheaf.imageSieve ((schemeYoneda S).map R.classMap)
    (⟨𝟙 R.parameter⟩ : ((schemeYoneda S).obj R.parameter).obj (op R.parameter))
  have hJ : J ∈ fppfTopology S R.parameter :=
    CategoryTheory.Presheaf.imageSieve_mem (fppfTopology S)
      ((schemeYoneda S).map R.classMap)
      (⟨𝟙 R.parameter⟩ : ((schemeYoneda S).obj R.parameter).obj (op R.parameter))
  apply Langlands.AlgebraicGeometry.FppfLocal.of_fppfTopology_sieve P
    R.classMap.left (Sieve.overEquiv _ J)
    ((GrothendieckTopology.mem_over_iff Scheme.fppfTopology J).1 hJ)
  intro U f hf
  obtain ⟨⟨p⟩, hp⟩ := (Sieve.overEquiv_iff J f).1 hf
  let U' : Over S := Over.mk (f ≫ R.parameter.hom)
  have hpf : p ≫ R.classMap = (Over.homMk f : U' ⟶ R.parameter) := by
    change (ULift.up (p ≫ R.classMap) : ULift.{u+1} (U' ⟶ R.parameter)) =
      ULift.up ((Over.homMk f : U' ⟶ R.parameter) ≫ 𝟙 R.parameter) at hp
    simpa only [Category.comp_id] using congrArg ULift.down hp
  have hpb := (R.isPullback_of_point hfree p).map (Over.forget S)
  rw [hpf] at hpb
  refine ⟨(A.X ⨯ U').left, (b.act prod.fst (prod.snd ≫ p)).left,
    (prod.snd : A.X ⨯ U' ⟶ U').left, hpb, ?_⟩
  exact P.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : A.X ⨯ U' ⟶ A.X) prod.snd) (prodIsProd A.X U')) hA

/-- Flatness of the acting group gives flatness of the class morphism. -/
theorem flat
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    [Flat A.X.hom] : Flat R.classMap.left := by
  have : IsZariskiLocalAtTarget @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  let :=
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @Flat
  exact R.classMap_property hfree (@Flat.{u}) inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- Quasi-compactness of the acting group gives quasi-compactness of the
class morphism, without requiring either whole parameter scheme to be
quasi-compact. -/
theorem quasiCompact
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    [QuasiCompact A.X.hom] : QuasiCompact R.classMap.left := by
  have : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    HasAffineProperty.instIsZariskiLocalAtTarget
      (Q := fun X _ _ _ => CompactSpace X)
  let := ActionQuotientFiniteness.quasiCompact_descendsAlong_fppf.{u}
  exact R.classMap_property hfree (@QuasiCompact.{u}) inferInstance

/-- Local finite presentation of the acting group is retained by the
represented free-action quotient morphism. -/
theorem locallyOfFinitePresentation
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    [LocallyOfFinitePresentation A.X.hom] :
    LocallyOfFinitePresentation R.classMap.left := by
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  let :=
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @LocallyOfFinitePresentation
  exact R.classMap_property hfree (@LocallyOfFinitePresentation.{u}) inferInstance

end Langlands.GroupScheme.SchemeAction.QuotientRepresentation

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)

/-- A represented canonical quotient for a faithful automorphic action is
an actual outer-isomorphism quotient with its required class geometry. -/
def outerOfQuotientRepresentation (ha : a.IsFaithful)
    (R : SchemeAction.QuotientRepresentation (I.modObj a))
    [Flat A.X.hom] [QuasiCompact A.X.hom] :
    OuterIsomorphismScheme I a where
  parameter := R.parameter
  classMap := R.classMap
  flat := R.flat (I.actionHom_injective_of_isFaithful a ha)
  surjective := inferInstance
  quasiCompact := R.quasiCompact (I.actionHom_injective_of_isFaithful a ha)
  invariant _T d p := R.invariant d p
  orbit _T p q hpq :=
    R.existsUnique_act (I.actionHom_injective_of_isFaithful a ha) p q hpq

end Langlands.GroupScheme.GroupIsomorphismScheme
