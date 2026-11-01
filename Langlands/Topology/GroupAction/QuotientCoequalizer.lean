import Langlands.CategoryTheory.TopCatSelfForget
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.Topology.ContinuousMap.Basic

/-! # Explicit fiber-relation coequalizers of continuous actions -/

noncomputable section

universe u v

namespace Langlands.ContinuousQuotient

open CategoryTheory CategoryTheory.Limits Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {M : Type v} [Monoid M] [TopologicalSpace M]
  {X Y : ContAction TopCat.{u} M} (q : X ⟶ Y)

private theorem equivariant_apply {A B : ContAction TopCat.{u} M}
    (f : A ⟶ B) (g : M) (x : A.obj.V) :
    f.hom.hom (ConcreteCategory.hom (A.obj.ρ g) x) =
      ConcreteCategory.hom (B.obj.ρ g) (f.hom.hom x) :=
  congrArg (fun k : A.obj.V ⟶ B.obj.V => k x) (f.hom.comm g)

/-- The actual equal-fiber subspace of the square of the source. -/
def Relation :=
  {p : X.obj.V × X.obj.V // q.hom.hom p.1 = q.hom.hom p.2}

instance : TopologicalSpace (Relation q) :=
  inferInstanceAs (TopologicalSpace {p : X.obj.V × X.obj.V //
    q.hom.hom p.1 = q.hom.hom p.2})

/-- Apply the original action to both coordinates of a fiber pair. -/
def relationMap (g : M) : C(Relation q, Relation q) where
  toFun p :=
    ⟨(ConcreteCategory.hom (X.obj.ρ g) p.val.1,
      ConcreteCategory.hom (X.obj.ρ g) p.val.2),
      (equivariant_apply q g p.val.1).trans
        ((congrArg (ConcreteCategory.hom (Y.obj.ρ g)) p.property).trans
          (equivariant_apply q g p.val.2).symm)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((X.obj.ρ g).hom.continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
      ((X.obj.ρ g).hom.continuous.comp
        (continuous_snd.comp continuous_subtype_val))

/-- The diagonal action uses the original product and subspace topologies. -/
def relationAction : Action TopCat.{u} M where
  V := TopCat.of (Relation q)
  ρ :=
    { toFun := fun g => TopCat.ofHom (relationMap q g)
      map_one' := by
        apply TopCat.ext
        intro p
        apply Subtype.ext
        change (ConcreteCategory.hom (X.obj.ρ 1) p.val.1,
          ConcreteCategory.hom (X.obj.ρ 1) p.val.2) = p.val
        rw [map_one]
        rfl
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro p
        apply Subtype.ext
        change (ConcreteCategory.hom (X.obj.ρ (g * h)) p.val.1,
          ConcreteCategory.hom (X.obj.ρ (g * h)) p.val.2) =
            (ConcreteCategory.hom (X.obj.ρ g)
                (ConcreteCategory.hom (X.obj.ρ h) p.val.1),
              ConcreteCategory.hom (X.obj.ρ g)
                (ConcreteCategory.hom (X.obj.ρ h) p.val.2))
        rw [map_mul]
        rfl }

theorem relationAction_isContinuous : (relationAction q).IsContinuous := by
  apply (Action.isContinuous_def _).mpr
  have hc := (Action.isContinuous_def X.obj).mp X.property
  change Continuous (fun p : M × Relation q => relationMap q p.1 p.2)
  exact ((hc.comp (continuous_fst.prodMk
    (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))).prodMk
    (hc.comp (continuous_fst.prodMk
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))).subtype_mk _

/-- The jointly continuous diagonal action on the actual fiber relation. -/
def relation : ContAction TopCat.{u} M :=
  ⟨relationAction q, relationAction_isContinuous q⟩

/-- First projection from the actual relation subspace. -/
def fst : relation q ⟶ X :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩
      comm := fun _ => by
        apply TopCat.ext
        intro p
        rfl }

/-- Second projection from the actual relation subspace. -/
def snd : relation q ⟶ X :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩
      comm := fun _ => by
        apply TopCat.ext
        intro p
        rfl }

theorem condition : fst q ≫ q = snd q ≫ q := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro p
  exact p.property

/-- The unique continuous equivariant map into the actual fiber relation. -/
def pair {W : ContAction TopCat.{u} M} (f g : W ⟶ X)
    (h : f ≫ q = g ≫ q) : W ⟶ relation q :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        { toFun := fun w => ⟨(f.hom.hom w, g.hom.hom w),
            congrArg (fun k : W ⟶ Y => k.hom.hom w) h⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact f.hom.hom.hom.continuous.prodMk g.hom.hom.hom.continuous }
      comm := fun a => by
        apply TopCat.ext
        intro w
        apply Subtype.ext
        exact Prod.ext (equivariant_apply f a w) (equivariant_apply g a w) }

@[simp]
theorem pair_fst {W : ContAction TopCat.{u} M} (f g : W ⟶ X)
    (h : f ≫ q = g ≫ q) : pair q f g h ≫ fst q = f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro w
  rfl

@[simp]
theorem pair_snd {W : ContAction TopCat.{u} M} (f g : W ⟶ X)
    (h : f ≫ q = g ≫ q) : pair q f g h ≫ snd q = g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro w
  rfl

/-- The concrete relation and its projections form the kernel-pair cone. -/
def pullbackCone : PullbackCone q q :=
  PullbackCone.mk (fst q) (snd q) (condition q)

/-- The actual product subspace, rather than an assumed pullback object,
satisfies the categorical kernel-pair universal property. -/
def isLimit : IsLimit (pullbackCone q) :=
  PullbackCone.IsLimit.mk (condition q)
    (fun s => pair q s.fst s.snd s.condition)
    (fun s => pair_fst q s.fst s.snd s.condition)
    (fun s => pair_snd q s.fst s.snd s.condition)
    (fun s k h₁ h₂ => by
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply TopCat.ext
      intro w
      apply Subtype.ext
      exact Prod.ext
        (congrArg (fun a : s.pt ⟶ X => a.hom.hom w) h₁)
        (congrArg (fun a : s.pt ⟶ X => a.hom.hom w) h₂))

/-- The cofork retains the supplied quotient morphism exactly. -/
def cofork : Cofork (fst q) (snd q) :=
  Cofork.ofπ q (condition q)

variable {Z : ContAction TopCat.{u} M}

/-- Equalizing both actual projections means constancy on all quotient fibers. -/
theorem condition_iff_factorsThrough (f : X ⟶ Z) :
    fst q ≫ f = snd q ≫ f ↔
      Function.FactorsThrough f.hom.hom q.hom.hom := by
  constructor
  · intro h x y hxy
    exact congrArg (fun k : relation q ⟶ Z => k.hom.hom ⟨(x, y), hxy⟩) h
  · intro h
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro p
    exact h p.property

variable (hq : IsQuotientMap q.hom.hom)
  (f : X ⟶ Z) (hf : fst q ≫ f = snd q ≫ f)

/-- Continuous descent along the original quotient map. -/
def liftMap : C(Y.obj.V, Z.obj.V) :=
  hq.lift f.hom.hom.hom ((condition_iff_factorsThrough q f).mp hf)

@[simp]
theorem liftMap_apply (x : X.obj.V) :
    liftMap q hq f hf (q.hom.hom x) = f.hom.hom x :=
  DFunLike.congr_fun
    (hq.lift_comp f.hom.hom.hom ((condition_iff_factorsThrough q f).mp hf)) x

/-- Surjectivity and the original equivariance equations prove equivariance
of the quotient lift. -/
def desc : Y ⟶ Z :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom (liftMap q hq f hf)
      comm := fun g => by
        apply TopCat.ext
        intro y
        obtain ⟨x, rfl⟩ := hq.surjective y
        change liftMap q hq f hf
          (ConcreteCategory.hom (Y.obj.ρ g) (q.hom.hom x)) =
            ConcreteCategory.hom (Z.obj.ρ g)
              (liftMap q hq f hf (q.hom.hom x))
        rw [← equivariant_apply q, liftMap_apply, liftMap_apply]
        exact equivariant_apply f g x }

@[simp]
theorem fac : q ≫ desc q hq f hf = f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  exact liftMap_apply q hq f hf x

theorem desc_unique (k : Y ⟶ Z) (hk : q ≫ k = f) :
    k = desc q hq f hf := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro y
  obtain ⟨x, rfl⟩ := hq.surjective y
  exact (congrArg (fun a : X ⟶ Z => a.hom.hom x) hk).trans
    (liftMap_apply q hq f hf x).symm

/-- The original quotient is the coequalizer of its actual diagonal-action
fiber relation in the category of jointly continuous actions. -/
def isColimit : IsColimit (cofork q) :=
  Cofork.IsColimit.mk _ (fun s => desc q hq s.π s.condition)
    (fun s => fac q hq s.π s.condition)
    (fun s k hk => desc_unique q hq s.π s.condition k hk)

end Langlands.ContinuousQuotient
