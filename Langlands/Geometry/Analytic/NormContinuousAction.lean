import Langlands.Geometry.Analytic.StrictTestDomain.ContinuousActionProof
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Norm-continuous actions on actual presented strict affinoid algebras -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (G : Type v) [Group G] [TopologicalSpace G]

/-- Continuity in the actual quotient norm of every forward algebra orbit. -/
def normContinuousAffinoidActionProperty :
    ObjectProperty (Action (PresentedStrictAffinoidAlgebra K) G) :=
  fun X => ∀ a : X.V, Continuous (fun g : G => (X.ρ g).toAlgHom a)

/-- All actions on actual presented quotients with continuous element orbits,
retaining every equivariant bounded algebra map. -/
abbrev NormContinuousAffinoidAction :=
  (normContinuousAffinoidActionProperty K G).FullSubcategory

/-- The geometric direction is opposite to that of the bounded algebra maps. -/
abbrev NormContinuousAffinoidSpace := (NormContinuousAffinoidAction K G)ᵒᵖ

namespace NormContinuousAffinoidAction

variable {K G}

/-- Bundle a specified bounded automorphism action with continuous element orbits. -/
def ofAut (P : PresentedStrictAffinoidAlgebra K) (ρ : G →* Aut P)
    (hρ : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) :
    NormContinuousAffinoidAction K G :=
  ⟨⟨P, (Aut.toEnd P).comp ρ⟩, hρ⟩

/-- The bounded inverses come from the group action, rather than an inverse theorem. -/
abbrev actionAut (X : NormContinuousAffinoidAction K G) : G →* Aut X.obj.V :=
  X.obj.ρAut

@[simp]
theorem actionAut_ofAut (P : PresentedStrictAffinoidAlgebra K) (ρ : G →* Aut P)
    (hρ : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) :
    (ofAut P ρ hρ).actionAut = ρ := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  rfl

theorem continuous_orbit (X : NormContinuousAffinoidAction K G) (a : X.obj.V) :
    Continuous (fun g : G => (X.actionAut g).hom.toAlgHom a) :=
  X.property a

/-- Every actual presentation carries the trivial continuous action. -/
def trivial (P : PresentedStrictAffinoidAlgebra K) :
    NormContinuousAffinoidAction K G :=
  ⟨Action.trivial G P, fun _ => continuous_const⟩

/-- The bounded algebra map retained by an equivariant morphism. -/
abbrev homMap {X Y : NormContinuousAffinoidAction K G} (f : X ⟶ Y) :
    BoundedAlgHom K X.obj.V Y.obj.V :=
  f.hom.hom

/-- Every bounded map satisfying the equivariance equations is an arrow. -/
def homMk {X Y : NormContinuousAffinoidAction K G}
    (f : BoundedAlgHom K X.obj.V Y.obj.V)
    (comm : ∀ g : G, X.obj.ρ g ≫ f = f ≫ Y.obj.ρ g) : X ⟶ Y :=
  ObjectProperty.homMk ⟨f, comm⟩

@[simp]
theorem homMap_homMk {X Y : NormContinuousAffinoidAction K G}
    (f : BoundedAlgHom K X.obj.V Y.obj.V)
    (comm : ∀ g : G, X.obj.ρ g ≫ f = f ≫ Y.obj.ρ g) :
    homMap (homMk f comm) = f :=
  rfl

theorem homMap_apply_action {X Y : NormContinuousAffinoidAction K G}
    (f : X ⟶ Y) (g : G) (a : X.obj.V) :
    homMap f ((X.actionAut g).hom.toAlgHom a) =
      (Y.actionAut g).hom.toAlgHom (homMap f a) :=
  congrArg (fun h : BoundedAlgHom K X.obj.V Y.obj.V => h a) (f.hom.comm g)

@[ext]
theorem hom_ext {X Y : NormContinuousAffinoidAction K G} {f h : X ⟶ Y}
    (heq : homMap f = homMap h) : f = h :=
  ObjectProperty.hom_ext _ (Action.Hom.ext heq)

/-- The full inclusion into Mathlib's action category. -/
def inclusion : NormContinuousAffinoidAction K G ⥤
    Action (PresentedStrictAffinoidAlgebra K) G :=
  (normContinuousAffinoidActionProperty K G).ι

instance : (inclusion (K := K) (G := G)).Full :=
  inferInstanceAs (normContinuousAffinoidActionProperty K G).ι.Full

instance : (inclusion (K := K) (G := G)).Faithful :=
  inferInstanceAs (normContinuousAffinoidActionProperty K G).ι.Faithful

/-- Forget the action, retaining the actual algebra and its bounded maps. -/
def forget : NormContinuousAffinoidAction K G ⥤ PresentedStrictAffinoidAlgebra K :=
  inclusion ⋙ Action.forget _ _

instance : (forget (K := K) (G := G)).Faithful :=
  inferInstanceAs (inclusion ⋙ Action.forget _ _).Faithful

section Restriction

variable {H : Type w} [Group H] [TopologicalSpace H]

/-- Restriction changes only the action parameter, preserving algebras and arrows. -/
def restrict (f : H →ₜ* G) :
    NormContinuousAffinoidAction K G ⥤ NormContinuousAffinoidAction K H :=
  (normContinuousAffinoidActionProperty K H).lift
    (inclusion ⋙ Action.res _ f.toMonoidHom)
    (fun X a => (X.property a).comp f.continuous)

@[simp]
theorem restrict_obj_algebra (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G) :
    ((restrict f).obj X).obj.V = X.obj.V :=
  rfl

@[simp]
theorem restrict_obj_apply (f : H →ₜ* G) (X : NormContinuousAffinoidAction K G)
    (h : H) (a : X.obj.V) :
    (((restrict f).obj X).obj.ρ h).toAlgHom a = (X.obj.ρ (f h)).toAlgHom a :=
  rfl

@[simp]
theorem homMap_restrict_map (f : H →ₜ* G)
    {X Y : NormContinuousAffinoidAction K G} (h : X ⟶ Y) :
    homMap ((restrict f).map h) = homMap h :=
  rfl

instance (f : H →ₜ* G) : (restrict (K := K) f).Faithful where
  map_injective {X} {Y} h k e := by
    apply hom_ext
    exact congrArg (fun q : (restrict f).obj X ⟶ (restrict f).obj Y => homMap q) e

end Restriction

section Spectrum

/-- The identity forgetful functor, used explicitly for Mathlib's continuous
actions on `TopCat` itself. It is not registered as a global instance. -/
@[instance_reducible]
def topCatSelfForget : HasForget₂ TopCat.{u} TopCat.{u} where
  forget₂ := 𝟭 _
  forget_comp := rfl

attribute [local instance] topCatSelfForget

/-- The actual inverse-pullback action on the bounded multiplicative spectrum. -/
def spectrumAction (X : NormContinuousAffinoidAction K G) : Action TopCat.{u} G where
  V := TopCat.of (BanachSpectrum X.obj.V)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        (BanachSpectrum.comapContinuous (X.actionAut g).inv.toBoundedRingHom)
      map_one' := by
        apply TopCat.ext
        intro x
        change (X.actionAut 1) • x = x
        simp
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        change (X.actionAut (g * h)) • x =
          (X.actionAut g) • ((X.actionAut h) • x)
        rw [map_mul, mul_smul] }

@[simp]
theorem spectrumAction_apply (X : NormContinuousAffinoidAction K G)
    (g : G) (x : BanachSpectrum X.obj.V) (a : X.obj.V) :
    BanachSpectrum.toMulRingSeminorm (ConcreteCategory.hom ((spectrumAction X).ρ g) x) a =
      x ((X.actionAut g).inv.toAlgHom a) :=
  rfl

variable [IsTopologicalGroup G]

/-- Joint continuity is derived from norm-continuous algebra orbits. -/
def spectrum (X : NormContinuousAffinoidAction K G) : ContAction TopCat.{u} G :=
  ⟨spectrumAction X, (Action.isContinuous_def _).mpr
    (StrictTestDomain.RationalAutomorphism.continuous_spectrumAction
      X.actionAut X.continuous_orbit)⟩

omit [IsTopologicalGroup G] in
/-- Pullback along every equivariant bounded map intertwines the point actions. -/
theorem spectrumMap_equivariant {X Y : NormContinuousAffinoidAction K G}
    (f : X ⟶ Y) (g : G) (x : BanachSpectrum Y.obj.V) :
    BanachSpectrum.comap (homMap f).toBoundedRingHom ((Y.actionAut g) • x) =
      (X.actionAut g) • BanachSpectrum.comap (homMap f).toBoundedRingHom x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun b : Y.obj.V => x b) (homMap_apply_action f (g⁻¹) a).symm

/-- In geometric direction, actual spectra and pullbacks form a functor to
Mathlib's category of continuous topological group actions. -/
def spectrumFunctor :
    NormContinuousAffinoidSpace K G ⥤ ContAction TopCat.{u} G where
  obj X := spectrum X.unop
  map f := ObjectProperty.homMk
    { hom := TopCat.ofHom (BanachSpectrum.comapContinuous (homMap f.unop).toBoundedRingHom)
      comm := fun g => by
        apply TopCat.ext
        intro x
        exact spectrumMap_equivariant f.unop g x }
  map_id _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    exact BanachSpectrum.ext fun _ => rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    exact BanachSpectrum.ext fun _ => rfl

@[simp]
theorem spectrumFunctor_map_apply {X Y : NormContinuousAffinoidSpace K G}
    (f : X ⟶ Y) (x : BanachSpectrum X.unop.obj.V) (a : Y.unop.obj.V) :
    BanachSpectrum.toMulRingSeminorm ((spectrumFunctor.map f).hom.hom x) a =
      x ((homMap f.unop).toAlgHom a) :=
  rfl

end Spectrum

end NormContinuousAffinoidAction

end Langlands.Analytic
