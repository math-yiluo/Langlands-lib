import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralAction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The full category of represented-domain spectral actions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

attribute [local instance] DomainAutomorphism.domainSpectralTopology

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (G : Type v) [Group G] [TopologicalSpace G]

/-- Continuity of the actual automorphism action in the constructed
represented-domain spectral topology. -/
def domainSpectralActionProperty :
    ObjectProperty (Action (PresentedAffinoidAlgebra K) G) :=
  fun X => @Continuous G (Aut X.V) _ (DomainAutomorphism.domainSpectralTopology X.V)
    X.ρAut

/-- All represented-domain spectral actions on actual presented quotients,
retaining every equivariant bounded algebra map. -/
abbrev DomainSpectralActionCategory :=
  (domainSpectralActionProperty K G).FullSubcategory

/-- The geometric direction is opposite to that of bounded algebra maps. -/
abbrev DomainSpectralSpace := (DomainSpectralActionCategory K G)ᵒᵖ

namespace DomainSpectralActionCategory

variable {K G}

/-- Bundle any actual automorphism homomorphism satisfying spectral continuity. -/
def ofAut (P : PresentedAffinoidAlgebra K) (ρ : G →* Aut P)
    (hρ : @Continuous G (Aut P) _ (DomainAutomorphism.domainSpectralTopology P) ρ) :
    DomainSpectralActionCategory K G :=
  ⟨⟨P, (Aut.toEnd P).comp ρ⟩, hρ.congr fun _ => by
    apply Aut.ext
    rfl⟩

/-- The bounded inverses are supplied by the group action. -/
abbrev actionAut (X : DomainSpectralActionCategory K G) : G →* Aut X.obj.V :=
  X.obj.ρAut

@[simp]
theorem actionAut_ofAut (P : PresentedAffinoidAlgebra K) (ρ : G →* Aut P)
    (hρ : @Continuous G (Aut P) _ (DomainAutomorphism.domainSpectralTopology P) ρ) :
    (ofAut P ρ hρ).actionAut = ρ := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  rfl

/-- Expose the object's continuity property using its actual automorphisms. -/
theorem continuous_actionAut (X : DomainSpectralActionCategory K G) :
    @Continuous G (Aut X.obj.V) _
      (DomainAutomorphism.domainSpectralTopology X.obj.V) X.actionAut :=
  X.property

/-- Recover the fixed-algebra continuous spectral action. -/
def toDomainSpectralAction [IsTopologicalGroup G]
    (X : DomainSpectralActionCategory K G) :
    DomainAutomorphism.DomainSpectralAction G X.obj.V :=
  ⟨X.actionAut, X.continuous_actionAut⟩

/-- Include a fixed-algebra spectral action without changing its algebra maps. -/
def ofDomainSpectralAction [IsTopologicalGroup G] {P : PresentedAffinoidAlgebra K}
    (ρ : DomainAutomorphism.DomainSpectralAction G P) :
    DomainSpectralActionCategory K G :=
  ofAut P ρ.toMonoidHom ρ.continuous_toMonoidHom

@[simp]
theorem actionAut_ofDomainSpectralAction [IsTopologicalGroup G]
    {P : PresentedAffinoidAlgebra K}
    (ρ : DomainAutomorphism.DomainSpectralAction G P) :
    (ofDomainSpectralAction ρ).actionAut = ρ.toMonoidHom :=
  actionAut_ofAut _ _ _

/-- Every actual presented quotient admits the trivial continuous action. -/
def trivial (P : PresentedAffinoidAlgebra K) :
    DomainSpectralActionCategory K G :=
  ofAut P 1 continuous_const

/-- Extract the actual bounded algebra map from an equivariant arrow. -/
abbrev homMap {X Y : DomainSpectralActionCategory K G} (f : X ⟶ Y) :
    BoundedAlgHom K X.obj.V Y.obj.V :=
  f.hom.hom

/-- Every equivariant bounded algebra map is an arrow of the full subcategory. -/
def homMk {X Y : DomainSpectralActionCategory K G}
    (f : BoundedAlgHom K X.obj.V Y.obj.V)
    (comm : ∀ g : G, X.obj.ρ g ≫ f = f ≫ Y.obj.ρ g) : X ⟶ Y :=
  ObjectProperty.homMk ⟨f, comm⟩

@[simp]
theorem homMap_homMk {X Y : DomainSpectralActionCategory K G}
    (f : BoundedAlgHom K X.obj.V Y.obj.V)
    (comm : ∀ g : G, X.obj.ρ g ≫ f = f ≫ Y.obj.ρ g) :
    homMap (homMk f comm) = f :=
  rfl

theorem homMap_apply_action {X Y : DomainSpectralActionCategory K G}
    (f : X ⟶ Y) (g : G) (a : X.obj.V) :
    homMap f ((X.actionAut g).hom.toAlgHom a) =
      (Y.actionAut g).hom.toAlgHom (homMap f a) :=
  congrArg (fun h : BoundedAlgHom K X.obj.V Y.obj.V => h a) (f.hom.comm g)

@[ext]
theorem hom_ext {X Y : DomainSpectralActionCategory K G} {f h : X ⟶ Y}
    (heq : homMap f = homMap h) : f = h :=
  ObjectProperty.hom_ext _ (Action.Hom.ext heq)

/-- The full inclusion into actions on actual quotient algebras. -/
def inclusion : DomainSpectralActionCategory K G ⥤
    Action (PresentedAffinoidAlgebra K) G :=
  (domainSpectralActionProperty K G).ι

instance : (inclusion (K := K) (G := G)).Full :=
  inferInstanceAs (domainSpectralActionProperty K G).ι.Full

instance : (inclusion (K := K) (G := G)).Faithful :=
  inferInstanceAs (domainSpectralActionProperty K G).ι.Faithful

/-- Forget the action, retaining the actual quotient algebra and bounded maps. -/
def forget : DomainSpectralActionCategory K G ⥤ PresentedAffinoidAlgebra K :=
  inclusion ⋙ Action.forget _ _

instance : (forget (K := K) (G := G)).Faithful :=
  inferInstanceAs (inclusion ⋙ Action.forget _ _).Faithful

section Restriction

variable {H : Type w} [Group H] [TopologicalSpace H]

/-- Continuous group restriction retains the algebras and all bounded arrows. -/
def restrict (f : H →ₜ* G) :
    DomainSpectralActionCategory K G ⥤ DomainSpectralActionCategory K H :=
  (domainSpectralActionProperty K H).lift
    (inclusion ⋙ Action.res _ f.toMonoidHom)
    (fun X => ((X.continuous_actionAut).comp f.continuous).congr fun _ => by
      apply Aut.ext
      rfl)

@[simp]
theorem restrict_obj_algebra (f : H →ₜ* G) (X : DomainSpectralActionCategory K G) :
    ((restrict f).obj X).obj.V = X.obj.V :=
  rfl

@[simp]
theorem restrict_obj_apply (f : H →ₜ* G) (X : DomainSpectralActionCategory K G)
    (h : H) (a : X.obj.V) :
    (((restrict f).obj X).obj.ρ h).toAlgHom a = (X.obj.ρ (f h)).toAlgHom a :=
  rfl

@[simp]
theorem homMap_restrict_map (f : H →ₜ* G)
    {X Y : DomainSpectralActionCategory K G} (h : X ⟶ Y) :
    homMap ((restrict f).map h) = homMap h :=
  rfl

instance (f : H →ₜ* G) : (restrict (K := K) f).Faithful where
  map_injective {X} {Y} h k e := by
    apply hom_ext
    exact congrArg (fun q : (restrict f).obj X ⟶ (restrict f).obj Y => homMap q) e

end Restriction

end DomainSpectralActionCategory

end Langlands.Analytic.PresentedAffinoidAlgebra
