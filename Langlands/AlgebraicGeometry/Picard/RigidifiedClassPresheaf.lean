import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackStatements
import Mathlib.CategoryTheory.Skeletal

/-! # The presheaf of rigidified line-bundle classes -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.SchemeModule.RigidifiedModule

variable (coherence : PullbackCoherenceStatement.{u})
variable {S X S' X' S'' X'' : Scheme.{u}}
variable {ε : S ⟶ X} {ε' : S' ⟶ X'} {ε'' : S'' ⟶ X''}

/-- The ordinary identity comparison, lifted using the stated compatibility law. -/
def pullbackId (ε : S ⟶ X) :
    pullback (𝟙 X) (𝟙 S) (by simp) ≅ 𝟭 (RigidifiedModule ε) :=
  NatIso.ofComponents
    (fun M ↦ isoMk ((Scheme.Modules.pullbackId X).app M.carrier)
      (coherence.1 S X ε _ M))
    (by intro M N h; apply Subtype.ext
        exact (Scheme.Modules.pullbackId X).hom.naturality h.val)

/-- The ordinary composition comparison, lifted using the stated compatibility law. -/
def pullbackComp (f : X' ⟶ X) (g : S' ⟶ S)
    (f' : X'' ⟶ X') (g' : S'' ⟶ S')
    (comm : ε' ≫ f = g ≫ ε) (comm' : ε'' ≫ f' = g' ≫ ε')
    (comm'' : ε'' ≫ (f' ≫ f) = (g' ≫ g) ≫ ε) :
    pullback f g comm ⋙ pullback f' g' comm' ≅
      pullback (f' ≫ f) (g' ≫ g) comm'' :=
  NatIso.ofComponents
    (fun M ↦ isoMk ((Scheme.Modules.pullbackComp f' f).app M.carrier)
      (coherence.2 S X S' X' S'' X'' ε ε' ε'' f g f' g' comm comm' comm'' M))
    (by intro M N h; apply Subtype.ext
        exact (Scheme.Modules.pullbackComp f' f).hom.naturality h.val)

end Langlands.SchemeModule.RigidifiedModule

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})
variable {S X S' X' S'' X'' : Scheme.{u}}
variable {ε : S ⟶ X} {ε' : S' ⟶ X'} {ε'' : S'' ⟶ X''}

/-- Identity pullback of rigidified line bundles is naturally isomorphic to the identity. -/
def pullbackId (ε : S ⟶ X) :
    pullback (𝟙 X) (𝟙 S) (by simp) ≅ 𝟭 (RigidifiedLineBundle ε) :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _ ((RigidifiedModule.pullbackId coherence ε).app L.obj))
    (by intro L M h; apply ObjectProperty.hom_ext
        exact (RigidifiedModule.pullbackId coherence ε).hom.naturality h.hom)

/-- Composition comparison for rigidified line-bundle pullback. -/
def pullbackComp (f : X' ⟶ X) (g : S' ⟶ S)
    (f' : X'' ⟶ X') (g' : S'' ⟶ S')
    (comm : ε' ≫ f = g ≫ ε) (comm' : ε'' ≫ f' = g' ≫ ε')
    (comm'' : ε'' ≫ (f' ≫ f) = (g' ≫ g) ≫ ε) :
    pullback f g comm ⋙ pullback f' g' comm' ≅
      pullback (f' ≫ f) (g' ≫ g) comm'' :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _
      ((RigidifiedModule.pullbackComp coherence f g f' g' comm comm' comm'').app L.obj))
    (by intro L M h; apply ObjectProperty.hom_ext
        exact (RigidifiedModule.pullbackComp coherence f g f' g' comm comm' comm'').hom.naturality h.hom)

/-- Equal maps give the same rigidified pullback, independently of square witnesses. -/
def pullbackCongr {f₁ f₂ : X' ⟶ X} {g₁ g₂ : S' ⟶ S}
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (comm₁ : ε' ≫ f₁ = g₁ ≫ ε) (comm₂ : ε' ≫ f₂ = g₂ ≫ ε) :
    pullback f₁ g₁ comm₁ ≅ pullback f₂ g₂ comm₂ := by
  subst f₂
  subst g₂
  exact Iso.refl _

variable (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

/-- Identity comparison in the relative fibre-product family. -/
def relativePullbackId (T : Over S) :
    relativePullback f ε section_eq (𝟙 T) ≅ 𝟭 (relative f ε section_eq T) :=
  pullbackCongr ((relativeSpace f).map_id T) rfl _ _ ≪≫
    pullbackId coherence _

/-- Composition comparison in the relative fibre-product family. -/
def relativePullbackComp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V) :
    relativePullback f ε section_eq k ⋙ relativePullback f ε section_eq h ≅
      relativePullback f ε section_eq (h ≫ k) :=
  pullbackComp coherence ((relativeSpace f).map k) k.left
    ((relativeSpace f).map h) h.left _ _
    (by rw [← Functor.map_comp]
        exact ((relativeSection f ε section_eq).naturality (h ≫ k)).symm) ≪≫
    pullbackCongr ((relativeSpace f).map_comp h k).symm rfl _ _

/-- Isomorphism classes of actual rigidified line bundles over the relative family. -/
abbrev Classes (T : Over S) :=
  Quotient (isIsomorphicSetoid (relative f ε section_eq T))

/-- Pullback of isomorphism classes is induced by the actual pullback functor. -/
def classesPullback {T U : Over S} (h : T ⟶ U) :
    Classes f ε section_eq U → Classes f ε section_eq T :=
  Quotient.map (relativePullback f ε section_eq h).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(relativePullback f ε section_eq h).mapIso e⟩)

/-- The set-valued presheaf of rigidified line-bundle classes, conditional on the explicit
compatibility proposition. Its object and map functions do not depend on that proof. -/
def classPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Classes f ε section_eq T.unop
  map h := TypeCat.ofHom (classesPullback f ε section_eq h.unop)
  map_id T := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    exact Quotient.sound ⟨(relativePullbackId coherence f ε section_eq T.unop).app L⟩
  map_comp h k := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    exact Quotient.sound
      ⟨((relativePullbackComp coherence f ε section_eq k.unop h.unop).app L).symm⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
