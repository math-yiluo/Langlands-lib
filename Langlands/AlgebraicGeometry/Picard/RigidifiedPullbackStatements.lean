import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-! # Compatibility targets for canonical rigidified pullback -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule.RigidifiedModule

/-- The ordinary identity comparison preserves the canonical pulled-back rigidification. -/
def PullbackIdentityStatement : Prop :=
  ∀ (S X : Scheme.{u}) (ε : S ⟶ X)
    (comm : ε ≫ 𝟙 X = 𝟙 S ≫ ε) (M : RigidifiedModule ε),
    ((pullback (𝟙 X) (𝟙 S) comm).obj M).rigidification.hom ≫
      (Scheme.Modules.pullback ε).map ((Scheme.Modules.pullbackId X).hom.app M.carrier) =
        M.rigidification.hom

/-- The ordinary composition comparison preserves the canonical pulled-back rigidifications. -/
def PullbackCompositionStatement : Prop :=
  ∀ (S X S' X' S'' X'' : Scheme.{u})
    (ε : S ⟶ X) (ε' : S' ⟶ X') (ε'' : S'' ⟶ X'')
    (f : X' ⟶ X) (g : S' ⟶ S) (f' : X'' ⟶ X') (g' : S'' ⟶ S')
    (comm : ε' ≫ f = g ≫ ε) (comm' : ε'' ≫ f' = g' ≫ ε')
    (comm'' : ε'' ≫ (f' ≫ f) = (g' ≫ g) ≫ ε) (M : RigidifiedModule ε),
    ((pullback f' g' comm').obj ((pullback f g comm).obj M)).rigidification.hom ≫
      (Scheme.Modules.pullback ε'').map
        ((Scheme.Modules.pullbackComp f' f).hom.app M.carrier) =
      ((pullback (f' ≫ f) (g' ≫ g) comm'').obj M).rigidification.hom

/-- The two compatibility laws needed for rigidified pullback on isomorphism classes. -/
def PullbackCoherenceStatement : Prop :=
  PullbackIdentityStatement.{u} ∧ PullbackCompositionStatement.{u}

end Langlands.SchemeModule.RigidifiedModule
