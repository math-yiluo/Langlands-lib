import Langlands.Shimura.Coefficients.CrossCover
import Langlands.Shimura.Coefficients.Etale

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {G H : Type u} [Group G] [Group H]
variable {Y : Action X.Etale G} {Z : Action X.Etale H}

/-- The actual associated small-etale coefficient map across compatible covers. -/
abbrev etaleCrossCoverMap (φ : H →* G) (a : Z ⟶ (Action.res X.Etale φ).obj Y)
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (etaleAssociatedFunctor X Y).obj M ⟶ (etaleAssociatedFunctor X Z).obj N :=
  constantCrossCoverMap (Scheme.smallEtaleTopology X) φ a c

@[simp] theorem etaleCrossCoverMap_id
    (Y : Action X.Etale G) (M : Action (ModuleCat.{u} R) G) :
    etaleCrossCoverMap X (MonoidHom.id G) (𝟙 Y) (𝟙 M) =
      𝟙 ((etaleAssociatedFunctor X Y).obj M) :=
  constantCrossCoverMap_id _ Y M

@[reassoc] theorem etaleCrossCoverMap_comp
    (φ : H →* G) (a : Z ⟶ (Action.res X.Etale φ).obj Y)
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N)
    {K : Type u} [Group K] {W : Action X.Etale K}
    {P : Action (ModuleCat.{u} R) K}
    (ψ : K →* H) (b : W ⟶ (Action.res X.Etale ψ).obj Z)
    (d : (Action.res (ModuleCat.{u} R) ψ).obj N ⟶ P) :
    etaleCrossCoverMap X φ a c ≫ etaleCrossCoverMap X ψ b d =
      etaleCrossCoverMap X (φ.comp ψ) (b ≫ (Action.res X.Etale ψ).map a)
        ((Action.res (ModuleCat.{u} R) ψ).map c ≫ d) :=
  constantCrossCoverMap_comp _ φ a c ψ b d

end Langlands.Shimura.Coefficients
