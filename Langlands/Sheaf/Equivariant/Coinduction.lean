import Langlands.Sheaf.Equivariant.Induction
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Coinduction of sheaves to equivariant sheaves

The inclusion of ordinary opens into the transport category lifts covers, so
right Kan extension along it sends sheaves to transport sheaves. The resulting
coinduction functor is right adjoint to forgetting equivariance.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u uA vA

variable (G : Type u) [Group G] (X : Type u) [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- A transport sieve on an ordinary open covers exactly when its label-one
inclusions cover, so the inclusion of ordinary opens lifts covers. -/
instance inclusion_isCocontinuous :
    (ActionOpens.inclusion G X).IsCocontinuous (Opens.grothendieckTopology X)
      (transportTopology G X) where
  cover_lift hS := hS

variable (A : Type uA) [Category.{vA} A] [HasLimitsOfSize.{u, u} A]

/-- Coinduction to transport sheaves: right Kan extension along the inclusion
of ordinary opens. -/
def transportCoinduction :
    Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf (transportTopology G X) A :=
  (ActionOpens.inclusion G X).sheafPushforwardCocontinuous A
    (Opens.grothendieckTopology X) (transportTopology G X)

/-- Coinduction from ordinary sheaves to equivariant sheaves. -/
def coinduction : TopCat.Sheaf A (TopCat.of X) ⥤ TopologicalSheaf G X A :=
  transportCoinduction G X A ⋙ (sheafEquivalence G X A).inverse

/-- Restricting a transport sheaf to ordinary opens is forgetting equivariance,
for any coefficient category. -/
def toSheafIsoPushforward :
    (sheafEquivalence G X A).functor ⋙
        (ActionOpens.inclusion G X).sheafPushforwardContinuous A
          (Opens.grothendieckTopology X) (transportTopology G X) ≅
      toSheaf G X A :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Coinduction is right adjoint to forgetting equivariance. -/
def coinductionAdjunction : toSheaf G X A ⊣ coinduction G X A :=
  ((sheafEquivalence G X A).toAdjunction.comp
    ((ActionOpens.inclusion G X).sheafAdjunctionCocontinuous A
      (Opens.grothendieckTopology X) (transportTopology G X))).ofNatIsoLeft
    (toSheafIsoPushforward G X A)

instance : (toSheaf G X A).IsLeftAdjoint :=
  (coinductionAdjunction G X A).isLeftAdjoint

instance : (coinduction G X A).IsRightAdjoint :=
  (coinductionAdjunction G X A).isRightAdjoint

variable (R : Type u) [CommRing R]

/-- Coinduction sends injective sheaves to injective equivariant sheaves,
since forgetting equivariance preserves monomorphisms. -/
instance coinduction_preservesInjectiveObjects :
    (coinduction G X (ModuleCat.{u} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (coinductionAdjunction G X (ModuleCat.{u} R))

end Langlands.Sheaf.Equivariant
