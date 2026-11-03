import Langlands.GroupScheme.Descent.ComponentCoverLifts
import Langlands.GroupScheme.SimplyConnected.BaseIsoTransport

/-! # Cover descent coherence on field components with isomorphic projections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]
variable {C H : GroupScheme (Spec (CommRingCat.of k))} {π : C ⟶ H}

namespace IsSimplyConnectedCover

/-- Lift a target comparison between two pullbacks along field-spectrum isomorphisms. -/
def pullbackIsoOfIsIso (hπ : IsSimplyConnectedCover π)
    (f g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso f] [IsIso g]
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    (baseChange f).obj C ≅ (baseChange g).obj C :=
  (hπ.baseChange_of_isIso f).isoOver (hπ.baseChange_of_isIso g) e

@[reassoc]
theorem pullbackIsoOfIsIso_hom_comp (hπ : IsSimplyConnectedCover π)
    (f g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso f] [IsIso g]
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    (hπ.pullbackIsoOfIsIso f g e).hom ≫ (baseChange g).map π =
      (baseChange f).map π ≫ e.hom :=
  (hπ.baseChange_of_isIso f).isoOver_hom_comp (hπ.baseChange_of_isIso g) e

/-- Uniqueness is proved at the specified field endpoints and target comparison. -/
theorem pullbackIsoLiftUnique_of_isIso (hπ : IsSimplyConnectedCover π)
    (f g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso f] [IsIso g]
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    Descent.PullbackIsoLiftUnique π e := by
  intro a b ha hb
  exact (hπ.baseChange_of_isIso f).hom_ext_over_iso
    (hπ.isSimplyConnected.isSemisimple.baseChange_of_isIso g)
    (hπ.isCentralIsogeny.baseChange g) e ha hb

end IsSimplyConnectedCover

namespace Descent

variable {B : Scheme.{u}} {p : Spec (CommRingCat.of k) ⟶ B}
variable {I J : Type} [Finite I] [Finite J]
variable {L : I → Type u} [∀ i, Field (L i)]
variable {M : J → Type u} [∀ j, Field (M j)]
variable (q : ∀ i, Spec (CommRingCat.of (L i)) ⟶ Overlap p)
variable (r : ∀ j, Spec (CommRingCat.of (M j)) ⟶ Triple p)
variable [IsIso (Limits.Sigma.desc q)] [IsIso (Limits.Sigma.desc r)]
variable [∀ i, IsIso (q i ≫ fst p)] [∀ i, IsIso (q i ≫ snd p)]
variable [∀ j, IsIso (r j ≫ p1 p)] [∀ j, IsIso (r j ≫ p3 p)]

/-- Lift an actual datum through a supplied cover using its field-component projections. -/
def Datum.liftOnFieldComponents (D : Datum p H) (hπ : IsSimplyConnectedCover π) :
    Datum p C :=
  D.liftFromComponentIsos q r
    (fun i => hπ.pullbackIsoOfIsIso (q i ≫ fst p) (q i ≫ snd p)
      (pullIso (q i) rfl rfl D.overlap))
    (fun i => hπ.pullbackIsoOfIsIso_hom_comp (q i ≫ fst p) (q i ≫ snd p)
      (pullIso (q i) rfl rfl D.overlap))
    (fun j => hπ.pullbackIsoLiftUnique_of_isIso (r j ≫ p1 p) (r j ≫ p3 p)
      (pullIso (r j) rfl rfl (iso13 D.overlap)))

/-- The constructed source datum makes the original covering map compatible. -/
theorem Datum.compatible_liftOnFieldComponents
    (D : Datum p H) (hπ : IsSimplyConnectedCover π) :
    Compatible (D.liftOnFieldComponents q r hπ) D π :=
  D.compatible_liftFromComponentIsos q r _ _ _

end Descent

end Langlands.GroupScheme
