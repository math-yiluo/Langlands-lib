import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant
import Langlands.AlgebraicGeometry.Modules.FixedRankLocalBases

/-! # Finite products of line bundles are locally free of finite rank -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}}

/-- A trivialization of a line bundle on an open restricts to every smaller open. -/
def restrictUnitIsoOfLE (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE h)

/-- A finite product of copies of the structure sheaf is free. -/
def piUnitFreeIso (Y : Scheme.{u}) (J : Type) [Fintype J] :
    (∏ᶜ fun _ : J => SheafOfModules.unit Y.ringCatSheaf : SheafOfModules.{u} Y.ringCatSheaf) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (Fintype.card J))) :=
  haveI : HasFiniteBiproducts (SheafOfModules.{u} Y.ringCatSheaf) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.whiskerEquiv (f := fun _ : J => SheafOfModules.unit Y.ringCatSheaf)
      (g := fun _ : ULift.{u} (Fin (Fintype.card J)) => SheafOfModules.unit Y.ringCatSheaf)
      ((Fintype.equivFin J).trans Equiv.ulift.symm) (fun _ => Iso.refl _)

/-- On an open trivializing every factor, a finite product of line bundles is
free with one generator for each factor. -/
def piRestrictFreeIso {J : Type} [Fintype J] (L : J → LineBundle X) (U : X.Opens)
    (e : ∀ j, (L j).obj.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (∏ᶜ fun j => (L j).obj).restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf)
        (ULift.{u} (Fin (Fintype.card J))) :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    PreservesProduct.iso (Scheme.Modules.pullback U.ι) _ ≪≫
    Pi.mapIso (fun j => ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫ e j) ≪≫
    piUnitFreeIso U.toScheme J

/-- A finite product of line bundles is locally free of rank the number of factors. -/
theorem isLocallyFreeOfRank_pi {J : Type} [Fintype J] (L : J → LineBundle X) :
    Langlands.Scheme.Modules.IsLocallyFreeOfRank (∏ᶜ fun j => (L j).obj)
      (Fintype.card J) := by
  classical
  apply Langlands.Scheme.Modules.isLocallyFreeOfRank_of_freeNeighborhoods
  intro x
  choose V hxV eV using fun j => (L j).property x
  let U : X.Opens := Finset.univ.inf V
  have hxU : x ∈ U := by
    change x ∈ ((Finset.univ.inf V : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter,
      Set.mem_iInter, Function.comp_apply]
    exact fun j => hxV j
  have hUV : ∀ j, U ≤ V j := fun j => Finset.inf_le (Finset.mem_univ j)
  exact ⟨U, hxU, ⟨piRestrictFreeIso L U fun j =>
    restrictUnitIsoOfLE (L j).obj (hUV j) (eV j).some⟩⟩

/-- Fixed finite rank gives a covering family of finite local bases. -/
theorem hasFiniteLocalBasis_of_isLocallyFreeOfRank {M : X.Modules} {n : ℕ}
    (h : Langlands.Scheme.Modules.IsLocallyFreeOfRank M n) :
    Langlands.Scheme.Modules.HasFiniteLocalBasis M := by
  obtain ⟨q, hq, hn⟩ := h
  refine ⟨q, hq, ?_⟩
  constructor
  intro i
  exact { finite := Finite.of_equiv (Fin n) (hn i).some.symm }

end Langlands.AlgebraicGeometry.Picard
