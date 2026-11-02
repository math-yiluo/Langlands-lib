import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionStatement
import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineChart
import Langlands.AlgebraicGeometry.ModuleDualLocalFree
import Langlands.AlgebraicGeometry.Modules.FixedRankLocalBases
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry

private def sectionBasis {X : _root_.AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (I : Type u) [Fintype I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : X.Opens) (h : V ≤ U) :
    Module.Basis I Γ(X, V) Γ(M, V) := by
  classical
  apply Module.Basis.ofEquivFun
  exact
    { toFun := fun x i => LocalHom.app (localBasisCoordinate e i) (homOfLE h) x
      invFun := fun a => ∑ i : I, a i •
        (show Γ(M, V) from (localBasisSection e i).val (op (Over.mk (homOfLE h))))
      left_inv := by
        intro x
        exact localBasis_expansion e (Over.mk (homOfLE h)) x
      right_inv := by
        intro a
        funext i
        change (LocalHom.app (localBasisCoordinate e i) (homOfLE h)).hom
          (∑ j : I, a j • (show Γ(M, V) from
            (localBasisSection e j).val (op (Over.mk (homOfLE h))))) = a i
        rw [map_sum]
        calc
          _ = ∑ j : I, a j * (if j = i then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [LinearMap.map_smul]
            change a j * _ = _
            exact congrArg (fun t : Γ(X, V) => a j * t)
              (localBasisCoordinate_basis e i j (Over.mk (homOfLE h)))
          _ = a i := by simp
      map_add' := by
        intro x y
        funext i
        exact map_add _ _ _
      map_smul' := by
        intro r x
        funext i
        exact (LocalHom.app (localBasisCoordinate e i) (homOfLE h)).hom.map_smul r x }

private lemma overlapDimension {X : _root_.AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U V : X.Opens) (n m : ℕ)
    (eU : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)))
    (eV : M.restrict V.ι ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin m)))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) : n = m := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hxU, hxV⟩⟩
  have h := mk_eq_mk_of_basis'
    (sectionBasis M U _ (freeOverIsoOfRestrict M U _ eU) (U ⊓ V) inf_le_left)
    (sectionBasis M V _ (freeOverIsoOfRestrict M V _ eV) (U ⊓ V) inf_le_right)
  simpa using h

private lemma standardSmooth_dimension_basis {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsStandardSmooth R A] :
    ∃ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R A ∧
      Nonempty (Module.Basis (ULift.{u} (Fin n)) A (KaehlerDifferential R A)) := by
  classical
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R A).out
  let := hσ
  let := hι
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = P.dimension := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card]
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl,
    ⟨P.basisKaehler.reindex ((Fintype.equivFinOfCardEq hc).trans Equiv.ulift.symm)⟩⟩

private lemma smooth_dimension_neighborhoods
    {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n ∧
      Nonempty ((Langlands.Scheme.relativeDifferentials f).restrict V.ι ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin n))) := by
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  let := (f.appLE U V e).hom.toAlgebra
  let : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hs
  obtain ⟨n, hn, ⟨b⟩⟩ :=
    standardSmooth_dimension_basis (R := Γ(Y, U)) (A := Γ(X, V))
  exact ⟨n, U, hU, V, hV, hx, e, hn,
    ⟨Langlands.Scheme.relativeDifferentialsAffineChartBasisIso f hU hV e _ b⟩⟩

/-- A smooth morphism with connected source has one standard-smooth chart dimension. -/
theorem smoothConnectedRelativeDimension :
    SmoothConnectedRelativeDimensionStatement.{u} := by
  classical
  intro X Y f hf hX
  let := hf
  let := hX
  choose n U hU V hV hx e hs hb using smooth_dimension_neighborhoods f
  have hlocal : IsLocallyConstant n := by
    apply (IsLocallyConstant.iff_exists_open n).mpr
    intro x
    refine ⟨V x, (V x).isOpen, hx x, ?_⟩
    intro y hy
    exact overlapDimension (Langlands.Scheme.relativeDifferentials f)
      (V y) (V x) (n y) (n x) (hb y).some (hb x).some y (hx y) hy
  let x₀ : X := Classical.arbitrary X
  refine ⟨n x₀, ⟨?_⟩⟩
  intro x
  exact ⟨U x, hU x, V x, hV x, hx x, e x,
    (hlocal.apply_eq_of_preconnectedSpace x x₀) ▸ hs x⟩

end Langlands.AlgebraicGeometry
