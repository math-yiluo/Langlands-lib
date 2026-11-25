/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.Monoidal
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# A connected Galois cover trivializing finitely many lisse sheaves of `Λ`-modules

For a finite commutative ring `Λ` and finitely many finite locally constant sheaves of
`Λ`-modules on a connected scheme `U`, we construct a connected finite étale Galois cover
of `U` on which all of them become constant with finite values.

Source: Stacks Project, Tags 0DV5, 0DV6 and the proof of 0A3R.
(blueprint: lemma-tangent-cones-on-cover, lemma-reduction-unipotent-local-system)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- On a connected scheme, a retract of a constant sheaf of `Λ`-modules is constant: the
constant sheaf functor is fully faithful, so constancy is the invertibility of the counit,
and isomorphisms are stable under retracts. -/
theorem Scheme.isConstant_of_retract {X : Scheme.{u}} [ConnectedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h : Retract F G) [G.IsConstant X.smallEtaleTopology] :
    F.IsConstant X.smallEtaleTopology := by
  let hT : IsTerminal (Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  rw [Sheaf.isConstant_iff_isIso_counit_app _ _ hT]
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    (NatTrans.retractArrowApp _ h)
    (inferInstanceAs (IsIso ((constantSheafAdj _ _ hT).counit.app G)))

/-- A constant finite sheaf of modules over a finite ring on a nonempty scheme has a finite
value. -/
theorem Scheme.finite_of_iso_constantSheaf {X : Scheme.{u}} [Nonempty X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [IsFiniteSheaf F]
    {M : ModuleCat.{u + 1} Λ} (e : F ≅ (constantSheaf X.smallEtaleTopology _).obj M) :
    Finite M := by
  have : IsFiniteSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    IsFiniteSheaf.of_iso e
  have : Module.Finite Λ M := Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf (Y := X) M
  exact Module.finite_of_finite Λ

/-- A finite locally constant sheaf of modules over a finite ring is constant, with finite
value, on a connected finite étale Galois cover. Source: Stacks Project, Tags 0DV5, 0DV6
and the proof of 0A3R.
(blueprint: lemma-tangent-cones-on-cover, lemma-reduction-unipotent-local-system)

Proof: the underlying sheaf of sets is finite locally constant, hence trivialized by a
connected Galois cover; the module pullback is then constant, and its value is finite since
the pullback is a finite sheaf. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_galoisCover_isConstant_upperStar
    {U : Scheme.{u}} [ConnectedSpace U] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf G] :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q)
      (c : Scheme.GaloisCover (ULift.{u + 1} Q) U) (_ : ConnectedSpace c.P),
      ((c.π)^*[ModuleCat.{u + 1} Λ].obj G).IsConstant c.P.smallEtaleTopology := by
  obtain ⟨d, hd⟩ := (Scheme.finite_locally_constant_module_values_iff G).1.mpr
    (inferInstance : IsFiniteLocallyConstantSheaf G)
  have hsets := (Scheme.lisseModuleSheaf_iff_underlying_finiteLocallyConstant G).mp
    ⟨d.cover, hd⟩
  obtain ⟨Q, hQ, hfin, c, hconn, hconstant⟩ :=
    Scheme.exists_connected_torsor_constant_set_pullback
      ((sheafForget U.smallEtaleTopology).obj G) hsets
  exact ⟨Q, hQ, hfin, c, hconn,
    Scheme.module_pullback_isConstant_of_set_pullback Λ c.π G hconstant⟩

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Finitely many finite locally constant sheaves of modules over a finite ring on a
connected scheme are simultaneously constant, with finite values, on one connected finite
étale Galois cover. Source: Stacks Project, Tags 0DV5, 0DV6 and the proof of 0A3R.
(blueprint: lemma-tangent-cones-on-cover, lemma-reduction-unipotent-local-system)

Proof: apply `exists_galoisCover_isConstant_upperStar` to the finite direct sum; each
summand pulls back to a retract of a constant sheaf on a connected scheme, hence is
constant, and its value is finite. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_galoisCover_trivializing
    {U : Scheme.{u}} [ConnectedSpace U] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {ι : Type} [Finite ι] (F : ι → Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ i, IsFiniteLocallyConstantSheaf (F i)] :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q)
      (c : Scheme.GaloisCover (ULift.{u + 1} Q) U) (_ : ConnectedSpace c.P),
      ∀ i, ∃ (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
        Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj (F i) ≅
          (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  have := IsFiniteLocallyConstantSheaf.biproduct F
  obtain ⟨Q, hQ, hfin, c, hconn, hconst⟩ := exists_galoisCover_isConstant_upperStar (⨁ F)
  refine ⟨Q, hQ, hfin, c, hconn, fun i ↦ ?_⟩
  let h : Retract (F i) (⨁ F) := ⟨biproduct.ι F i, biproduct.π F i, by simp⟩
  have := Scheme.isConstant_of_retract (h.map (c.π)^*[ModuleCat.{u + 1} Λ])
  obtain ⟨M, ⟨e⟩⟩ := ((c.π)^*[ModuleCat.{u + 1} Λ].obj (F i)).mem_essImage_of_isConstant
  have : IsFiniteSheaf ((c.π)^*[ModuleCat.{u + 1} Λ].obj (F i)) :=
    IsFiniteSheaf.upperStar c.π (F i)
  exact ⟨M, Scheme.finite_of_iso_constantSheaf e.symm, ⟨e.symm⟩⟩

end AlgebraicGeometry
