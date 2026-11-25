/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact

/-!
# Exactness of extension by zero on the small Zariski site

Source: Stacks Project, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-zariski-extension-by-zero-exact).

`U_Zar` is the localized site `(Opens.grothendieckTopology X).over U` (the opens `W ⊆ U`,
with the coverings of `X_Zar`), and extension by zero `j_! : Ab(U_Zar) ⥤ Ab(X_Zar)` is
`sheafToPresheaf ⋙ (Over.forget U).op.lan ⋙ presheafToSheaf`
(`Functor.sheafPullbackConstruction.sheafPullback`): the left Kan extension of `F` along
the inclusion is the presheaf `j_{p!} F` (`F(V)` for `V ⊆ U`, the empty colimit `0`
otherwise), followed by sheafification on `X_Zar`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Extension by zero `j_! : Ab(U_Zar) ⥤ Ab(X_Zar)`, the sheafification of `j_{p!}`, is
additive.

Source: Stacks Project, Modules on Sites, Lemma 03DJ, additivity clause
(blueprint: lem-weil-pbc-zariski-extension-by-zero-exact).

Proof: `j_!` is a left adjoint of restriction (Mathlib's
`sheafPullbackConstruction.sheafAdjunctionContinuous`); a left adjoint between
preadditive categories preserves finite biproducts, hence is additive. -/
@[instance]
theorem zariski_extensionByZero_additive (X : Scheme.{u}) (U : X.Opens) :
    (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U) AddCommGrpCat.{u}
        ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)).Additive := by
  have : ((Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u}
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)).Additive :=
    ⟨by intro A B f g; ext V; rfl⟩
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Over.forget U) AddCommGrpCat.{u} ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology X)).left_adjoint_additive

/-- Extension by zero `j_! : Ab(U_Zar) ⥤ Ab(X_Zar)` (additive by
`zariski_extensionByZero_additive`) carries every short exact sequence to a short exact
sequence, and in particular carries monomorphisms to monomorphisms.

Source: Stacks Project, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-zariski-extension-by-zero-exact).

Proof: `j_!` is a left adjoint of restriction, hence right exact, so it preserves
cokernels. A monomorphism of `Ab(U_Zar)` is sectionwise injective, so `j_{p!}` of it is
sectionwise injective, and sheafification preserves finite limits, so `j_!` of it is a
monomorphism. A short exact sequence is a mono followed by its cokernel; both are
preserved, which gives short exactness of the image. -/
theorem zariski_extensionByZero_exact (X : Scheme.{u}) (U : X.Opens) :
    (∀ S : ShortComplex (Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}),
      S.ShortExact →
        (S.map (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U)
          AddCommGrpCat.{u} ((Opens.grothendieckTopology X).over U)
          (Opens.grothendieckTopology X))).ShortExact) ∧
    (∀ {A B : Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}} (f : A ⟶ B),
      Mono f →
        Mono ((Functor.sheafPullbackConstruction.sheafPullback (Over.forget U)
          AddCommGrpCat.{u} ((Opens.grothendieckTopology X).over U)
          (Opens.grothendieckTopology X)).map f)) := by
  have htop : (Opens.grothendieckTopology X).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology X := by
    apply le_antisymm (GrothendieckTopology.toGrothendieck_toPrecoverage_le _)
    intro V S hS
    simpa only [Sieve.generate_sieve] using
      (Precoverage.generate_mem_toGrothendieck
        ((Opens.grothendieckTopology X).arrows_mem_toPrecoverage_iff S |>.mpr hS))
  have hshort := site_extensionByZero_exact
    (Opens.grothendieckTopology X).toPrecoverage U
  rw [htop] at hshort
  obtain ⟨hzero, hshort⟩ := hshort
  refine ⟨hshort, ?_⟩
  intro A B f hf
  have : Mono (ShortComplex.cokernelSequence f).f := hf
  exact (hshort (ShortComplex.cokernelSequence f)
    ⟨ShortComplex.cokernelSequence_exact f⟩).mono_f

end AlgebraicGeometry
