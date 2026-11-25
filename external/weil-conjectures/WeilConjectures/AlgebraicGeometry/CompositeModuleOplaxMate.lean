/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Topology.ProfiniteCondensedRing
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # Composite module pullback and its specified oplax mate

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL
(auxiliary; not a blueprint node).

The left side uses the actual composite strong monoidal structure on mapMod followed
by extension of scalars. The right side uses the direct-image structure uniquely
normalized on local pure tensors, and the unit of the specified composite adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

/-- The actual composite oplax maps have the specified module-adjunction transposes.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL
(auxiliary; not a blueprint node).

Proof:
1. Write R = R_Y, A = F R, S = R_X and E = Ext_alpha. Relative tensor projections
   are coequalizer maps, so equality can be checked after those projections and after
   forgetting module structure (prose-03-02,
   def-weil-pbc-category-colimit, sk-def-sfb-module-objects).
2. The specified scalar Hom bijection is precomposition with its scalar unit a,
   and the lifted Hom bijection is the ambient abelian one. Thus Phi(h) = v ; G(a ; h)
   and u = v ; G(a). The right-adjoint identification is the identity on underlying
   sheaves, since the coefficient map is the mate of alpha
   (def-sfb-modobj-extend-restrict-adjunction, def-sfb-modobj-transport-adjunction,
   prose-03-02, sk-def-sfb-coefficient-morphisms,
   prose-03-02).
3. The actual scalar tensor map b sends s tensor (m tensor n) to
   (s tensor m) tensor (1 tensor n). Consequently q_A ; a ; b = (a tensor a) ; q_S.
   The normalized structure in lem-sfb-internal-extension-monoidal has this equation;
   cancellation of q_A and injectivity of the scalar Hom bijection identify its map
   with the stipulated scalar insertion (sk-def-sfb-sheaf-tensor,
   def-sfb-modobj-extension, def-sfb-modobj-extend-restrict-adjunction).
4. The scalar unit map b_0 is multiplication after alpha on the second factor.
   The unit law gives a_A ; b_0 = alpha; the mapMod unit is the identity
   (def-sfb-modobj-extension, def-sfb-modobj-extend-restrict-adjunction,
   sk-def-sfb-coefficient-morphisms, sk-def-sfb-module-objects,
   def-sfb-modobj-transport).
5. The descended map t satisfies F(q_R) ; t = delta_F ; q_A, and the composite
   map is E(t) ; b. Naturality of a therefore gives
   F(q_R) ; a ; d = delta_F ; (a tensor a) ; q_S
   (prose-03-02, def-sfb-modobj-extend-restrict-adjunction).
6. The ambient mate identity is v ; G(delta_F) = (v tensor v) ; mu_G.
   Substitute Step 5 into the formula of Step 2 and use naturality of v and mu_G.
   This gives q_R ; Phi(d) = (u tensor u) ; mu_G ; G(q_S)
   (def-sfb-finite-upper-star-monoidal, lem-sfb-adjunction-oplax-mate).
7. By the actual balanced direct-image construction, q_R ; m = mu_G ; G(q_S).
   Naturality of q_R for the two module units and cancellation of q_R now give
   the tensor identity (prose-03-02, prose-03-02).
8. Steps 2 and 4 give Phi(d_0) = v_R ; G(alpha) = e. These two identities say
   exactly that d and d_0 are the inverse Hom images defining the oplax mate;
   bijectivity makes that identification unique (sk-def-sfb-coefficient-morphisms,
   lem-sfb-adjunction-oplax-mate).
-/
theorem composite_module_oplax_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ M N : internalModules Λ Y,
      (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv (M ⊗ N)
          ((CondensedRing.upperStar Λ f).obj M ⊗ (CondensedRing.upperStar Λ f).obj N)
          ((CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N) =
        ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M ⊗ₘ
          (CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app N) ≫
          (internalPushLax Λ f).μ
            ((CondensedRing.upperStar Λ f).obj M) ((CondensedRing.upperStar Λ f).obj N)) ∧
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv
        (𝟙_ (internalModules Λ Y)) (𝟙_ (internalModules Λ X))
        (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.η =
      (internalPushLax Λ f).ε) := by
  -- The normalized direct image recovers the actual composite oplax structure.
  rw [← internalPullOplax_eq_canonical Λ f]
  constructor
  · intro M N
    exact ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _).apply_symm_apply _
  · exact ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _).apply_symm_apply _

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
