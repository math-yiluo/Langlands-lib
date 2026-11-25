/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.SheafCoinductionAction
import WeilConjectures.AlgebraicGeometry.SheafCoinductionCounit

/-!
# The sheaf coinduction adjunction

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine.
(blueprint: lem-sc-sheaf-coinduction-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Restriction of scalars along the structure sheaf map has a right adjoint,
whose underlying module sheaf is internal Hom, with the multiplication action
and evaluation-at-one counit. This assertion does not require affineness.

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine;
Modules, lemma-adjoint-tensor-restrict.
(blueprint: lem-sc-sheaf-coinduction-adjunction).

Proof: On each open U, put on Hom(A|U,F|U) the A(U)-action
(a phi)_W(b) = phi_W(a|W * b). Multiplication is O-linear and restrictions
preserve multiplication, so this gives a presheaf of A-modules. Its underlying
abelian presheaf is the existing internal Hom sheaf, so it is a sheaf.
Postcomposition with a map F -> F' is A-linear and defines the functor H;
forgetting the action gives the natural identification i with internal Hom.
For an A-module G, an O-linear g : T(G) -> F gives the A-linear morphism
G -> H(F) whose value at m on U, evaluated at b on W, is
 g_W(b * m|W). Conversely evaluate an A-linear psi : G -> H(F) at one.
Naturality follows from compatibility with restriction and multiplication.
The two assignments are inverse: linearity gives psi(m)(b)=psi(b*m)(1),
and evaluating the first assignment at one gives g(m). They are natural
in both arguments, hence define T adjoint to H. The inverse assignment
at the identity of H(F) is evaluation at one, proving the counit formula.
The definition of the action proves the remaining compatibility formula. -/
theorem sheafHom_restrictScalars_adjunction
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∃ H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A,
      ∃ i : H ⋙ T ≅ K, ∃ adj : T ⊣ H,
        (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
          (W : Over U) (b : A.obj.obj (op W.left)),
          (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
            (((i.hom.app F).val.app (op U)).hom φ).app (op W)
              (A.obj.map W.hom.op a * b)) ∧
        (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (φ : (H.obj F).val.obj (op U)),
          ((adj.counit.app F).val.app (op U)).hom φ =
            ((((i.hom.app F).val.app (op U)).hom φ).app
              (op (Over.mk (𝟙 U)))) (1 : A.obj.obj (op U))) := by
  dsimp only
  obtain ⟨H, i, haction⟩ := sheafHom_restrictScalars_with_action f
  obtain ⟨e, he⟩ := sheafHom_restrictScalars_counit f H i haction
  refine ⟨H, i, Adjunction.mkOfHomEquiv e, haction, ?_⟩
  intro F U φ
  change (((e.homEquiv (H.obj F) F).symm (𝟙 (H.obj F))).val.app (op U)).hom φ = _
  simpa using he (H.obj F) F (𝟙 (H.obj F)) U φ

end AlgebraicGeometry
