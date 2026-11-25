/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CechModuleSheafFunctor

/-! # The terms of the concrete module-sheaf Čech complex

Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, displayed complex and proof
paragraph 1. (blueprint: lem-pc-cech-module-sheaf-terms).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Over-site extension is scheme-theoretic extension from the open subscheme. -/
private noncomputable def cechIntersectionSheafIsoPushforward
    {X : Scheme.{u}} (F : X.Modules) (W : X.Opens) :
    cechIntersectionSheaf F W ≅ (Scheme.Modules.pushforward W.ι).obj
      (F.restrict W.ι) := by
  let adj := (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) W).comp
    (Scheme.Modules.overEquiv W).toAdjunction
  let adj' := adj.ofNatIsoLeft (Scheme.Modules.overFunctorEquiv W)
  let e := Adjunction.rightAdjointUniq adj' (Scheme.Modules.restrictAdjunction W.ι)
  exact (SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).mapIso
      ((Scheme.Modules.overEquiv W).unitIso.app (F.over W)) ≪≫
    e.app ((Scheme.Modules.overEquiv W).functor.obj (F.over W)) ≪≫
    (Scheme.Modules.pushforward W.ι).mapIso ((Scheme.Modules.overFunctorEquiv W).app F)

/-- Finite products of opens are their infima. -/
private noncomputable def cechOpensProductIsoInf
    {X : Scheme.{u}} {α : Type} [Finite α] (V : α → X.Opens) :
    (∏ᶜ V) ≅ ⨅ a, V a where
  hom := homOfLE (le_iInf fun a => leOfHom (Pi.π V a))
  inv := Pi.lift fun a => homOfLE (iInf_le V a)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Each concrete Čech term is the product of extensions from the corresponding
finite intersections. Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, displayed
complex and proof paragraph 1. (blueprint: lem-pc-cech-module-sheaf-terms)

Proof: for an open W, the equivalence between the over site X.Opens/W and the opens
of W.toScheme identifies F.over W with F.restrict W.ι. Under this equivalence, the
right adjoint to restriction is pushforward along W.ι. Uniqueness of right adjoints,
or directly the section isomorphisms F(W × V) ≅ F(W ∩ V), therefore identifies
cechIntersectionSheaf F W with W.ι_*(F.restrict W.ι). The identification is linear
for O_X(V), because both actions are restrictions of scalars along the same map.
For a finite tuple y, the categorical product of its opens is canonically isomorphic
to their infimum. Indeed both are greatest lower bounds, so the projection maps and
universal property give inverse inclusions. Apply cechModuleSheafFunctor to this
isomorphism, then apply the preceding over-site identification at the infimum.
The degree-p term of cechModuleSheafComplex is definitionally the product over all
y : Fin(p+1) -> ι of cechIntersectionSheaf at the categorical product. Taking the
product of these component isomorphisms gives the asserted isomorphism. Empty index
families give the empty product on each side, and p=0 is the same argument with a
singleton finite tuple. There is no covering, affine or finiteness assumption on ι. -/
theorem cechModuleSheafComplex_term_iso
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules) (p : ℕ) :
    Nonempty ((cechModuleSheafComplex U F).X p ≅ ∏ᶜ fun y : Fin (p + 1) → ι =>
      (Scheme.Modules.pushforward (⨅ l, U (y l)).ι).obj
        (F.restrict (⨅ l, U (y l)).ι)) := by
  refine ⟨Pi.mapIso fun y : Fin (p + 1) → ι => ?_⟩
  exact (cechModuleSheafFunctor F).mapIso
      (cechOpensProductIsoInf (fun l => U (y l))).symm.op ≪≫
    cechIntersectionSheafIsoPushforward F (⨅ l, U (y l))

end AlgebraicGeometry
