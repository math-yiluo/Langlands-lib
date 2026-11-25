/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback

/-! # Pullback of completion with normalized quotient projections

Source: Stacks Project, Tag 0887 and the completion identity in Tag 088B.
(blueprint: lem-weil-pbc-formal-completion-pullback-normalized).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The completion-pullback isomorphism carries the pulled quotient projection to
its new quotient projection, including specified transports of the ideal and module.
Source: Stacks Project, Tag 0887 and the completion identity in the proof of 088B.
(blueprint: lem-weil-pbc-formal-completion-pullback-normalized).

Proof: Eliminate the equalities of the ideal and underlying module. Take the inverse
of the completionPullbackIso component at F. At level n it is the inverse of
powerQuotientIso. The projection equation powerQuotientIso_pi says the new quotient
projection followed by its forward component equals the pulled original quotient
projection. Postcompose with the inverse component and cancel the isomorphism.
The quotient comparisons form an isomorphism of inverse systems by their naturality
at the transition maps; this is exactly the existing completionPullbackIso.
The normalization uniquely determines every component, because the pulled quotient
projection is an epimorphism (tensor pullback preserves cokernels). Thus these are
specified quotient maps, and the conclusion does not choose arbitrary isomorphisms.
The argument applies to empty schemes, zero modules and zero or unit ideals. -/
theorem exists_formalCompletionPullback_normalized
    {X Y : Scheme.{u}} [IsNoetherian Y] (a : X ⟶ Y) (J : Y.IdealSheafData)
    (F : CoherentModules Y) (I : X.IdealSheafData) (hI : J.comap a = I)
    (M : X.Modules) (hM : M = (Scheme.Modules.tensorPullback a).obj F.obj) :
    ∃ e : formalCompletionSystem J F.obj ⋙ Scheme.Modules.tensorPullback a ≅
        formalCompletionSystem I M,
      ∀ n : ℕ, (Scheme.Modules.tensorPullback a).map
          (formalModuleQuotientπ J (n + 1) F.obj) ≫ e.hom.app (op n) =
        eqToHom hM.symm ≫ formalModuleQuotientπ I (n + 1) M := by
  classical
  subst I
  subst M
  refine ⟨((completionPullbackIso a J).app F).symm, ?_⟩
  intro n
  have hF : F.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp F.property).1
  change (Scheme.Modules.tensorPullback a).map
      (formalModuleQuotientπ J (n + 1) F.obj) ≫
        (powerQuotientIso a J F.obj hF (n + 1)).inv =
    𝟙 _ ≫ formalModuleQuotientπ (J.comap a) (n + 1)
      ((Scheme.Modules.tensorPullback a).obj F.obj)
  rw [← powerQuotientIso_π a J F.obj hF (n + 1)]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

end AlgebraicGeometry
