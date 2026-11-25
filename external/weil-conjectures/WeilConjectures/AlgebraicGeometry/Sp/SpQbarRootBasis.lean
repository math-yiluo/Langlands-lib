/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
import WeilConjectures.AlgebraicGeometry.Sp.SpQbarPositiveRootBasis

/-! # Local bases from a prescribed compatible root tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

/-- On one slice with a normalized compatible root basis, the specified field colimit
of rational twists is a free rank-one module over the field-colimit coefficient.

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, clause (3), algebraic-closure case;
sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md, field-colimit formula.
(blueprint: lem-sp-qbar-root-basis)

Proof: use on this slice the basis b -> b tensor zeta_n at every finite quotient.
The normalization he and compatibility hζ make these bases commute with the
coefficient reductions. Taking inverse limits and identifying the cofinal ell-power
coefficient limit with O_E,X gives a normalized integral basis for every E. Extending
scalars gives a rational basis for every E. For E contained in F the finite transition
sends b tensor zeta_n to i_EF(b) tensor zeta_n, because the root sections do not depend
on E. Thus the integral bases commute with field transitions by the limit projection
identities; the rational bases commute by their scalar-extension pure-tensor formula.
They give an isomorphism from the rational twist diagram to the coefficient diagram
on the slice. Restriction to the slice commutes with their sheafified colimits:
presheaf colimits use the same sections, and the slice has the same covering families,
so the sheafification universal properties agree. The coefficient colimit is Qbar_X
since pullback from the point preserves the finite-subextension colimit. Take colimits
of the basis maps and their inverses. To check linearity, represent a scalar at stage E
and a twist section at stage F locally, and choose a finite H containing both. At H
the basis map is H_X-linear and commutes with the transitions, so preserves their
product. A larger common stage gives the same identity. Sheafification extends it
from these local representatives to all sections. The resulting isomorphism and
its inverse respect exactly the action specifying spQbarTwist. Transport through the
internal/sectionwise equivalence and the degree-one/zero identifications gives the
stated isomorphism. This uses the prescribed roots and coefficient stages throughout. -/
theorem spQbarRootBasis
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n)) :
    Nonempty ((spSignedTwist X _ (spQbarTwist X ℓ) 1).over W ≅
      (spSignedTwist X _ (spQbarTwist X ℓ) 0).over W) := by
  simpa using spQbarPositiveRootBasis X ℓ W ζ e hζ he 0

end AlgebraicGeometry.ProEtale
