/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.AffineConormalSectionsExistence
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-!
# Affine sections of the conormal sheaf

Source: Stacks Project, Morphisms, Definition 01R2 (definition-conormal-sheaf)
and Lemma 01R3 (lemma-affine-conormal), assertion (2)
(blueprint: lem-weil-pbc-affine-conormal-sections).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The tensor pullback of the ideal of a closed immersion is quasi-coherent, and its
sections on the inverse image of an affine open are canonically `I/I²`.
The affine coordinates are supplied by `r : R ≃+* Γ(X, U)`. The hypothesis on `I` says that
`Z ∩ U = Spec(R/I)` over `U`: for a closed immersion this is equivalent to
`I = ker((i.app U) ∘ r)`.
The target is written as sections of the pushforward, whose scalar action is restriction
along `i.app U`; its underlying group is exactly the conormal sections over `i ⁻¹ᵁ U`.
The equation on ideal sections pins the equivalence to the canonical map `a mod I² ↦ i* a`.
Semilinearity along `r` expresses `R`-linearity in these coordinates. Since `(i.app U) ∘ r`
is surjective with kernel `I`, the equivalence is also `R/I`-linear.

Source: Stacks Project, Morphisms, Definition 01R2 and Lemma 01R3 (2)
(blueprint: lem-weil-pbc-affine-conormal-sections).
Proof, following the node's five steps:
1. By def-sbc-closed-immersion-ideal-sheaf and
   lem-weil-pbc-closed-immersion-affine-cover-criterion, the inverse image of `U` is affine,
   its section ring is `R/I`, and the ideal sheaf on `U` is the associated module of `I`.
2. By lem-weil-pbc-module-pullback-quasi-coherent, pulling this quasi-coherent ideal sheaf
   back along `i` gives a quasi-coherent conormal sheaf (pqf-def-coherent).
3. By lem-weil-pbc-module-pullback-affine-sections, the canonical section map identifies
   these conormal sections with `I ⊗[R] (R/I)`; it sends `a ⊗ 1` to the pullback of `a`.
4. By lem-weil-pbc-tensor-over-quotient-ring and the tensor swap, this tensor product is
   `I/I²`, via `a ⊗ r̄ ↦ ra mod I²`. Both sides are annihilated by `I`, so this is also
   an `R/I`-linear equivalence.
5. Compose the inverse of the equivalence in step 4 with that in step 3. Its value on
   `a mod I²` is the tensor-pullback unit on the ideal section `a`, giving the displayed
   equation and the canonical identification, independently of any choices. -/
theorem affine_conormal_sections {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ((tensorPullback i).obj i.ker.toModules).IsQuasicoherent ∧
      ∀ (U : X.affineOpens) (R : Type v) [CommRing R]
        (r : R ≃+* Γ(X, U.1)) (I : Ideal R),
        I = RingHom.ker ((i.app U.1).hom.comp (r : R →+* Γ(X, U.1))) →
        ∃ e : LinearEquiv (r : R →+* Γ(X, U.1))
            (σ' := (r.symm : Γ(X, U.1) →+* R)) I.Cotangent
            Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), U.1),
          ∀ (a : I) (s : Γ(i.ker.toModules, U.1)),
            i.ker.toModulesι.app U.1 s = r (a : R) →
            e (I.toCotangent a) =
              ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).app U.1 s := by
  constructor
  · have := SheafOfModules.isQuasicoherent_unit (R := i.ker.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward i.ker.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)) :=
      isQuasicoherent_pushforward_of_isClosedImmersion i.ker.subschemeι _
    have : i.ker.toModules.IsQuasicoherent :=
      isQuasicoherent_kernel i.ker.toPushforwardSubscheme
    let e : tensorPullback i ≅ pullback i :=
      (Classical.choose (exists_tensorPullbackAdjunction i)).leftAdjointUniq
        (pullbackPushforwardAdjunction i)
    exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (e.app i.ker.toModules).symm (by infer_instance)
  · exact affine_conormal_sections_existence i

end AlgebraicGeometry.Scheme.Modules
