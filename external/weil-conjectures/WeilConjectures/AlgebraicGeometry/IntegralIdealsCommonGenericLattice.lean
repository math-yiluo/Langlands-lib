/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.CoherentPushforwardIdeal
import WeilConjectures.AlgebraicGeometry.CommonGenericLatticeMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Generic common lattices for two integral ideal sheaves

Source: Stacks Project, Tag 01YH, `lemma-property-irreducible`, proof, the intersection
of the two nonzero ideals and its two inclusions.
(blueprint: lem-pc-r2-integral-ideals-common-generic-lattice)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Two nonzero integral ideals have coherent pushforward and a coherent common generic lattice.
Source: Stacks Project, Tag 01YH, `lemma-property-irreducible`, proof, the paragraph
beginning "Next, suppose" and its two intersection sequences.
(blueprint: lem-pc-r2-integral-ideals-common-generic-lattice)

Proof: W is locally Noetherian as a closed subscheme of X. The zero ideal has zero
sections on every affine open, hence a zero module; pushforward preserves zero objects.
Thus the hypothesis on i_*I implies I is nonzero. Ideals are quasi-coherent kernels;
coherent submodule closure inside the coherent structure module proves I is coherent.
Construct L = Ker(I.toModules → O_W → (W/J)_*O_(W/J)). Its kernel arrow b_0 is mono.
The composite L → I.toModules → O_W lifts to J.toModules by its kernel universal
property. Call this lift d_0; its composite with the mono J → O_W is the mono
L → I → O_W, so d_0 is mono. L is a quasi-coherent submodule of coherent I,
hence coherent, as is i_*I by closed pushforward. This constructs the intersection
as a kernel, with no arbitrary choice.
Both I and J have full generic stalk by the integral-ideal criterion. Since J → O_W
is surjective there and its composite with O_W → (W/J)_*O_(W/J) is zero, the latter
map is zero at the generic stalk. Kernel-stalk exactness therefore makes b_0 bijective.
The equality d_0 followed by J → O_W = b_0 followed by I → O_W, and bijectivity
of the three other generic maps, make d_0 bijective. Set K = i_*L and push forward
the two maps. Finite pushforward preserves coherence and monomorphisms, and naturality
of closed-pushforward stalk comparison transfers the two generic bijections. The proof
uses no cokernel-support result. Unit ideals and zero cokernels require no separate case;
zero ideals are excluded precisely by the two stated nonzero hypotheses. -/
theorem integral_ideals_common_generic_lattice {X W : Scheme.{u}}
    [IsLocallyNoetherian X] (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I J : W.IdealSheafData) (hI : ¬ IsZero ((pushforward i).obj I.toModules))
    (hJ : J ≠ ⊥) :
    ∃ (K : X.Modules) (b : K ⟶ (pushforward i).obj J.toModules)
      (d : K ⟶ (pushforward i).obj I.toModules),
      RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) ∧
      RingedSpace.IsCoherent X.toRingedSpace K ∧ Mono b ∧ Mono d ∧
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).map b) ∧
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).map d)  := by
  obtain ⟨K, b, d, hK, hb, hd, hbξ, hdξ⟩ :=
    exists_common_generic_lattice_maps i I J hI hJ
  have hIcoh := coherent_pushforward_ideal i I
  exact ⟨K, b, d, hIcoh, hK, hb, hd, hbξ, hdξ⟩

end AlgebraicGeometry.Scheme.Modules
