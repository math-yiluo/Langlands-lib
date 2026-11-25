/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.AffineCechInverseImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The inverse-image Cech comparison on cocycles

Source: Stacks Project, Tags 01FD, 02KH, 01XD and 02KE.
(blueprint: lem-pc-flat-cech-cocycle-comparison)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

/-- Extend a Cech cocycle and apply a chain map. This construction needs no flatness:
only the fact that scalar extension takes a zero differential to zero is used.
Source: Stacks Tag 02KH, the map on Cech cocycles in the separated-case argument.
(blueprint: lem-pc-flat-cech-cocycle-comparison) -/
noncomputable def extendedCechCycles (f : X ⟶ Spec (.of R)) (U : ι → X.Opens)
    (M : X.Modules)
    (c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)) (q : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).obj ((cechOver f U M).cycles q) ⟶
      (cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)).cycles q := by
  have : (ModuleCat.extendScalars (algebraMap R S)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).left_adjoint_additive
  refine HomologicalComplex.liftCycles _
    ((ModuleCat.extendScalars (algebraMap R S)).map ((cechOver f U M).iCycles q) ≫ c.f q)
    (q + 1) (by simp) ?_
  rw [Category.assoc, c.comm, ← Category.assoc]
  change (ModuleCat.extendScalars (algebraMap R S)).map ((cechOver f U M).iCycles q) ≫
    (ModuleCat.extendScalars (algebraMap R S)).map ((cechOver f U M).d q (q + 1)) ≫
      c.f (q + 1) = 0
  rw [← Category.assoc, ← Functor.map_comp, HomologicalComplex.iCycles_d,
    Functor.map_zero, zero_comp]

/-- Leray's comparisons identify the class of the pullback of an original Cech
cocycle with its inverse-image cohomology class. There is no assertion about
arbitrary elements of tensor homology, and flatness is not assumed.

Source: Stacks Project, Lemma 20.15.1 (01FD), inverse-image naturality;
Lemma 30.5.2 (02KH), separated-case paragraph;
Lemma 30.2.6 (01XD), and the canonical comparison of Tag 02KE.
(blueprint: lem-pc-flat-cech-cocycle-comparison)

Proof: The affine opens have affine nonempty finite intersections by separatedness
of f over the affine scheme Spec R. Their inverse images are affine after affine
base change, cover X_S, and have affine intersections. Pullback preserves
quasi-coherence. For both covers form the augmented Cech double complex of an
injective resolution of the underlying abelian sheaf. The affine acyclicity of M
and its pullback collapses the vertical comparison, and exactness of the augmented
Cech complex of an injective sheaf gives the comparison with Ext cohomology.
Use these edge maps as the two Leray isomorphisms. Naturality in multiplication
by global functions makes them linear; restrict scalars along f and f_S.
The adjunction unit into p_*p^*M induces the comparison of augmentations. On a
cocycle z its tuple component is pullback of that section. The hypothesis hc,
specialized to b = 1, identifies those tuple components with c applied to 1 tensor
z. The restrictions to intersections in hc are exactly the restriction maps of
the augmented double complexes. Passing to classes therefore gives the displayed
identity. The inverse-image action on Ext, using the canonical constant integer
sheaf isomorphism and the adjoint coefficient map, is H.baseChangeLinear by its
definition. No tensor-homology isomorphism or preservation of kernels by tensor
is used. In degree zero the same augmented comparison is the section map. An
empty cover forces X empty and gives zero groups; the zero algebra gives an empty
base-changed scheme, so the same identity holds in these cases. -/
theorem exists_cechBaseChange_cocycle_comparison
    (f : X ⟶ Spec (.of R)) [IsSeparated f] [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    (c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)) (hc : IsCechBaseChange f U M c) :
    ∃ e : (cechOver f U M).homology q ≅ ModuleCat.of R (HOver f M q),
    ∃ e' : (cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)).homology q ≅
          ModuleCat.of S (HOver (baseChangeSnd (S := S) f)
            (baseChangedModule (S := S) f M) q),
      ∀ z : (cechOver f U M).cycles q,
        e'.hom ((cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
          (baseChangedModule (S := S) f M)).homologyπ q
            (extendedCechCycles f U M c q ((1 : S) ⊗ₜ[R] z))) =
          H.baseChangeLinear (S := S) f M q (e.hom ((cechOver f U M).homologyπ q z)) := by
  classical
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  have hI (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) :=
    IsAffineOpen.iInf (fun l ↦ hU (y l))
  have : IsAffineHom (baseChangeFst (S := S) f) := by
    exact MorphismProperty.pullback_fst (P := @IsAffineHom) _ _
      (isAffineHom_of_isAffine (baseChangeMap R S))
  have : (baseChangedModule (S := S) f M).IsQuasicoherent := by
    dsimp [baseChangedModule]
    infer_instance
  have hV (k : ℕ) (y : Fin (k + 1) → ι) :
      IsAffineOpen (⨅ l, baseChangeCover (S := S) f U (y l)) := by
    have he : (⨅ l, baseChangeCover (S := S) f U (y l)) =
        baseChangeFst (S := S) f ⁻¹ᵁ (⨅ l, U (y l)) := by
      ext x
      simp [baseChangeCover, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    rw [he]
    exact (hI k y).preimage _
  have hcover' : iSup (baseChangeCover (S := S) f U) = ⊤ :=
    (baseChangeFst (S := S) f).iSup_preimage_eq_top hcover
  obtain ⟨e, e', he⟩ := exists_affineCech_inverseImage
    (baseChangeFst (S := S) f) f (baseChangeSnd (S := S) f)
    U (baseChangeCover (S := S) f U) hI hV hcover hcover' M
    (baseChangedModule (S := S) f M) (baseChangeUnit (S := S) f M) q
    (baseChangeCover_intersection_le (S := S) f U)
  refine ⟨e, e', fun z ↦ he z _ ?_⟩
  intro y
  have hi : (cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
      (baseChangedModule (S := S) f M)).iCycles q
        (extendedCechCycles f U M c q ((1 : S) ⊗ₜ[R] z)) =
          c.f q ((1 : S) ⊗ₜ[R] ((cechOver f U M).iCycles q z)) := by
    dsimp only [extendedCechCycles]
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
    rfl
  rw [hi]
  simpa using hc q y 1 ((cechOver f U M).iCycles q z)

end AlgebraicGeometry.Scheme.Modules
