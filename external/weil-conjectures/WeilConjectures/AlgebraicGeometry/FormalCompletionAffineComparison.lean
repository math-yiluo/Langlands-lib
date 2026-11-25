/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.AdicCompletion.Functoriality

import WeilConjectures.AlgebraicGeometry.FormalCompletionAffineNaturalComparison
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine comparison of the completed arrows

Source: Stacks Project, Lemma 0881, affine identification in its proof, and Lemma 087W.
(blueprint: lem-weil-pbc-formal-completion-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private def affineSections (X : Scheme.{u}) (U : X.Opens) :
    CoherentModules X ⥤ ModuleCat.{u} Γ(X, U) :=
  ObjectProperty.ι (C := X.Modules) (RingedSpace.IsCoherent X.toRingedSpace) ⋙
    SheafOfModules.evaluation X.ringCatSheaf (op U)

private instance (X : Scheme.{u}) (U : X.Opens) :
    (affineSections X U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private theorem coherent_inclusion_shortExact (X : Scheme.{u})
    (S : ShortComplex (CoherentModules X)) (hS : S.ShortExact) :
    (S.map (ObjectProperty.ι (C := X.Modules)
      (RingedSpace.IsCoherent X.toRingedSpace))).ShortExact :=
  open scoped ZeroObject in by
    let P : ObjectProperty X.Modules := RingedSpace.IsCoherent X.toRingedSpace
    have h := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
    have : P.ContainsZero := ⟨_, isZero_zero _, h.2.2.2.1⟩
    have : P.IsClosedUnderKernels := by
      constructor
      rintro _ ⟨f, k, hk, hF, hG⟩
      exact h.2.2.2.2 _ _ ((kernelIsKernel f).conePointUniqueUpToIso hk)
        (h.1 _ _ f hF hG).1
    have : P.IsClosedUnderCokernels := by
      constructor
      rintro _ ⟨f, k, hk, hF, hG⟩
      exact h.2.2.2.2 _ _ ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
        (h.1 _ _ f hF hG).2
    have : P.ι.PreservesHomology :=
      ⟨fun {_ _} f ↦ P.preservesKernels_ι f, fun {_ _} f ↦ P.preservesCokernels_ι f⟩
    have := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
    have := P.preservesEpimorphisms_ι_of_isNormalMonoCategory
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map P.ι

set_option backward.isDefEq.respectTransparency false in
private theorem coherent_affine_sections_shortExact (X : Scheme.{u}) [IsNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U)
    (S : ShortComplex (CoherentModules X)) (hS : S.ShortExact) :
    (S.map (affineSections X U)).ShortExact := by
  let T := S.map (ObjectProperty.ι (C := X.Modules) (RingedSpace.IsCoherent X.toRingedSpace))
  have hT := coherent_inclusion_shortExact X S hS
  let : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  let B := T.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := by
    apply preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  have hB : B.ShortExact := hT.map_of_exact (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  have : S.X₁.obj.IsQuasicoherent :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp S.X₁.property |>.1
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    exact TopCat.Sheaf.exists_app_f_eq hB (op U) x hx
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact TopCat.Sheaf.injective_app_f hB (op U)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact Scheme.Modules.surjective_app_of_cechAcyclicOnAffines hB
      (Scheme.Modules.cechAcyclicOnAffines_of_isQuasicoherent S.X₁.obj) hU

set_option backward.isDefEq.respectTransparency false in
/-- The restricted completed arrows identify with adic completions of an original
short exact module sequence. This is a comparison statement: it asserts neither
injectivity nor exactness of the completed maps.

Source: Stacks Project, Lemma 0881, the affine identification in its proof;
Lemma 087W; Algebra, Lemma 00MB (2) supplies the subsequent exactness argument.
(blueprint: lem-weil-pbc-formal-completion-affine-comparison).

Proof:
1. Take A to be the ring of sections on U, and J the sections of I on U. The affine
open of a Noetherian scheme has a Noetherian ring of sections. Restrict S and take
sections. The coherent inclusion preserves kernels and cokernels, open restriction
is exact, and affine sections on quasi-coherent modules are exact. Thus the resulting
module short complex M is short exact. Coherence gives finite sections, in particular
Module.Finite A M.X₂.
2. Identify U.toScheme with Spec A by its canonical affine isomorphism. Transport
formal systems along this isomorphism and use the equivalence of Lemma 087W. Compose
its functor with the finite-module inclusion and restriction of scalars from the
completed ring to A, obtaining F. Each constituent preserves zero morphisms.
The equivalence and full inclusion reflect limits. Scalar restriction creates limits
and reflects isomorphisms, hence reflects limits. Their composite therefore reflects
limits of parallel pairs, without any assertion that formal kernels are termwise.
3. Open restriction commutes with ideal products and their positive powers, and with
quotient cokernels. Affine sections identify these quotients with Mᵢ/J^(n+1)Mᵢ and
identify the induced maps with reductions of M.f and M.g. The equality hρ identifies
these very systems with the underlying systems of V.
4. The natural limiting cones in the affine equivalence identify F.obj V.Xᵢ with
AdicCompletion J M.Xᵢ. Mathlib indexes all nonnegative powers; deleting the initial
zero quotient is cofinal and gives the same limit. Uniqueness of the limit comparison
gives A-linear equivalences eᵢ. Naturality of the cones, checked on every quotient
projection, gives the two displayed equations on arrows.
For J = 0 these are the original modules; for J = A all completions are zero.
Empty affine opens give the zero ring, and zero modules cause no exceptional case.
-/
theorem formalCompletion_affine_comparison (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (h : (completion X I).Additive)
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (ρ : CoherentFormalModule X I ⥤ CoherentFormalModule U.toScheme (I.comap U.ι))
    (hz : ρ.PreservesZeroMorphisms)
    (hρ : ρ ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
      (IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι))
    (S : ShortComplex (CoherentModules X)) (hS : S.ShortExact) :
    let T := @ShortComplex.map _ _ _ _ _ _ S (completion X I)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (completion X I) h)
    let V := @ShortComplex.map _ _ _ _ _ _ T ρ hz
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (J : Ideal A)
      (M : ShortComplex (ModuleCat.{u} A)),
      Module.Finite A M.X₂ ∧ M.ShortExact ∧
      ∃ F : CoherentFormalModule U.toScheme (I.comap U.ι) ⥤ ModuleCat.{u} A,
        F.PreservesZeroMorphisms ∧ ReflectsLimitsOfShape WalkingParallelPair F ∧
        ∃ (e₁ : F.obj V.X₁ ≃ₗ[A] AdicCompletion J M.X₁)
          (e₂ : F.obj V.X₂ ≃ₗ[A] AdicCompletion J M.X₂)
          (e₃ : F.obj V.X₃ ≃ₗ[A] AdicCompletion J M.X₃),
          (∀ x, e₂ ((F.map V.f) x) = AdicCompletion.map J M.f.hom (e₁ x)) ∧
          (∀ x, e₃ ((F.map V.g) x) = AdicCompletion.map J M.g.hom (e₂ x)) := by
  let A := Γ(X, U)
  have hA : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let M := S.map (affineSections X U)
  have hM : M.ShortExact := coherent_affine_sections_shortExact X U hU S hS
  have hfinite : Module.Finite A M.X₂ := by
    have hcoh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
      X S.X₂.obj).mp S.X₂.property
    have : S.X₂.obj.IsQuasicoherent := hcoh.1
    have : S.X₂.obj.IsFiniteType := hcoh.2
    exact Scheme.Modules.finite_sections_of_finiteType S.X₂.obj hU
  obtain ⟨F, hF, hr, e, he⟩ :=
    formalCompletion_affine_natural_comparison X I U hU ρ hρ
  refine ⟨A, inferInstance, hA, I.ideal ⟨U, hU⟩, M, hfinite, hM,
    F, hF, hr, e S.X₁, e S.X₂, e S.X₃, ?_, ?_⟩
  · exact he S.X₁ S.X₂ S.f
  · exact he S.X₂ S.X₃ S.g

end AlgebraicGeometry
