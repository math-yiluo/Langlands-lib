/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Construction of the common generic lattice, with coherence separated from the
coherence of the original pushed ideal.
(blueprint: lem-pc-r2-common-generic-lattice-maps)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem pushforward_stalk_isIso {X W : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] {F G : W.Modules} (f : F ⟶ G) (z : W)
    (hf : IsIso ((RingedSpace.moduleStalkFunctor W.toRingedSpace z).map f)) :
    IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base z)).map
      ((pushforward i).map f)) := by
  let cF := TopCat.Presheaf.stalkPushforward Ab i.base F.presheaf z
  let cG := TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z
  have : IsIso cF := (closedImmersion_pushforward_stalks i i.isClosedEmbedding F).2.1 z |>.2.1
  have : IsIso cG := (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).2.1 z |>.2.1
  let s := (TopCat.Presheaf.stalkFunctor Ab z).map f.mapPresheaf
  have : IsIso s := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ConcreteCategory.bijective_of_isIso
      ((RingedSpace.moduleStalkFunctor W.toRingedSpace z).map f)
  let t := (TopCat.Presheaf.stalkFunctor Ab (i.base z)).map
    ((pushforward i).map f).mapPresheaf
  have ht : t = cF ≫ s ≫ inv cG := by
    apply (cancel_mono cG).1
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
      (closedImmersion_pushforward_stalks i i.isClosedEmbedding F).2.2 G f z
  have : IsIso t := by rw [ht]; infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso t

/-- Two nonzero ideals on an integral closed subscheme admit a coherent common
generic lattice and monomorphisms into both pushed ideals, which are isomorphisms
at the generic point.  The coherence of the pushed ideal itself is separate.
Source: Stacks Project, Cohomology of Schemes, Tag 01YH, intersection comparison.
(blueprint: lem-pc-r2-common-generic-lattice-maps)

Proof: Nonzero pushed I implies I is nonzero: if I were zero, its affine sections
would vanish, hence its module and its pushforward would be zero. Set
L = kernel (I.toModulesι followed by J.toPushforwardSubscheme). Its kernel arrow
d embeds it into I. The composite into the structure module factors through the
kernel defining J, giving b; its composite with the inclusion of J equals the
mono d followed by the inclusion of I, so b is mono too. Both ideals and the
pushed structure module of the subscheme defined by J are coherent, by coherent
kernel closure and finite pushforward. Thus L is coherent by kernel closure.
At the generic point both ideal inclusions are isomorphisms. The comparison from
the structure module to the quotient defined by J is therefore zero there.
Kernel-stalk exactness makes d an isomorphism, and the equality of composites
makes b one too. Push L, b and d forward along i. This preserves coherence and
monomorphisms. The bijective, natural closed-pushforward stalk comparisons
conjugate the two stalk maps into the original isomorphisms. The construction
also covers unit ideals; no witness is selected from an existence theorem.
-/
theorem exists_common_generic_lattice_maps {X W : Scheme.{u}}
    [IsLocallyNoetherian X] (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I J : W.IdealSheafData) (hI : ¬ IsZero ((pushforward i).obj I.toModules))
    (hJ : J ≠ ⊥) :
    ∃ (K : X.Modules) (b : K ⟶ (pushforward i).obj J.toModules)
      (d : K ⟶ (pushforward i).obj I.toModules),
      RingedSpace.IsCoherent X.toRingedSpace K ∧ Mono b ∧ Mono d ∧
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).map b) ∧
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).map d) := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian i
  have (T : W.IdealSheafData) : IsLocallyNoetherian T.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian T.subschemeι
  have coherent_unit (T : Scheme.{u}) [IsLocallyNoetherian T] :
      RingedSpace.IsCoherent T.toRingedSpace (SheafOfModules.unit T.ringCatSheaf) := by
    have : (SheafOfModules.unit T.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have : (SheafOfModules.unit T.ringCatSheaf).IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    have : (SheafOfModules.unit T.ringCatSheaf).IsFinitePresentation :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
    exact (isCoherent_iff_isQuasicoherent_and_isFiniteType T _).mpr
      ⟨SheafOfModules.isQuasicoherent_unit.{u, u, u},
        SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} _⟩
  have coherent_pushforward {S T : Scheme.{u}} (f : S ⟶ T)
      [IsFinite f] [IsLocallyNoetherian T] (G : S.Modules)
      (hG : RingedSpace.IsCoherent S.toRingedSpace G) :
      RingedSpace.IsCoherent T.toRingedSpace ((pushforward f).obj G) := by
    have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian f
    obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType S G).mp hG
    have : G.IsQuasicoherent := hq
    have : G.IsFiniteType := ht
    exact (isCoherent_iff_isQuasicoherent_and_isFiniteType T _).mpr
      (isQuasicoherent_and_isFiniteType_pushforward_of_isFinite f G)
  have hIne : I ≠ ⊥ := by
    intro hbot
    apply hI
    apply (pushforward i).map_isZero
    apply isZero_of_forall_affineOpens
    intro U
    refine ⟨fun a b ↦ ?_⟩
    apply I.injective_toModulesι_app U.1
    have zero (a : Γ(I.toModules, U.1)) : I.toModulesι.app U.1 a = 0 := by
      have ha : I.toModulesι.app U.1 a ∈ (I.ideal U : Set Γ(W, U.1)) := by
        rw [← I.range_toModulesι_app U]
        exact Set.mem_range_self a
      simpa [hbot] using ha
    exact (zero a).trans (zero b).symm
  let q := I.toModulesι ≫ J.toPushforwardSubscheme
  let L := kernel q
  let d : L ⟶ I.toModules := kernel.ι q
  let b : L ⟶ J.toModules := kernel.lift J.toPushforwardSubscheme
    (d ≫ I.toModulesι) (by simp [d, q, Category.assoc])
  have hbd : b ≫ J.toModulesι = d ≫ I.toModulesι := kernel.lift_ι _ _ _
  have : Mono d := inferInstance
  have : Mono (b ≫ J.toModulesι) := by rw [hbd]; infer_instance
  have : Mono b := mono_of_mono b J.toModulesι
  have hW := coherent_unit W
  have ideal_coh (T : W.IdealSheafData) : RingedSpace.IsCoherent W.toRingedSpace T.toModules := by
    have hunit := coherent_unit T.subscheme
    have hquot := coherent_pushforward T.subschemeι _ hunit
    exact ((isCoherent_kernel_cokernel_biprod_and_submodule W).1 _ _
      hW hquot).1 T.toPushforwardSubscheme |>.1
  have hJunit := coherent_unit J.subscheme
  have hJquot := coherent_pushforward J.subschemeι _ hJunit
  have hL : RingedSpace.IsCoherent W.toRingedSpace L :=
    ((isCoherent_kernel_cokernel_biprod_and_submodule W).1 _ _
      (ideal_coh I) hJquot).1 q |>.1
  let S := RingedSpace.moduleStalkFunctor W.toRingedSpace (genericPoint W)
  have hi : IsIso (S.map I.toModulesι) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(integral_ideal_generic_stalk W I).2.1,
        (integral_ideal_generic_stalk W I).2.2.2.2.mp hIne⟩
  have hj : IsIso (S.map J.toModulesι) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(integral_ideal_generic_stalk W J).2.1,
        (integral_ideal_generic_stalk W J).2.2.2.2.mp hJ⟩
  have hJzero : S.map J.toPushforwardSubscheme = 0 := by
    apply (cancel_epi (S.map J.toModulesι)).1
    rw [← S.map_comp]
    simp [IdealSheafData.toModulesι]
  have hqzero : S.map q = 0 := by simp [q, hJzero]
  have hdexact := (RingedSpace.module_stalk_exact W.toRingedSpace q).2.1 (genericPoint W)
  have : Mono (S.map d) := hdexact.1
  have : Epi (S.map d) := (ShortComplex.exact_iff_epi _ hqzero).mp hdexact.2
  have hd : IsIso (S.map d) := isIso_of_mono_of_epi _
  have hb : IsIso (S.map b) := by
    have he : S.map b = S.map d ≫ S.map I.toModulesι ≫ inv (S.map J.toModulesι) := by
      apply (cancel_mono (S.map J.toModulesι)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← S.map_comp, hbd]
    rw [he]
    infer_instance
  exact ⟨(pushforward i).obj L, (pushforward i).map b, (pushforward i).map d,
    coherent_pushforward i L hL, inferInstance, inferInstance,
    pushforward_stalk_isIso i b _ hb, pushforward_stalk_isIso i d _ hd⟩

end AlgebraicGeometry.Scheme.Modules
