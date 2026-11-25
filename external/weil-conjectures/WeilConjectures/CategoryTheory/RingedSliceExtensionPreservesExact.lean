/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists

/-!
# Preservation of exactness by ringed-slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8G
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

-- Direct sums of sectionwise injections remain injective (Stacks 03DJ).
private theorem extensionPresheaf_preservesMonomorphisms
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C) :
    (extensionByZeroPresheaf.{max u v} R U).PreservesMonomorphisms where
  preserves {F G} a ha := by
    classical
    apply PresheafOfModules.mono_of_injective
    intro V
    change Function.Injective (DirectSum.lmap (R := R.obj.obj V)
      (fun φ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
    apply (DirectSum.lmap_injective _).mpr
    intro φ
    apply (ModuleCat.mono_iff_injective _).mp
    exact (evaluation (R.over U) (Opposite.op (Over.mk φ))).map_mono a

/-- The sheafified direct-sum extension preserves exactness at the middle term.

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8G
(auxiliary; not a blueprint node).

Proof: Write L for the displayed extension and T for restriction to the slice.
A map from the direct-sum presheaf of G to a module sheaf F is specified by
its maps on each summand. Naturality identifies these maps with a morphism
G → T(F); conversely such a morphism extends by the direct-sum universal
property. Module sheafification extends this bijection uniquely to maps
L(G) → F, giving L ⊣ T. Thus L preserves colimits and is right exact.
A monomorphism of module sheaves is injective on sections. Its direct-sum
extension is injective on every summand and hence on the whole direct sum.
Exact module sheafification preserves this injection, so L preserves monos.
An additive right exact functor between abelian categories that preserves
monos is exact: factor the first arrow through its image, then use the
short exact sequence from that image to the middle and final image.
Consequently L sends S.Exact to exactness of S.map L, which is the displayed
image-kernel equality. This argument uses arbitrary covering sieves and
requires neither pullbacks in C nor equality of its two universes. -/
theorem ringedSliceExtension_preserves_exact
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max u v}) (U : C)
    (S : ShortComplex (ringedSiteModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).over U)))
    (hS : S.Exact) :
    let R := (sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
    let L := extensionByZeroPresheaf.{max u v} R U ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
    imageSubobject (L.map S.f) = kernelSubobject (L.map S.g) := by
  let R := (sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
  let L := extensionByZeroPresheaf.{max u v} R U ⋙
    PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
  have : (overFunctor.{max u v} R U).Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  let adj := CategoryTheory.extensionSheafAdjunction R U
  have : L.Additive := adj.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L := inferInstance
  have : (extensionByZeroPresheaf.{max u v} R U).PreservesMonomorphisms :=
    extensionPresheaf_preservesMonomorphisms R U
  have : L.PreservesMonomorphisms := inferInstance
  have hshort : ∀ T : ShortComplex (SheafOfModules.{max u v} (R.over U)),
      T.ShortExact → (T.map L).ShortExact := by
    intro T hT
    have : Mono T.f := hT.mono_f
    have : Mono (T.map L).f := L.map_mono T.f
    have hright : (T.map L).Exact ∧ Epi (T.map L).g :=
      (T.map L).exact_and_epi_g_iff_g_is_cokernel.mpr
        ⟨CokernelCofork.mapIsColimit _ hT.gIsCokernel L⟩
    have : Epi (T.map L).g := hright.2
    exact ⟨hright.1⟩
  have hex : ∀ T : ShortComplex (SheafOfModules.{max u v} (R.over U)),
      T.Exact → (T.map L).Exact := (L.exact_tfae.out 1 2).mp hshort
  exact (S.map L).exact_iff_image_eq_kernel.mp (hex S hS)

end SheafOfModules
