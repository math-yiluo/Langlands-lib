/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# The free abelian presentation of a torsor extension

Source: Stacks Project, Lemma 02FQ, first construction.
(blueprint: lem-sc-zariski-torsor-free-extension-short-exact)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u})
variable {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (T : Torsor G)

namespace FreeExtension

/-- The free abelian sheaf on the sections of the torsor. -/
noncomputable abbrev freeSheaf :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (T.sheaf.obj ⋙ AddCommGrpCat.free)

/-- The free abelian sheaf on pairs of sections. -/
noncomputable abbrev relations :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (T.pairs ⋙ AddCommGrpCat.free)

/-- The relation sending `(x,y)` to `[y]-[x]`. -/
noncomputable abbrev difference : relations X T ⟶ freeSheaf X T :=
  (presheafToSheaf _ _).map T.pairsDiff

/-- The relation sending `(x,y)` to the unique `g` with `g +ᵥ x = y`. -/
noncomputable def displacement : relations X T ⟶ G :=
  ⟨sheafifyLift _ T.pairsSub G.property⟩

/-- The quotient of `G ⊕ ℤ[T]` by `[y]-[x] = y-x`, formed as a pushout. -/
noncomputable abbrev extension := pushout (difference X T) (displacement X T)

/-- The inclusion of the coefficient sheaf in the presented extension. -/
noncomputable abbrev inclusion : G ⟶ extension X T :=
  pushout.inr (difference X T) (displacement X T)

/-- The map of the free generators to the presented extension. -/
noncomputable abbrev generators : freeSheaf X T ⟶ extension X T :=
  pushout.inl (difference X T) (displacement X T)

/-- The constant integer presheaf, in the coefficient universe of the torsor. -/
abbrev integers : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u, 0} ℤ))

/-- Augmentation of the free abelian presheaf. -/
def augmentation : T.sheaf.obj ⋙ AddCommGrpCat.free ⟶ integers X where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ ↦ (⟨1⟩ : ULift.{u, 0} ℤ))
  naturality U V f := by
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun t ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of t)) = _
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
    rfl

private lemma difference_augmentation : T.pairsDiff ≫ augmentation X T = 0 := by
  ext U : 2
  ext : 1
  refine FreeAbelianGroup.lift_ext _ _ fun p ↦ ?_
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p)) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub, _root_.sub_self]

/-- Augmentation of the free abelian sheaf. -/
noncomputable abbrev degree : freeSheaf X T ⟶
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u, 0} ℤ)) :=
  (presheafToSheaf _ _).map (augmentation X T)

/-- The pair-difference relation has degree zero. -/
lemma difference_degree : difference X T ≫ degree X T = 0 := by
  rw [← Functor.map_comp, difference_augmentation]
  exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_zero _ _

/-- The degree of a section of the presented extension. -/
noncomputable def projection : extension X T ⟶
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u, 0} ℤ)) :=
  pushout.desc (degree X T) 0 (by rw [difference_degree, comp_zero])

/-- The coefficient sheaf lies in degree zero. -/
lemma inclusion_projection : inclusion X T ≫ projection X T = 0 := by
  apply pushout.inr_desc

/-- A local section of the torsor gives a degree-one section of the extension. -/
noncomputable def generator (U : (Opens X)ᵒᵖ) (t : T.sheaf.obj.obj U) :
    (extension X T).obj.obj U :=
  (generators X T).hom.app U
    ((toSheafify (Opens.grothendieckTopology X)
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (FreeAbelianGroup.of t))

private lemma augmentation_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (augmentation X T) := by
  constructor
  intro U n
  refine (Opens.grothendieckTopology X).superset_covering
    (fun V f hf ↦ ?_) (T.nonemptySieve_mem U)
  obtain ⟨t⟩ := hf
  refine ⟨n.down • FreeAbelianGroup.of t, ?_⟩
  change FreeAbelianGroup.lift _ (n.down • FreeAbelianGroup.of t) = n
  rw [map_zsmul, FreeAbelianGroup.lift_apply_of]
  apply ULift.ext
  change n.down • (1 : ℤ) = n.down
  simp

/-- Every integer section locally lifts to the presented extension. -/
lemma projection_epi : Epi (projection X T) := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (augmentation X T) :=
    augmentation_locallySurjective X T
  have : Sheaf.IsLocallySurjective (degree X T) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).mpr inferInstance
  have : Epi (degree X T) := inferInstance
  exact epi_of_epi_fac (pushout.inl_desc (degree X T) 0 _)

private lemma kernel_difference_displacement :
    kernel.ι (difference X T) ≫ displacement X T = 0 := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  rw [← PreservesKernel.iso_inv_ι F T.pairsDiff, Category.assoc]
  have h : F.map (kernel.ι T.pairsDiff) ≫ displacement X T = 0 := by
    ext1
    change sheafifyMap (Opens.grothendieckTopology X) (kernel.ι T.pairsDiff) ≫
      sheafifyLift (Opens.grothendieckTopology X) T.pairsSub G.property = 0
    rw [sheafifyMap_sheafifyLift, T.kernel_ι_pairsDiff_comp_pairsSub]
    apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _ G.property
    simp
  rw [h, comp_zero]

/-- The relation presentation never identifies two different coefficients. -/
lemma inclusion_mono : Mono (inclusion X T) := by
  let sq := IsPushout.of_hasPushout (difference X T) (displacement X T)
  have : Epi (kernel.map (difference X T) (inclusion X T)
      (displacement X T) (generators X T) sq.w) :=
    Abelian.epi_kernel_map_of_isPushout sq
  apply Abelian.mono_of_kernel_ι_eq_zero
  rw [← cancel_epi (kernel.map (difference X T) (inclusion X T)
    (displacement X T) (generators X T) sq.w), kernel.map, kernel.lift_ι]
  simp only [kernel_difference_displacement, comp_zero]

private lemma degree_desc
    {H : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (k : freeSheaf X T ⟶ H) (hk : difference X T ≫ k = 0) :
    ∃ q : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u, 0} ℤ)) ⟶ H, degree X T ≫ q = k := by
  let J := Opens.grothendieckTopology X
  let β : T.sheaf.obj ⋙ AddCommGrpCat.free ⟶ H.obj := toSheafify J _ ≫ k.hom
  let b (U : (Opens X)ᵒᵖ) (t : T.sheaf.obj.obj U) : H.obj.obj U :=
    β.app U (FreeAbelianGroup.of t)
  have hb_nat {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (t : T.sheaf.obj.obj U) :
      H.obj.map f (b U t) = b V (T.sheaf.obj.map f t) := by
    exact (congr_arg (fun η ↦ η (FreeAbelianGroup.of t)) (β.naturality f)).symm
  have hβ : T.pairsDiff ≫ β = 0 := by
    dsimp [β]
    rw [← Category.assoc, toSheafify_naturality, Category.assoc]
    change toSheafify J _ ≫ (difference X T ≫ k).hom = 0
    rw [hk]
    simp
  have hb_inv (U : (Opens X)ᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U) :
      b U (T.vadd U g t) = b U t := by
    have h := congr_arg (fun η ↦ η.app U
      (FreeAbelianGroup.of ((t, T.vadd U g t) : T.pairs.obj U))) hβ
    change β.app U (FreeAbelianGroup.lift _ (FreeAbelianGroup.of _)) = 0 at h
    rw [FreeAbelianGroup.lift_apply_of, map_sub] at h
    exact sub_eq_zero.mp h
  let htop := IsTerminal.ofUnique (⊤ : Opens X)
  obtain ⟨σ, hσ⟩ := T.exists_section_of_invariant
    ((sheafCompose J (forget AddCommGrpCat.{u})).obj H) htop b
    (fun _ _ f t ↦ hb_nat f t) hb_inv
  let η : integers X ⟶ H.obj :=
    { app U := AddCommGrpCat.ofHom
        { toFun n := n.down • H.obj.map (htop.from U.unop).op σ
          map_zero' := by simp
          map_add' n m := by simp [add_zsmul] }
      naturality U V f := by
        ext n
        change n.down • H.obj.map (htop.from V.unop).op σ =
          H.obj.map f (n.down • H.obj.map (htop.from U.unop).op σ)
        rw [map_zsmul, ← ConcreteCategory.comp_apply, ← H.obj.map_comp]
        congr 2
        }
  let q : (constantSheaf J AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u, 0} ℤ)) ⟶ H :=
    ⟨sheafifyLift J η H.property⟩
  refine ⟨q, ?_⟩
  ext1
  apply sheafify_hom_ext J _ _ H.property
  change toSheafify J _ ≫ sheafifyMap J (augmentation X T) ≫
    sheafifyLift J η H.property = β
  rw [← toSheafify_naturality_assoc, toSheafify_sheafifyLift]
  ext U : 2
  ext : 1
  refine FreeAbelianGroup.lift_ext _ _ fun t ↦ ?_
  change (FreeAbelianGroup.lift (fun _ ↦ (⟨1⟩ : ULift.{u, 0} ℤ))
    (FreeAbelianGroup.of t)).down •
    H.obj.map (htop.from U.unop).op σ = b U t
  rw [FreeAbelianGroup.lift_apply_of]
  have hs : b U t = H.obj.map (htop.from U.unop).op σ := hσ U t
  simpa using hs.symm

private lemma projection_exact :
    (ShortComplex.mk (inclusion X T) (projection X T) (inclusion_projection X T)).Exact := by
  have := projection_epi X T
  apply ShortComplex.exact_of_g_is_cokernel
  apply CokernelCofork.IsColimit.ofπ'
  intro H k hk
  apply Classical.choice
  obtain ⟨q, hq⟩ := degree_desc X T (generators X T ≫ k) (by
    rw [← Category.assoc, pushout.condition, Category.assoc, hk, comp_zero])
  refine ⟨⟨q, ?_⟩⟩
  apply pushout.hom_ext
  · simpa [← Category.assoc, projection] using hq
  · simp [← Category.assoc, projection, hk]

/-- The free abelian relation presentation of a torsor is a short exact extension.

Source: Stacks Project, Lemma 02FQ, first construction
(https://stacks.math.columbia.edu/tag/02FQ).
Proof: The augmentation sends every free generator to one, and annihilates each
pair difference. Push it out against the pair-displacement map to define the degree
projection. Given an integer `n`, a local torsor section `t` gives the preimage
`n[t]`, so augmentation and projection are epimorphisms after sheafification.
The displacement map kills the kernel of pair differences, by
`Torsor.kernel_ι_pairsDiff_comp_pairsSub`. Sheafification preserves this kernel.
In an abelian pushout, the induced map from the kernel of the top arrow to the
kernel of the bottom arrow is epi (`Abelian.epi_kernel_map_of_isPushout`). Its
composite with the bottom kernel inclusion is zero, hence that inclusion is zero
and the coefficient inclusion is mono.
For exactness, a map out of the free sheaf killing pair differences has equal values
on every pair of torsor sections, so its values are invariant under the torsor action.
`Torsor.exists_section_of_invariant` glues them to a global section of the codomain.
Integer multiples of its restrictions define a map from the constant integer sheaf.
Checking on free generators proves the factorization through augmentation. The
pushout universal property therefore makes projection a cokernel of inclusion;
uniqueness follows from projection being epi. A monomorphism followed by its
cokernel is short exact. The construction uses only sheafification, free groups,
and an abelian pushout in universe `u`, including for empty `X` and zero `G`.
(blueprint: lem-sc-zariski-torsor-free-extension-short-exact) -/
theorem shortExact :
    (ShortComplex.mk (inclusion X T) (projection X T) (inclusion_projection X T)).ShortExact := by
  have := projection_epi X T
  exact ShortComplex.ShortExact.mk' (projection_exact X T) (inclusion_mono X T) inferInstance

end FreeExtension
end CategoryTheory.Sheaf.Torsor
