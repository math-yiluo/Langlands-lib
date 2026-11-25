/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.NormalOpenLowerStar
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections

/-!
# Constructibility of direct images along open immersions

Let `Λ` be a finite commutative ring, `X` a scheme of finite type over a field and
`j : U ⟶ X` an open immersion. For a constructible sheaf `F` of `Λ`-modules on `U_ét` the
direct image `j_* F` is constructible on `X_ét`
(`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isOpenImmersion`, blueprint
`thm-fin-open-degree-zero`), and so is the boundary sheaf `i^* j_* F` on the closed complement
`i : Z ⟶ X` (`AlgebraicGeometry.Etale.isConstructibleSheaf_upperStar_lowerStar_of_isOpenImmersion`,
blueprint `lemma-extreme-degrees-affine-curve`).

The proof is a Noetherian induction on the closed subset of `X` underlying a closed subscheme.
Given `j : U ⟶ Z`, choose a nonempty open `V ⊆ U` of `Z` on which `F` is finite locally constant
and whose reduced structure is normal and integral
(`AlgebraicGeometry.Etale.exists_isConstructibleSheaf_lowerStar_opens`). With `h : V ⟶ U`, the
direct image `(j h)_* h^* F` is constructible
(`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFiniteLocallyConstantSheaf`, along
the closure of `V`). The kernel `K` of `F ⟶ h_* h^* F` vanishes on `V`, hence is pushed forward
from the closed complement `W` of `V`, and `j_* K` is constructible by induction. Finally
`0 ⟶ j_* K ⟶ j_* F ⟶ I ⟶ 0` is exact with `I ⊆ (j h)_* h^* F`, and constructible sheaves form a
Serre class.

The blueprint first reduces to a reduced `X` and treats a non-dense `U` separately; both steps are
unnecessary here: the induction runs over arbitrary closed subschemes, the reduced structure only
being used on the closure of `V` (through a thickening, along which pullback is an equivalence),
and a single open `V` is chosen in each step.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- In an abelian category, a property of objects closed under isomorphisms, subobjects and
extensions holds for the source of a morphism `φ` as soon as it holds for the kernel of `φ` and
for the target of `φ`: the source is an extension of the coimage of `φ`, a subobject of the
target, by the kernel. -/
lemma _root_.CategoryTheory.Abelian.prop_of_isLimit_kernelFork {C : Type*} [Category C]
    [Abelian C] (P : C → Prop) (hiso : ∀ {X Y : C}, (X ≅ Y) → P X → P Y)
    (hmono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], P Y → P X)
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {X Y : C} {φ : X ⟶ Y} {c : KernelFork φ} (hc : IsLimit c) (hK : P c.pt) (hY : P Y) :
    P X := by
  let S := ShortComplex.mk (kernel.ι φ) (Abelian.coimage.π φ) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι φ) }
  exact hext S hS (hiso (hc.conePointUniqueUpToIso (limit.isLimit _)) hK)
    (hmono (Abelian.factorThruCoimage φ) hY)

/-- **A normal open piece.** Let `Z` be of finite type over a field and `O` a nonempty open of `Z`
with irreducible underlying set. There is a nonempty open `V ⊆ O` such that the direct image
along `V ⟶ Z` of every finite locally constant sheaf of `Λ`-modules on `V` is constructible.

Let `ι : Z_C ⟶ Z` be the reduced closed subscheme on the closure `C` of `O`, an integral scheme.
Take `V` with `ι⁻¹ V` a nonempty normal open of `Z_C`
(`AlgebraicGeometry.Scheme.exists_nonempty_forall_isIntegrallyClosed_stalk`). Then
`Q = Z_C ×_Z V ⟶ V` is a thickening, so `L ≅ snd_* snd^* L`, and
`(V ⟶ Z)_* L ≅ ι_* fst_* snd^* L` with `fst : Q ⟶ Z_C` a normal open, to which
`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFiniteLocallyConstantSheaf`
applies. -/
theorem exists_isConstructibleSheaf_lowerStar_opens {k : Type u} [Field k] {Z : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] (O : Z.Opens)
    (hO : IsIrreducible (O : Set Z)) :
    ∃ V : Z.Opens, V ≤ O ∧ (V : Set Z).Nonempty ∧
      ∀ (L : Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsFiniteLocallyConstantSheaf L],
        IsConstructibleSheaf ((V.ι)_*[ModuleCat.{u + 1} Λ].obj L) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian aZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  have : IsNoetherian Z := {}
  -- the reduced closed subscheme `Z_C` on the closure of `O`, an integral scheme
  let C : Closeds Z := ⟨closure (O : Set Z), isClosed_closure⟩
  let I := IdealSheafData.vanishingIdeal C
  let ι := I.subschemeι
  have hι : Set.range ι.base = closure (O : Set Z) := by
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IrreducibleSpace I.subscheme := by
    have := Subtype.irreducibleSpace (hι ▸ hO.closure : IsIrreducible (Set.range ι.base))
    let e := ι.isClosedEmbedding.toIsEmbedding.toHomeomorph
    exact e.symm.surjective.irreducibleSpace e.symm.continuous
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  -- a nonempty normal open `V₁` of `Z_C` meeting `ι⁻¹ O`
  obtain ⟨V₁, hV₁, hV₁n⟩ := Scheme.exists_nonempty_forall_isIntegrallyClosed_stalk I.subscheme
    (ι ≫ aZ)
  obtain ⟨z, hz⟩ := hO.nonempty
  obtain ⟨y, hy⟩ : z ∈ Set.range ι.base := hι ▸ subset_closure hz
  have hO₁ : (ι.base ⁻¹' (O : Set Z)).Nonempty := ⟨y, by simpa [hy] using hz⟩
  obtain ⟨y₂, hy₂V, hy₂O⟩ := nonempty_preirreducible_inter V₁.isOpen
    (O.isOpen.preimage ι.continuous) hV₁ hO₁
  obtain ⟨G, hG, hGV⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.1 V₁.isOpen
  let V : Z.Opens := ⟨G, hG⟩ ⊓ O
  have hy₂G : ι.base y₂ ∈ G := by
    rw [← Set.mem_preimage, hGV]
    exact hy₂V
  refine ⟨V, inf_le_right, ⟨ι.base y₂, hy₂G, hy₂O⟩, fun L _ ↦ ?_⟩
  -- the thickening `snd : Z_C ×_Z V ⟶ V` and the normal open `fst : Z_C ×_Z V ⟶ Z_C`
  have hVC : Set.range V.ι.base ⊆ Set.range ι.base := by
    rw [Opens.range_ι, hι]
    exact fun x hx ↦ subset_closure hx.2
  let fst := pullback.fst ι V.ι
  let snd := pullback.snd ι V.ι
  have hsnd : Function.Surjective snd.base := by
    rw [← Set.range_eq_univ, Pullback.range_snd, Set.preimage_eq_univ_iff]
    exact hVC
  have hfst : Set.range fst.base ⊆ (V₁ : Set I.subscheme) := by
    rw [Pullback.range_fst, Opens.range_ι, ← hGV]
    exact fun x hx ↦ hx.1
  obtain ⟨q₀, -⟩ := hsnd ⟨ι.base y₂, hy₂G, hy₂O⟩
  have : Nonempty ↥(pullback ι V.ι) := ⟨q₀⟩
  have hQ (q : ↥(pullback ι V.ι)) :
      IsIntegrallyClosed ((pullback ι V.ι).presheaf.stalk q) :=
    have := hV₁n _ (hfst ⟨q, rfl⟩)
    .of_equiv (asIso (fst.stalkMap q)).commRingCatIsoToRingEquiv
  have : IsFiniteLocallyConstantSheaf ((snd)^*[ModuleCat.{u + 1} Λ].obj L) :=
    IsFiniteLocallyConstantSheaf.upperStar snd L
  have hD := isConstructibleSheaf_lowerStar_of_isFiniteLocallyConstantSheaf (ι ≫ aZ) fst hQ
    ((snd)^*[ModuleCat.{u + 1} Λ].obj L)
  have hE := (isConstructibleSheaf_lowerStar_of_isClosedImmersion ι
    ((fst)_*[ModuleCat.{u + 1} Λ].obj ((snd)^*[ModuleCat.{u + 1} Λ].obj L))).1
  -- `(V ⟶ Z)_* L ≅ ι_* fst_* snd^* L`
  have := isEquivalence_upperStar_of_thickening (ModuleCat.{u + 1} Λ) snd hsnd
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) snd).unit_isIso_of_L_fully_faithful
  let e : (V.ι)_*[ModuleCat.{u + 1} Λ].obj L ≅ (ι)_*[ModuleCat.{u + 1} Λ].obj
      ((fst)_*[ModuleCat.{u + 1} Λ].obj ((snd)^*[ModuleCat.{u + 1} Λ].obj L)) :=
    (V.ι)_*[ModuleCat.{u + 1} Λ].mapIso
        (asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) snd).unit.app L)) ≪≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) snd V.ι (fst ≫ ι) pullback.condition).app _ ≪≫
      ((lowerStarComp (ModuleCat.{u + 1} Λ) fst ι).app _).symm
  exact IsConstructibleSheaf.of_iso e.symm

/-- The induction behind
`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isOpenImmersion`:
Noetherian induction on the closed subset `T` of `X₀` containing the image of a closed subscheme
`Z` of `X₀`. -/
theorem isConstructibleSheaf_lowerStar_of_isOpenImmersion_aux {k : Type u} [Field k]
    {X₀ : Scheme.{u}} (a₀ : X₀ ⟶ Spec (.of k)) [LocallyOfFiniteType a₀] [QuasiCompact a₀]
    (T : Closeds X₀) :
    ∀ {Z U : Scheme.{u}} (i : Z ⟶ X₀) [IsClosedImmersion i], Set.range i.base ⊆ T →
      ∀ (j : U ⟶ Z) [IsOpenImmersion j] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsConstructibleSheaf F], IsConstructibleSheaf ((j)_*[ModuleCat.{u + 1} Λ].obj F) := by
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian a₀
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace a₀
  have : IsNoetherian X₀ := {}
  induction T using WellFoundedLT.induction with
  | _ T ih =>
  intro Z U i _ hiT j _ F _
  let aZ := i ≫ a₀
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian aZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  have : IsNoetherian Z := {}
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (j ≫ aZ)
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (j ≫ aZ)
  have : IsNoetherian U := {}
  rcases isEmpty_or_nonempty U with hU | hU
  · exact IsConstructibleSheaf.of_isZero
      (Functor.map_isZero _ (Scheme.Etale.isZero_sheaf_of_isEmpty F))
  -- a nonempty irreducible open `O₀` of `U` on which `F` is finite locally constant
  obtain ⟨U₀, hU₀d, hU₀⟩ := IsConstructibleSheaf.exists_dense_open F
  obtain ⟨c, hc, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {hU.some}
    isIrreducible_singleton
  obtain ⟨o, ho, hon, hoc⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent c hc
  obtain ⟨x, hxo, hxU₀⟩ := hU₀d.inter_open_nonempty o ho hon
  let O₀ : U.Opens := ⟨o, ho⟩ ⊓ U₀
  have hO₀ : IsIrreducible (O₀ : Set U) :=
    ⟨⟨x, hxo, hxU₀⟩, hc.1.2.open_subset O₀.isOpen (Set.inter_subset_left.trans hoc)⟩
  let O : Z.Opens := ⟨j.base '' O₀, j.isOpenMap _ O₀.isOpen⟩
  have hO : IsIrreducible (O : Set Z) := hO₀.image _ j.continuous.continuousOn
  -- a normal open `V ⊆ O` along which direct images of lisse sheaves are constructible
  obtain ⟨V, hVO, hVne, hVL⟩ := exists_isConstructibleSheaf_lowerStar_opens (Λ := Λ) aZ O hO
  have hVj : Set.range V.ι.base ⊆ Set.range j.base := by
    rw [Opens.range_ι]
    exact fun z hz ↦ (Set.image_subset_range _ _) (hVO hz)
  let h : V.toScheme ⟶ U := IsOpenImmersion.lift j V.ι hVj
  have hh : h ≫ j = V.ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (h ≫ j) := hh ▸ inferInstance
  have : IsOpenImmersion h := IsOpenImmersion.of_comp h j
  have hrange : Set.range h.base = j.base ⁻¹' V := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨⟨_, hx⟩, j.isOpenEmbedding.injective ?_⟩⟩
    · rintro ⟨v, rfl⟩
      change (h ≫ j).base v ∈ V
      rw [hh]
      exact v.2
    · change (h ≫ j).base _ = _
      rw [hh]
      rfl
  have hhU₀ : Set.range h.base ⊆ Set.range U₀.ι.base := by
    rw [hrange, Opens.range_ι]
    intro x hx
    obtain ⟨x', hx', hxx'⟩ := hVO hx
    rw [j.isOpenEmbedding.injective hxx'] at hx'
    exact hx'.2
  have : IsFiniteLocallyConstantSheaf ((h)^*[ModuleCat.{u + 1} Λ].obj F) :=
    IsFiniteLocallyConstantSheaf.upperStar_of_range_subset h U₀.ι hhU₀ F
  have hL := hVL ((h)^*[ModuleCat.{u + 1} Λ].obj F)
  -- the kernel `K` of the unit `F ⟶ h_* h^* F` vanishes on `V`
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app F
  have hK0 : IsZero ((h)^*[ModuleCat.{u + 1} Λ].obj (kernel η)) :=
    isZero_upperStar_sectionsWithSupport (ModuleCat.{u + 1} Λ) h F
  have : IsConstructibleSheaf ((𝟭 (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj F) := ‹_›
  have : IsConstructibleSheaf (kernel η) := Scheme.IsConstructibleSheaf.of_mono (kernel.ι η)
  -- the closed complement `W` of `V`, and its trace `W_U` on `U`
  let C' : Closeds Z := ⟨(V : Set Z)ᶜ, V.isOpen.isClosed_compl⟩
  let I' := IdealSheafData.vanishingIdeal C'
  let iW := I'.subschemeι
  have hiW : Set.range iW.base = (V : Set Z)ᶜ := by
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let i' := pullback.snd iW j
  let jW := pullback.fst iW j
  have hi' : Set.range i'.base = (Set.range h.base)ᶜ := by
    rw [Pullback.range_snd, hiW, hrange]
    rfl
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i').unit.app (kernel η)) :=
    isIso_upperStarLowerStarAdjunction_unit_app_of_isZero (ModuleCat.{u + 1} Λ) i' h hi' hK0
  -- `j_* K ≅ iW_* jW_* i'^* K` is constructible by induction
  let G := (i')^*[ModuleCat.{u + 1} Λ].obj (kernel η)
  have : IsConstructibleSheaf G := IsConstructibleSheaf.upperStar i' _
  let T' : Closeds X₀ := ⟨i.base '' (V : Set Z)ᶜ,
    i.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl⟩
  have hT' : T' < T := by
    refine lt_of_le_of_ne (fun x ⟨z, _, hz⟩ ↦ hiT ⟨z, hz⟩) fun hTT ↦ ?_
    obtain ⟨v, hv⟩ := hVne
    have : i.base v ∈ (T' : Set X₀) := hTT ▸ hiT ⟨v, rfl⟩
    obtain ⟨z, hz, hzv⟩ := this
    exact hz (i.isClosedEmbedding.injective hzv ▸ hv)
  have hjW := ih T' hT' (iW ≫ i) (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hiW]
    exact le_rfl) jW G
  have hiWjW := (isConstructibleSheaf_lowerStar_of_isClosedImmersion iW
    ((jW)_*[ModuleCat.{u + 1} Λ].obj G)).1
  let eK : (j)_*[ModuleCat.{u + 1} Λ].obj (kernel η) ≅
      (iW)_*[ModuleCat.{u + 1} Λ].obj ((jW)_*[ModuleCat.{u + 1} Λ].obj G) :=
    (j)_*[ModuleCat.{u + 1} Λ].mapIso (asIso
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i').unit.app (kernel η))) ≪≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) i' j (jW ≫ iW) pullback.condition).app G ≪≫
      ((lowerStarComp (ModuleCat.{u + 1} Λ) jW iW).app G).symm
  have : IsConstructibleSheaf ((j)_*[ModuleCat.{u + 1} Λ].obj (kernel η)) :=
    IsConstructibleSheaf.of_iso eK.symm
  -- the exact sequence `0 ⟶ j_* K ⟶ j_* F ⟶ I ⟶ 0` with `I ⊆ (j h)_* h^* F`
  have : IsConstructibleSheaf ((j)_*[ModuleCat.{u + 1} Λ].obj
      (((h)^*[ModuleCat.{u + 1} Λ] ⋙ (h)_*[ModuleCat.{u + 1} Λ]).obj F)) :=
    IsConstructibleSheaf.of_iso
      ((lowerStarComp (ModuleCat.{u + 1} Λ) h j V.ι hh.symm).app _).symm
  exact Abelian.prop_of_isLimit_kernelFork (fun G ↦ IsConstructibleSheaf G)
    (fun e hG ↦ by have := hG; exact IsConstructibleSheaf.of_iso e)
    (fun f _ hG ↦ by have := hG; exact Scheme.IsConstructibleSheaf.of_mono f)
    (fun S hS h₁ h₃ ↦ by have := h₁; have := h₃; exact IsConstructibleSheaf.of_shortExact hS)
    (KernelFork.mapIsLimit _ (kernelIsKernel η) (j)_*[ModuleCat.{u + 1} Λ]) ‹_› ‹_›

/-- Blueprint `thm-fin-open-degree-zero`: Constructibility of the degree-zero open direct image.

Let `X` be of finite type over a field `k`, `j : U ⟶ X` an open immersion and `F` a
constructible sheaf of modules over a finite commutative ring `Λ` on `U_ét`. Then `j_* F` is
constructible on `X_ét`. This is
`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isOpenImmersion_aux` for the closed
subscheme `X` of itself. -/
theorem isConstructibleSheaf_lowerStar_of_isOpenImmersion {k : Type u} [Field k]
    {U X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsConstructibleSheaf ((j)_*[ModuleCat.{u + 1} Λ].obj F) :=
  isConstructibleSheaf_lowerStar_of_isOpenImmersion_aux aX ⊤ (𝟙 X) (Set.subset_univ _) j F

/-- Blueprint `lemma-extreme-degrees-affine-curve`: Boundary sheaf of an open immersion.

Let `X` be of finite type over a field `k`, `j : U ⟶ X` an open immersion, `i : Z ⟶ X` a
closed immersion onto the closed complement of `U`, and `F` a constructible sheaf of
`Λ`-modules on `U_ét`. Then the boundary sheaf `i^* j_* F` is constructible on `Z_ét`: `j_* F` is
constructible (`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isOpenImmersion`), and
inverse images of constructible sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.upperStar`). The statement holds for any `i`;
the hypothesis that `i` is the closed complement of `j` only fixes the blueprint's setting. -/
theorem isConstructibleSheaf_upperStar_lowerStar_of_isOpenImmersion {k : Type u} [Field k]
    {U X Z : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsConstructibleSheaf ((i)^*[ModuleCat.{u + 1} Λ].obj ((j)_*[ModuleCat.{u + 1} Λ].obj F)) :=
  have := isConstructibleSheaf_lowerStar_of_isOpenImmersion aX j F
  IsConstructibleSheaf.upperStar i _

end Etale

end AlgebraicGeometry

end
