/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianComponents
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.StalkCardinality
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation
import WeilConjectures.AlgebraicGeometry.IrreducibleStratificationRefinement

/-!
# Constructible sheaves on Noetherian schemes

Let `Λ` be a finite commutative ring and `X` a Noetherian scheme. This file collects the
stalkwise criteria for constructible étale sheaves of `Λ`-modules on `X`:

- `AlgebraicGeometry.Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf` (blueprint
  `lem-weil-pbc-lisse-generic-kernel`): on an irreducible scheme, a morphism out of a locally
  constant sheaf which is injective on the stalk at a geometric generic point is a monomorphism.
- `AlgebraicGeometry.Etale.exists_isConstructible_sheafFiber_map_eq_zero`: a morphism into a
  constructible sheaf whose stalk at a point vanishes has vanishing stalks on a constructible
  neighbourhood of that point.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`
  (blueprint `lem-weil-pbc-irreducible-lisse-strata`): a constructible sheaf is finite locally
  constant on the strata of a stratification by irreducible strata.
- `AlgebraicGeometry.Etale.exists_finset_mono_pi_lift` (blueprint
  `lem-weil-pbc-constructible-noetherian-finite-selection`): finitely many maps out of a
  constructible sheaf jointly detect the nonzero stalk elements detected by a family of maps.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono` (blueprint
  `lem-weil-pbc-constructible-subobjects-noetherian`): subsheaves of constructible sheaves are
  constructible.
- `AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_isConstructible_card` (blueprint
  `proposition-proper-direct-image-finite-coefficients`): a sheaf with finite stalks is
  constructible if and only if the loci where its stalks have a given cardinality are constructible.

The blueprint states these for abelian étale sheaves; a constructible abelian sheaf on a
Noetherian scheme has finite stalks and finitely many strata, hence is killed by some `N`, so it
is a constructible sheaf of `ℤ/N`-modules, an instance of the present setting.

The geometric stalk at a point `x : X` is taken at the geometric point
`AlgebraicGeometry.Scheme.algClosurePoint x`, with values in an algebraic closure of the residue
field of `x`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology Opposite
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lem-weil-pbc-lisse-generic-kernel`: A generic stalk detects kernels in a locally
constant sheaf.

Let `S` be an irreducible scheme and `s` a geometric point of `S` lying over its generic point.
Let `F` be a locally constant sheaf of `Λ`-modules and `φ : F ⟶ G` a morphism of sheaves. If the
stalk of `φ` at `s` is injective, then `φ` is a monomorphism. -/
theorem Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf {S : Scheme.{u}}
    [IrreducibleSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ x, s.base x = genericPoint S)
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [IsLocallyConstantSheaf F]
    (φ : F ⟶ G) (hφ : Mono ((pointSmallEtale s).sheafFiber.map φ)) : Mono φ := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  set Φ := pointSmallEtale s
  have hinj : Function.Injective (Φ.sheafFiber.map φ) := (ModuleCat.mono_iff_injective _).1 hφ
  -- a section of `F` killed by `φ` vanishes near the points over the generic point, which are
  -- dense, hence everywhere since its vanishing locus is closed
  have key (W : S.Etale) (b : ToType (F.obj.obj (op W))) (hb : φ.hom.app (op W) b = 0) :
      b = 0 := by
    have hW : Etale W.hom := W.prop
    have hgen : {w : W.left | W.hom w = genericPoint S} ⊆ moduleVanishingLocus F b := by
      intro w hw
      obtain ⟨t, ht⟩ := pointSmallEtaleFiberObjToPreimage_surjective s (hs default) W ⟨w, hw⟩
      have htw : t.left (default : Spec (.of Ω)) = w := congrArg Subtype.val ht
      have h0 : Φ.toPresheafFiber W t F.obj b = Φ.toPresheafFiber W t F.obj 0 := by
        rw [map_zero]
        apply hinj
        rw [map_zero]
        have hnat := ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality φ.hom W t) b
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
        refine hnat.trans ?_
        rw [hb, map_zero]
      obtain ⟨W', g, y, rfl, hy⟩ := (Φ.toPresheafFiber_eq_iff' W _ _ _).1 h0
      exact ⟨W', g, y.left (default : Spec (.of Ω)), htw, by simpa using hy⟩
    have hdense : Dense {w : W.left | W.hom w = genericPoint S} := by
      refine dense_iff_inter_open.2 fun N hN ⟨w, hw⟩ ↦ ?_
      obtain ⟨v, hvN, hv⟩ := ((genericPoint_spec S).mem_open_set_iff (W.hom.isOpenMap _ hN)).2
        ⟨_, Set.mem_univ _, w, hw, rfl⟩
      exact ⟨v, hvN, hv⟩
    refine eq_zero_of_moduleVanishingLocus_eq_univ (Set.eq_univ_of_univ_subset ?_)
    rw [← hdense.closure_eq]
    exact (isClopen_moduleVanishingLocus b).isClosed.closure_subset_iff.2 hgen
  refine (Preadditive.mono_iff_cancel_zero φ).2 fun P g hg ↦ ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext
    (LinearMap.ext fun a ↦ ?_)))
  induction V using Opposite.rec with | op V => ?_
  change g.hom.app (op V) a = 0
  refine key V _ ?_
  have := congrArg (fun f ↦ f.hom.app (op V) a) hg
  simpa using this

/-- **Vanishing of a stalk map spreads to a constructible neighbourhood.** Let `T` be Noetherian,
`Q` a constructible sheaf of `Λ`-modules on `T_ét` and `χ : G ⟶ Q` a morphism of sheaves whose
stalk at the geometric point over `x` vanishes. Then the stalks of `χ` vanish on a constructible
subset containing `x`: on a dense open `U` of the closure of `x` the pullback of `Q` is locally
constant, and the pullback of `χ` to `U` vanishes since its image is a locally constant subsheaf
with vanishing generic stalk
(`AlgebraicGeometry.Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf`). -/
theorem Etale.exists_isConstructible_sheafFiber_map_eq_zero {T : Scheme.{u}} [IsNoetherian T]
    {G Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} [IsConstructibleSheaf Q]
    (χ : G ⟶ Q) (x : T) (hx : (pointSmallEtale (T.algClosurePoint x)).sheafFiber.map χ = 0) :
    ∃ E : Set T, IsConstructible E ∧ x ∈ E ∧
      ∀ y ∈ E, (pointSmallEtale (T.algClosurePoint y)).sheafFiber.map χ = 0 := by
  -- the closure of `x`, as a closed subscheme `i : Z ⟶ T`
  let I := IdealSheafData.vanishingIdeal
    (⟨closure {x}, isClosed_closure⟩ : TopologicalSpace.Closeds T)
  let i := I.subschemeι
  have hi : Set.range i.base = closure {x} := by simp [i, I, IdealSheafData.range_subschemeι]
  have := IsConstructibleSheaf.upperStar i Q
  -- `Q` is finite locally constant on a dense open `U` of `Z`
  obtain ⟨U, hU, hQU⟩ := IsConstructibleSheaf.exists_dense_open
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    ((i)^*[ModuleCat.{u + 1} Λ].obj Q)
  let k := U.ι ≫ i
  have hk : Set.range k.base ⊆ closure {x} := by
    rw [← hi, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  obtain ⟨z, hz⟩ : x ∈ Set.range i.base := hi ▸ subset_closure rfl
  have : Nonempty I.subscheme := ⟨z⟩
  have hxk : x ∈ Set.range k.base := by
    obtain ⟨v, hv⟩ := hU.nonempty
    have hzv : z ⤳ v := by
      rw [← i.isEmbedding.isInducing.specializes_iff, hz, specializes_iff_mem_closure, ← hi]
      exact ⟨v, rfl⟩
    exact ⟨⟨z, hzv.mem_open U.isOpen hv⟩, by simpa [k] using hz⟩
  -- `U` is irreducible, with generic point over `x`
  have hirr : IsIrreducible (Set.range k.base) := by
    refine isIrreducible_iff_closure.1 ?_
    rw [subset_antisymm (closure_minimal hk isClosed_closure)
      (closure_mono (Set.singleton_subset_iff.2 hxk))]
    exact isIrreducible_singleton.closure
  have : IrreducibleSpace (Set.range k.base) := Subtype.irreducibleSpace hirr
  have : IrreducibleSpace U := k.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this
  obtain ⟨t, ht⟩ := IsImmersion.exists_comp_eq_of_field k (T.algClosurePoint x)
    (by rw [algClosurePoint_base]; exact hxk)
  have htgen (p : Spec (.of (AlgebraicClosure (T.residueField x)))) :
      t.base p = genericPoint U := by
    apply k.isEmbedding.injective
    have h₁ : k.base (t.base p) = x := by
      rw [← Scheme.Hom.comp_apply, ht, algClosurePoint_base]
    rw [h₁]
    exact (Specializes.antisymm (specializes_iff_mem_closure.2 (hk ⟨_, rfl⟩))
      (h₁ ▸ (genericPoint_specializes (t.base p)).map k.continuous)).eq
  -- the pullback of `χ` to `U` vanishes
  have hx' : ((pointSmallEtale (t ≫ k)).sheafFiber (A := ModuleCat.{u + 1} Λ)).map χ = 0 := by
    rw [ht]
    exact hx
  have hχt : ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
      ((k)^*[ModuleCat.{u + 1} Λ].map χ) = 0 := by
    have h := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) k t).hom.naturality χ
    rw [Functor.comp_map, hx', comp_zero] at h
    exact (Iso.cancel_iso_hom_right _ _
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) k t).app Q)).1
      (h.trans zero_comp.symm)
  have : IsLocallyConstantSheaf ((k)^*[ModuleCat.{u + 1} Λ].obj Q) :=
    have := hQU.toIsLocallyConstantSheaf
    IsLocallyConstantSheaf.of_iso
      (F := (U.ι)^*[ModuleCat.{u + 1} Λ].obj ((i)^*[ModuleCat.{u + 1} Λ].obj Q))
      ((upperStarComp (ModuleCat.{u + 1} Λ) U.ι i).app Q).symm
  have hmono : Mono (cokernel.π ((k)^*[ModuleCat.{u + 1} Λ].map χ)) := by
    refine mono_of_mono_sheafFiber_of_isLocallyConstantSheaf t htgen _ ?_
    set P := (pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have h₁ := PreservesCokernel.π_iso_hom P ((k)^*[ModuleCat.{u + 1} Λ].map χ)
    have : IsIso (cokernel.π (P.map ((k)^*[ModuleCat.{u + 1} Λ].map χ))) :=
      cokernel.π_of_zero hχt
    rw [← h₁] at this
    have := IsIso.of_isIso_comp_right
      (P.map (cokernel.π ((k)^*[ModuleCat.{u + 1} Λ].map χ))) (PreservesCokernel.iso P _).hom
    infer_instance
  have hk0 : (k)^*[ModuleCat.{u + 1} Λ].map χ = 0 :=
    (cancel_mono (cokernel.π _)).1 (by rw [cokernel.condition, zero_comp])
  -- hence the stalks of `χ` vanish on the range of `U`
  refine ⟨Set.range k.base, k.isLocallyClosed_range.isConstructible_of_noetherianSpace, hxk, ?_⟩
  intro y hy
  obtain ⟨t', ht'⟩ := IsImmersion.exists_comp_eq_of_field k (T.algClosurePoint y)
    (by rw [algClosurePoint_base]; exact hy)
  rw [← ht']
  exact sheafFiber_map_comp_eq_zero k hk0 t'

variable [Finite Λ]

/-- Blueprint `lem-weil-pbc-irreducible-lisse-strata`: Irreducible lisse strata.

Let `X` be Noetherian and `F` a constructible sheaf of `Λ`-modules on `X_ét`. Then there is a
stratification of `X` all of whose strata are (nonempty) irreducible and on each of which `F` is
finite locally constant. -/
theorem Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible {X : Scheme.{u}}
    [IsNoetherian X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    ∃ S : Stratification X, (∀ i, IsIrreducible (S.stratum i)) ∧
      ∀ i, IsFiniteLocallyConstantSheaf ((S.immersion i)^*[ModuleCat.{u + 1} Λ].obj F) := by
  classical
  let _ := Fintype.ofFinite Λ
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := F)
  obtain ⟨T, hTS, hT⟩ := exists_irreducible_refinement_topological X S
  refine ⟨T, fun i ↦ ?_, hTS.isFiniteLocallyConstantSheaf_upperStar F hS⟩
  have := hT i
  rw [← T.range_immersion i]
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (T.domain i)).image
      (T.immersion i) (T.immersion i).continuous.continuousOn

/-- Blueprint `lem-weil-pbc-constructible-noetherian-finite-selection`: Noetherian finite
selection of stalk tests.

Let `X` be Noetherian, `F` a constructible sheaf of `Λ`-modules and `(φ_l : F ⟶ G_l)_{l ∈ L}` a
family of morphisms to arbitrary sheaves. Assume that at every point `x` of `X` every nonzero
element of the geometric stalk `F_x̄` is not killed by some `φ_l`. Then for a finite subset
`L₀ ⊆ L` the morphism `(φ_l)_{l ∈ L₀} : F ⟶ ∏_{l ∈ L₀} G_l` is a monomorphism. -/
theorem Etale.exists_finset_mono_pi_lift {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    {L : Type*} (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (φ : ∀ l, F ⟶ G l)
    (h : ∀ (x : X) (v : (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F), v ≠ 0 →
      ∃ l, ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.map (φ l)).hom v ≠ 0) :
    ∃ L₀ : Finset L, Mono (Pi.lift fun l : L₀ ↦ φ l) := by
  classical
  obtain ⟨S, hI, hS⟩ := IsConstructibleSheaf.exists_stratification_isIrreducible F
  have hirr (i : Fin S.n) : IrreducibleSpace (S.domain i) := by
    have : IrreducibleSpace (Set.range (S.immersion i)) :=
      Subtype.irreducibleSpace ((S.range_immersion i).symm ▸ hI i)
    exact (S.immersion i).isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  let η (i : Fin S.n) := genericPoint (S.domain i)
  let x (i : Fin S.n) := S.immersion i (η i)
  let P (z : X) := (pointSmallEtale (X.algClosurePoint z)).sheafFiber
    (A := ModuleCat.{u + 1} Λ)
  let V (i : Fin S.n) := (P (x i)).obj F
  have : IsFiniteSheaf F := (inferInstance : IsConstructibleSheaf F).isFiniteSheaf
  have hfin (i : Fin S.n) : Finite (V i) := by
    have := (ModuleCat.isFinitelyGenerated_iff _).mp
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) _ (X.algClosurePoint (x i)))
    exact Module.finite_of_finite Λ
  -- Only the finite generic stalks are needed to choose the indices.
  let K := (i : Fin S.n) × {v : V i // v ≠ 0}
  have hdetect : ∀ k : K, ∃ l, ((P (x k.1)).map (φ l)).hom k.2.val ≠ 0 :=
    fun k ↦ h (x k.1) k.2.val k.2.property
  choose index hindex using hdetect
  let : Fintype K := Fintype.ofFinite K
  let L₀ := Finset.univ.image index
  let f := Pi.lift fun l : L₀ ↦ φ l
  have htest (i : Fin S.n) : Mono
      ((P (x i)).map f) := by
    apply (ModuleCat.mono_iff_injective _).2
    apply (injective_iff_map_eq_zero _).2
    intro v hv
    by_contra hne
    let k : K := ⟨i, ⟨v, hne⟩⟩
    let l : L₀ := ⟨index k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
    apply hindex k
    change ((P (x i)).map (φ l)).hom v = 0
    rw [← Pi.lift_comp_π (fun l : L₀ ↦ φ l) l, Functor.map_comp,
      ConcreteCategory.comp_apply, hv]
    simp
  -- The generic-stalk criterion propagates injectivity over each irreducible stratum.
  have hmono (i : Fin S.n) : Mono ((S.immersion i)^*[ModuleCat.{u + 1} Λ].map f) := by
    obtain ⟨s, hs⟩ := exists_comp_eq_of_mem_range (S.immersion i)
      (X.algClosurePoint (x i)) (by simp [x])
    have hsη (p) : s.base p = η i := by
      apply (S.immersion i).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hs, algClosurePoint_base]
    have := hS i
    have := htest i
    have htest' : Mono (((pointSmallEtale (s ≫ S.immersion i)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map f) := by
      rw [hs]
      infer_instance
    let e := upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (S.immersion i) s
    have hc : Mono ((e.app F).hom ≫
        ((pointSmallEtale (s ≫ S.immersion i)).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map f) := inferInstance
    rw [Iso.app_hom, ← e.hom.naturality f] at hc
    have hg : Mono (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
        ((S.immersion i)^*[ModuleCat.{u + 1} Λ].map f)) :=
      @mono_of_mono _ _ _ _ _ _ (e.hom.app _) hc
    exact mono_of_mono_sheafFiber_of_isLocallyConstantSheaf s hsη _ hg
  -- Every geometric point lifts to a stratum, so stalkwise cancellation is global.
  refine ⟨L₀, ⟨fun {H} a b hab ↦ ?_⟩⟩
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ z)
  rw [← S.range_immersion i] at hi
  obtain ⟨t, ht⟩ := exists_comp_eq_of_mem_range (S.immersion i) (X.algClosurePoint z)
    (by simpa using hi)
  have := hmono i
  let e := upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (S.immersion i) t
  have hm' : Mono (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
      ((S.immersion i)^*[ModuleCat.{u + 1} Λ].map f)) := inferInstance
  have : Mono (((S.immersion i)^*[ModuleCat.{u + 1} Λ] ⋙
      (pointSmallEtale t).sheafFiber).map f) := hm'
  have hc : Mono ((e.app F).inv ≫ ((S.immersion i)^*[ModuleCat.{u + 1} Λ] ⋙
      (pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map f) := inferInstance
  rw [Iso.app_inv, ← e.inv.naturality f] at hc
  have hm : Mono (((pointSmallEtale (t ≫ S.immersion i)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map f) :=
    @mono_of_mono _ _ _ _ _ _ (e.inv.app _) hc
  rw [ht] at hm
  apply (cancel_mono ((P z).map f)).1
  change (P z).map a ≫ (P z).map f = (P z).map b ≫ (P z).map f
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (P z).map hab

/-- Blueprint `lem-weil-pbc-constructible-subobjects-noetherian`: Subsheaves of a constructible
sheaf on a Noetherian scheme.

Let `T` be Noetherian. Every subsheaf of a constructible sheaf of `Λ`-modules on `T_ét` is
constructible. -/
theorem Scheme.IsConstructibleSheaf.of_mono {T : Scheme.{u}} [IsNoetherian T]
    {G F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ι : G ⟶ F) [Mono ι]
    [IsConstructibleSheaf F] : IsConstructibleSheaf G := by
  classical
  -- `G` is a quotient of a sum of constructible sheaves `v_! Λ`
  let H : Etale.SectionIndex G → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun i ↦ Etale.lowerShriekUnit (Λ := Λ) i.1.1.hom i.1.1.prop
  have hH (i : Etale.SectionIndex G) : IsConstructibleSheaf (H i) :=
    have : IsAffine ((𝟭 Scheme).obj i.1.1.left) := i.1.2
    have : Etale i.1.1.hom := i.1.1.prop
    isConstructibleSheaf_lowerShriekUnit_of_isAffine_source (X := T) i.1.1.hom
  have := Etale.epi_sigmaDesc_sectionHom G
  let φ := fun i : Etale.SectionIndex G ↦ Etale.sectionHom G i.1.1.hom i.1.1.prop i.2
  let d (S : Finset (Etale.SectionIndex G)) := finsetSigmaDesc H φ S
  have hSig (S : Finset (Etale.SectionIndex G)) : IsConstructibleSheaf (∐ fun i : S ↦ H i.1) :=
    isConstructibleSheaf_finsetSigma H S
  have hQ (S : Finset (Etale.SectionIndex G)) :
      IsConstructibleSheaf (Limits.cokernel (d S ≫ ι)) :=
    have := hSig S
    IsConstructibleSheaf.cokernel _
  -- the subsum indexed by `S` is surjective on a stalk iff `χ S : G ⟶ coker (d S ≫ ι)`
  -- vanishes there
  let χ (S : Finset (Etale.SectionIndex G)) := ι ≫ Limits.cokernel.π (d S ≫ ι)
  have hχ (S : Finset (Etale.SectionIndex G)) (x : T) :
      (pointSmallEtale (T.algClosurePoint x)).sheafFiber.map (χ S) = 0 ↔
        Function.Surjective ((pointSmallEtale (T.algClosurePoint x)).sheafFiber.map (d S)) := by
    set P := (pointSmallEtale (T.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have : P.Additive := (pointSmallEtale (T.algClosurePoint x)).sheafFiber_additive
    constructor
    · intro h v
      have hinj : Function.Injective (P.map ι) := (ModuleCat.mono_iff_injective _).1 inferInstance
      have h' : P.map ι ≫
          ModuleCat.ofHom (LinearMap.range (P.map (d S ≫ ι)).hom).mkQ = 0 := by
        rw [← ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom,
          ← PreservesCokernel.π_iso_hom P]
        simp only [Category.assoc]
        rw [← P.map_comp_assoc]
        change P.map (χ S) ≫ _ = 0
        rw [h, zero_comp]
      have hv := ConcreteCategory.congr_hom h' v
      simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, Submodule.mkQ_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at hv
      obtain ⟨w, hw⟩ := hv
      refine ⟨w, hinj ?_⟩
      rw [← ConcreteCategory.comp_apply, ← P.map_comp]
      exact hw
    · intro hs
      have : Epi (P.map (d S)) := (ModuleCat.epi_iff_surjective _).2 hs
      rw [← cancel_epi (P.map (d S)), ← P.map_comp, comp_zero]
      change P.map (d S ≫ ι ≫ Limits.cokernel.π (d S ≫ ι)) = 0
      rw [← Category.assoc, Limits.cokernel.condition, P.map_zero]
  -- the stalks of `G` are finite
  have hfin (x : T) : Module.Finite Λ
      (((pointSmallEtale (T.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) := by
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      ((inferInstance : IsConstructibleSheaf F).isFiniteSheaf.isFinitelyGenerated_sheafFiber _
        (T.algClosurePoint x))
    exact Module.Finite.of_injective
      ((pointSmallEtale (T.algClosurePoint x)).sheafFiber.map ι).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  -- near every point some finite subsum is surjective on stalks
  have hpt (x : T) : ∃ S : Finset (Etale.SectionIndex G), ∃ E : Set T, IsConstructible E ∧
      x ∈ E ∧ ∀ y ∈ E,
        Function.Surjective ((pointSmallEtale (T.algClosurePoint y)).sheafFiber.map (d S)) := by
    obtain ⟨S, hS⟩ :=
      exists_finset_surjective_sheafFiber_map H φ (T.algClosurePoint x) (hfin x)
    have := hQ S
    obtain ⟨E, hE, hxE, hEχ⟩ :=
      Etale.exists_isConstructible_sheafFiber_map_eq_zero (χ S) x ((hχ S x).2 hS)
    exact ⟨S, E, hE, hxE, fun y hy ↦ (hχ S y).1 (hEχ y hy)⟩
  choose S E hE hxE hES using hpt
  have hcov : (Set.univ : Set T) ⊆ ⋃ x, E x := fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxE x⟩
  obtain ⟨T₀, hT₀⟩ :=
    (isCompact_univ (X := WithConstructibleTopology T)).elim_finite_subcover
    (fun x ↦ WithTopology.ofTopology ⁻¹' E x)
    (fun x ↦ by
      rw [WithConstructibleTopology.isOpen_iff]
      exact (hE x).isClopen_constructibleTopology.2)
    (fun w _ ↦ by simpa using hcov (Set.mem_univ (WithTopology.ofTopology w)))
  have hT (y : T) : y ∈ ⋃ x ∈ T₀, E x := by
    simpa using hT₀ (Set.mem_univ (WithTopology.toTopology _ y))
  -- the subsum indexed by `T₀.sup S` is an epimorphism
  have hall (y : T) : IsZero ((pointSmallEtale (T.algClosurePoint y)).sheafFiber.obj
      (Limits.cokernel (d (T₀.sup S)))) := by
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hT y)
    rw [isZero_sheafFiber_cokernel_iff]
    intro m
    obtain ⟨w, hw⟩ := hES x y hy m
    exact range_sheafFiber_map_finsetSigmaDesc_mono H φ _ (Finset.le_sup (f := S) hx) ⟨w, hw⟩
  have : IsIso (0 : Limits.cokernel (d (T₀.sup S)) ⟶ _) :=
    isIso_of_isIso_sheafFiber_map _ fun x ↦ by
      have hx : IsZero ((T.uliftPointSmallEtale x).sheafFiber.obj
          (Limits.cokernel (d (T₀.sup S)))) :=
        (hall x).of_iso (((pointSmallEtale (T.algClosurePoint x)).uliftSheafFiberIso _).app _)
      exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  have : Epi (d (T₀.sup S)) := Preadditive.epi_of_isZero_cokernel _ (by
    rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : Limits.cokernel (d (T₀.sup S)) ⟶
      Limits.cokernel (d (T₀.sup S))), zero_comp])
  -- its coimage is constructible
  have := hSig (T₀.sup S)
  have := IsConstructibleSheaf.kernel (d (T₀.sup S) ≫ ι)
  have : IsConstructibleSheaf (Limits.kernel (d (T₀.sup S))) :=
    IsConstructibleSheaf.of_iso (kernelCompMono (d (T₀.sup S)) ι)
  have : IsConstructibleSheaf (Abelian.coimage (d (T₀.sup S))) :=
    IsConstructibleSheaf.cokernel (Limits.kernel.ι (d (T₀.sup S)))
  exact IsConstructibleSheaf.of_iso (asIso (Abelian.factorThruCoimage (d (T₀.sup S))))

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Constructibility from the
cardinalities of finite stalks.

Let `X` be Noetherian and `F` a sheaf of `Λ`-modules on `X_ét` with finite geometric stalks. For
`n ≥ 1` let `C_n` be the set of points `x` with `|F_x̄| = n`. Then `F` is constructible if and
only if every `C_n` is a constructible subset of `X`. -/
theorem Scheme.isConstructibleSheaf_iff_isConstructible_card {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteSheaf F] :
    IsConstructibleSheaf F ↔ ∀ n : ℕ, 1 ≤ n →
      IsConstructible {x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj F) = n} := by
  refine ⟨fun _ n _ ↦ IsConstructibleSheaf.isConstructible_setOf_natCard F n, fun hC ↦ ?_⟩
  classical
  -- `F` is a quotient of a sum of constructible sheaves `v_! Λ`
  let G : Etale.SectionIndex F → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun i ↦ Etale.lowerShriekUnit (Λ := Λ) i.1.1.hom i.1.1.prop
  have hG (i : Etale.SectionIndex F) : IsConstructibleSheaf (G i) :=
    have : IsAffine ((𝟭 Scheme).obj i.1.1.left) := i.1.2
    have : Etale i.1.1.hom := i.1.1.prop
    isConstructibleSheaf_lowerShriekUnit_of_isAffine_source (X := X) i.1.1.hom
  have := Etale.epi_sigmaDesc_sectionHom F
  let φ := fun i : Etale.SectionIndex F ↦ Etale.sectionHom F i.1.1.hom i.1.1.prop i.2
  let d (S : Finset (Etale.SectionIndex F)) := finsetSigmaDesc G φ S
  -- the images of the finite subsums are constructible
  have hI (S : Finset (Etale.SectionIndex F)) : IsConstructibleSheaf (Abelian.coimage (d S)) := by
    have := isConstructibleSheaf_finsetSigma G S
    have := IsConstructibleSheaf.of_mono (kernel.ι (d S))
    exact IsConstructibleSheaf.cokernel _
  have hfin (x : X) : Finite ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F) :=
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) _ (X.algClosurePoint x))
    Module.finite_of_finite Λ
  -- the locus where the subsum indexed by `S` is surjective on stalks
  let E (S : Finset (Etale.SectionIndex F)) : Set X :=
    ⋃ n : ℕ, ({x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj (Abelian.coimage (d S))) = n + 1} ∩
      {x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj F) = n + 1})
  have hE (S : Finset (Etale.SectionIndex F)) (x : X) : x ∈ E S ↔
      Function.Surjective ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.map (d S)) := by
    have := hfin x
    rw [surjective_sheafFiber_map_iff_natCard_coimage]
    simp only [E, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨fun ⟨n, h₁, h₂⟩ ↦ h₁.trans h₂.symm, fun h ↦ ?_⟩
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.card_pos (α := 
      ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj F))).ne'
    exact ⟨n, h.trans hn, hn⟩
  have hcov : (Set.univ : Set X) ⊆ ⋃ S, E S := by
    intro x _
    obtain ⟨S, hS⟩ := exists_finset_surjective_sheafFiber_map G φ (X.algClosurePoint x)
      ((ModuleCat.isFinitelyGenerated_iff _).1
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) _ _))
    exact Set.mem_iUnion.mpr ⟨S, (hE S x).2 hS⟩
  obtain ⟨T, hT₀⟩ := (isCompact_univ (X := WithConstructibleTopology X)).elim_finite_subcover
    (fun S ↦ WithTopology.ofTopology ⁻¹' E S)
    (fun S ↦ by
      rw [WithConstructibleTopology.isOpen_iff]
      refine @isOpen_iUnion X _ (constructibleTopology X) _ fun n ↦ ?_
      exact @IsOpen.inter X (constructibleTopology X) _ _
        (IsConstructibleSheaf.isConstructible_setOf_natCard _ _).isClopen_constructibleTopology.2
        (hC _ (Nat.le_add_left 1 n)).isClopen_constructibleTopology.2)
    (fun w _ ↦ by simpa using hcov (Set.mem_univ (WithTopology.ofTopology w)))
  have hT (x : X) : x ∈ ⋃ S ∈ T, E S := by
    simpa using hT₀ (Set.mem_univ (WithTopology.toTopology _ x))
  -- the subsum indexed by `T.sup id` is an epimorphism
  have hall (x : X) : IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
      (cokernel (d (T.sup id)))) := by
    obtain ⟨S, hST, hx⟩ := Set.mem_iUnion₂.mp (hT x)
    rw [isZero_sheafFiber_cokernel_iff]
    intro m
    obtain ⟨y, hy⟩ := (hE S x).1 hx m
    exact range_sheafFiber_map_finsetSigmaDesc_mono G φ _ (Finset.le_sup (f := id) hST) ⟨y, hy⟩
  have : IsIso (0 : cokernel (d (T.sup id)) ⟶ _) :=
    isIso_of_isIso_sheafFiber_map _ fun x ↦ by
      have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj (cokernel (d (T.sup id)))) :=
        (hall x).of_iso (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app _)
      exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  have : Epi (d (T.sup id)) := Preadditive.epi_of_isZero_cokernel _ (by
    rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : cokernel (d (T.sup id)) ⟶
      cokernel (d (T.sup id))), zero_comp])
  have := hI (T.sup id)
  exact IsConstructibleSheaf.of_iso (asIso (Abelian.factorThruCoimage (d (T.sup id))))

end AlgebraicGeometry

end
