/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.CoherentHomsOverOpen
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! Generic coherent ideal lattices. Source: Stacks Project, Tag 01YE. -/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private theorem hom_zero_of_affine {X : Scheme.{w}} {M N : X.Modules}
    (φ : M ⟶ N) (h : ∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = 0) :
    φ = 0 := by
  apply hom_ext
  intro W
  ext s
  change φ.app W s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    rw [← Hom.app_presheaf_map, map_zero]
    exact h i.1 _

/-- Factor an inclusion through a monomorphism by vanishing of its cokernel projection.
This is the affine-range comparison used in the ideal-power calculation below. -/
private theorem subobject_le_of_affine_range {X : Scheme.{w}} {M N P : X.Modules}
    (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j]
    (h : ∀ V : X.affineOpens, Set.range (i.app V.1) ⊆ Set.range (j.app V.1)) :
    Subobject.mk i ≤ Subobject.mk j := by
  have hz : i ≫ cokernel.π j = 0 := by
    apply hom_zero_of_affine
    intro V s
    obtain ⟨t, ht⟩ := h V ⟨s, rfl⟩
    change (cokernel.π j).app V.1 (i.app V.1 s) = 0
    rw [← ht]
    exact congrArg (fun q ↦ q.app V.1 t) (cokernel.condition j)
  let k : M ⟶ Abelian.image j := kernel.lift (cokernel.π j) i hz
  let l : M ⟶ N := k ≫ inv (Abelian.factorThruImage j)
  apply Subobject.mk_le_mk_of_comm l
  change k ≫ inv (Abelian.factorThruImage j) ≫ j = i
  calc
    k ≫ inv (Abelian.factorThruImage j) ≫ j =
        k ≫ inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
      congrArg (fun q ↦ k ≫ inv (Abelian.factorThruImage j) ≫ q)
        (Abelian.image.fac j).symm
    _ = k ≫ Abelian.image.ι j := by rw [IsIso.inv_hom_id_assoc]
    _ = i := kernel.lift_ι _ _ hz

set_option backward.isDefEq.respectTransparency false in
private theorem power_inclusion_mono {X : Scheme.{w}} (J : X.IdealSheafData) (n : ℕ) :
    Mono (Scheme.idealSheafPower J.toModulesι n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => dsimp [Scheme.idealSheafPower]; infer_instance
  | one => dsimp [Scheme.idealSheafPower]; infer_instance
  | more n _ ih =>
    change Mono (Scheme.idealModuleProductι J.toModulesι
      (Scheme.idealSheafPower J.toModulesι (n + 1)).1 ≫
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2)
    have := ih
    have : Mono (Scheme.idealModuleProductι J.toModulesι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).1) := by
      dsimp [Scheme.idealModuleProductι]; infer_instance
    infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem power_inclusion_iso {X : Scheme.{w}} (J : X.IdealSheafData)
    (n : ℕ) :
    ∃ e : (Scheme.idealSheafPower J.toModulesι n).1 ≅ (J ^ n).toModules,
      e.hom ≫ (J ^ n).toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
  have := power_inclusion_mono J n
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hr (U : X.affineOpens) :
      Set.range ((Scheme.idealSheafPower J.toModulesι n).2.app U.1) =
        Set.range ((J ^ n).toModulesι.app U.1) := by
    rw [(J ^ n).range_toModulesι_app]
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    cases n with
    | zero => simp [Scheme.idealSheafPower]
    | succ n =>
      ext a
      exact Set.ext_iff.mp
        (((ideal_times_quasiCoherent_affine_sections J
          (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 U).2.2.2 (n + 1)
          (Nat.zero_lt_succ n)) a
  have he : Subobject.mk (Scheme.idealSheafPower J.toModulesι n).2 =
      Subobject.mk (J ^ n).toModulesι := le_antisymm
    (subobject_le_of_affine_range _ _ (fun U ↦ (hr U).subset))
    (subobject_le_of_affine_range _ _ (fun U ↦ (hr U).symm.subset))
  exact ⟨Subobject.isoOfMkEqMk _ _ he, by simp⟩

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem product_free_iso (Z : Scheme.{w}) {K : Z.Modules}
    (i : K ⟶ SheafOfModules.unit Z.ringCatSheaf) [Mono i] (r : ℕ) :
    Nonempty ((∐ fun _ : ULift.{w} (Fin r) ↦ K) ≅
      idealModuleProduct i
        (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r)))) := by
  let : MonoidalCategory Z.Modules := SheafOfModules.monoidalCategory Z.sheaf
  let : HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let E : Z.Modules := SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))
  let F := tensorLeft K
  have : PreservesColimitsOfSize.{w, w} F :=
    (SheafOfModules.tensorHomAdjunction Z.sheaf K).leftAdjoint_preservesColimits
  let c : (∐ fun _ : ULift.{w} (Fin r) ↦ K) ≅ K ⊗ E :=
    Sigma.mapIso (fun _ ↦ (ρ_ K).symm) ≪≫
      (PreservesCoproduct.iso F (fun _ : ULift.{w} (Fin r) ↦ O)).symm
  let μ : K ⊗ E ⟶ E := i ▷ E ≫ (λ_ E).hom
  have hc : c.hom ≫ μ = Limits.Sigma.map (fun _ : ULift.{w} (Fin r) ↦ i) := by
    apply Sigma.hom_ext
    intro j
    dsimp [c, μ, F]
    simp only [Category.assoc, Sigma.ι_mapIso_hom_assoc, Sigma.ι_map]
    change (ρ_ K).inv ≫
      Sigma.ι (fun _ : ULift.{w} (Fin r) ↦ (tensorLeft K).obj O) j ≫
      sigmaComparison (tensorLeft K) (fun _ : ULift.{w} (Fin r) ↦ O) ≫
      i ▷ E ≫ (λ_ E).hom = i ≫ Sigma.ι (fun _ : ULift.{w} (Fin r) ↦ O) j
    rw [ι_comp_sigmaComparison_assoc]
    change (ρ_ K).inv ≫ K ◁ Sigma.ι (fun _ : ULift.{w} (Fin r) ↦ O) j ≫
      i ▷ E ≫ (λ_ E).hom = i ≫ Sigma.ι (fun _ : ULift.{w} (Fin r) ↦ O) j
    erw [whisker_exchange_assoc, leftUnitor_naturality]
    erw [← Category.assoc, ← rightUnitor_inv_naturality]
    rw [unitors_equal]
    change (i ≫ (ρ_ O).inv) ≫ (ρ_ O).hom ≫
      Sigma.ι (fun _ : ULift.{w} (Fin r) ↦ O) j = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have : Mono (Limits.Sigma.map (fun _ : ULift.{w} (Fin r) ↦ i)) := inferInstance
  have : Mono μ := by
    have : Mono (c.hom ≫ μ) := by rw [hc]; infer_instance
    have he : μ = c.inv ≫ (c.hom ≫ μ) := by simp
    rw [he]
    infer_instance
  exact ⟨c ≪≫ (imageMonoIsoSource μ).symm⟩

/-- An ideal power times a finite free module is a sum of copies of the power ideal.

Source: Stacks Project, Tag 01YE, integral-case paragraph (the map from a sum of
copies of a power ideal), the coordinate identity in its final paragraph.
Proof: Construct the power ideal as the actual ideal-sheaf product `J ^ n`, whose
sections on every affine W are `J(W) ^ n`. For n = 0 this is the unit ideal. The
recursive module power has these same affine section ranges by the affine product
formula, and hence is isomorphic, compatibly with its inclusion, to `(J ^ n).toModules`.
Multiplication into the free module acts separately on each standard coordinate.
Its image is therefore the direct sum of r copies of that power ideal on every affine
open. These coordinate identifications commute with restriction and localization;
sheaf gluing gives the displayed isomorphism. When r = 0 both modules
are zero and the same coordinate construction is the unique isomorphism. -/
private theorem ideal_power_finite_free_lattice (Z : Scheme.{w})
    (J : Z.IdealSheafData) (n r : ℕ) :
    Nonempty ((∐ fun _ : Fin r ↦ (J ^ n).toModules) ≅
        idealModuleProduct (idealSheafPower J.toModulesι n).2
          (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r)))) := by
  obtain ⟨e, he⟩ := power_inclusion_iso J n
  have := power_inclusion_mono J n
  obtain ⟨a⟩ := product_free_iso Z (idealSheafPower J.toModulesι n).2 r
  let b : (∐ fun _ : ULift.{w} (Fin r) ↦ (J ^ n).toModules) ≅
      (∐ fun _ : Fin r ↦ (J ^ n).toModules) :=
    Sigma.reindex Equiv.ulift (fun _ : Fin r ↦ (J ^ n).toModules)
  exact ⟨b.symm ≪≫ Sigma.mapIso (fun _ ↦ e.symm) ≪≫ a⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finite_free_coherent (Z : Scheme.{w}) [IsLocallyNoetherian Z] (r : ℕ) :
    RingedSpace.IsCoherent Z.toRingedSpace
      (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))) := by
  let E : Z.Modules := SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))
  let g := SheafOfModules.GeneratingSections.ofEpiFree (𝟙 E)
  have : g.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{w} (Fin r)))⟩
  let q := g.localGeneratorsData
  have : q.IsFiniteType := by
    constructor
    intro j
    constructor
    exact inferInstanceAs (Finite g.I)
  have : E.IsFiniteType := by
    constructor
    exact ⟨q, inferInstance⟩
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType Z E).mpr
    ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_stalk_of_restrict {Z : Scheme.{w}} {M N : Z.Modules}
    (f : M ⟶ N) (U : Z.Opens) (x : Z) (hx : x ∈ U)
    (h : IsIso ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
      (⟨x, hx⟩ : U.toScheme)).map ((restrictFunctor U.ι).map f))) :
    IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace x).map f) := by
  let y : U.toScheme := ⟨x, hx⟩
  let A := restrictFunctor U.ι ⋙ toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{w} y
  let B := toPresheaf Z ⋙ TopCat.Presheaf.stalkFunctor Ab.{w} (U.ι y)
  let e := restrictStalkNatIso U.ι y
  have hbij := ConcreteCategory.bijective_of_isIso
    ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y).map
      ((restrictFunctor U.ι).map f))
  have : IsIso (A.map f) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have he : B.map f = e.inv.app M ≫ A.map f ≫ e.hom.app N := by
    rw [e.hom.naturality f]
    simp
    rfl
  have : IsIso (B.map f) := by rw [he]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (ConcreteCategory.bijective_of_isIso (B.map f))

set_option backward.isDefEq.respectTransparency false in
private theorem ideal_coherent (Z : Scheme.{w}) [IsLocallyNoetherian Z]
    (I : Z.IdealSheafData) : RingedSpace.IsCoherent Z.toRingedSpace I.toModules := by
  have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := Z.ringCatSheaf)
  have : ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isClosedImmersion I.subschemeι _
  have hqc := isQuasicoherent_kernel I.toPushforwardSubscheme
  let g := SheafOfModules.GeneratingSections.ofEpiFree
    (SheafOfModules.freeUniqueIso (R := Z.ringCatSheaf) PUnit.{w + 1}).hom
  have : g.IsFiniteType := ⟨inferInstanceAs (Finite PUnit.{w + 1})⟩
  let q := g.localGeneratorsData
  have : q.IsFiniteType := by
    constructor
    intro j
    constructor
    exact inferInstanceAs (Finite g.I)
  have ht : (SheafOfModules.unit Z.ringCatSheaf).IsFiniteType := by
    constructor
    exact ⟨q, inferInstance⟩
  have hu := (isCoherent_iff_isQuasicoherent_and_isFiniteType Z
    (SheafOfModules.unit Z.ringCatSheaf)).mpr ⟨inferInstance, ht⟩
  exact ((isCoherent_kernel_cokernel_biprod_and_submodule Z).2 _ _
    I.toModulesι hu inferInstance hqc).1

/-- A finite free map defined near the generic point extends from an ideal-sum lattice.

Source: Stacks Project, Tag 01YE, extension over a power of the complement ideal.
Proof: let J be the vanishing ideal of the closed subset Z ∖ U, with its
reduced induced closed subscheme structure. Its affine radical-ideal description
and the affine ideal-zero-set criterion show that J_x → O_{Z,x} is surjective
exactly for x ∈ U. Thus the open supplied by coherent_homs_over_open for J is U.
Let E be the finite free source. It is coherent by the locally Noetherian criterion;
G is quasi-coherent by that criterion and hG. Identify restriction to the open scheme
with restriction to the slice site, and apply the final surjectivity clause of
coherent_homs_over_open to the given φ. Obtain n and a map J^n E → G whose restriction
agrees with φ after the canonical inclusion J^n E → E.
Construct I as the ideal sheaf with affine sections J(W)^n (the unit ideal if n = 0).
The affine-sections formula for ideal products identifies J^n E with the finite sum
of copies of I: in each coordinate multiplication has image J(W)^n, and these
identifications commute with localization and glue on overlaps. Use this isomorphism
to turn the extension into χ. The power ideal is quasi-coherent by the ideal-products
lemma, and its inclusion into the coherent structure module is a monomorphism, so
the quasi-coherent-submodule clause gives its coherence. On U its inclusion is an
isomorphism, as is the inclusion J^n E → E. Take the stalk of the extension identity
at ξ ∈ U and conjugate by the restriction-stalk isomorphisms. It expresses χ_ξ as
φ_ξ composed with isomorphisms, so χ_ξ is invertible. For n = 0 this is the unit
ideal and for r = 0 all coordinate statements are empty; the argument still applies.
(blueprint: lem-weil-pbc-coherent-integral-generic-lattice-extension)
-/
theorem exists_generic_ideal_extension (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules)
    (hG : RingedSpace.IsCoherent Z.toRingedSpace G)
    (r : ℕ) (U : Z.Opens) (hx : genericPoint Z ∈ U)
    (φ : (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))) ⟶
      (restrictFunctor U.ι).obj G)
    (hφ : IsIso ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
      (⟨genericPoint Z, hx⟩ : U.toScheme)).map φ)) :
    ∃ (I : Z.IdealSheafData),
      RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      ∃ (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G),
        IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace
          (genericPoint Z)).map χ) := by
  classical
  let E : Z.Modules := SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))
  let T : TopologicalSpace.Closeds Z := ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩
  let J := IdealSheafData.vanishingIdeal T
  have : G.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType Z G).mp hG).1
  obtain ⟨V, ρ, hV, _, hIso, _, _, hExt⟩ :=
    coherent_homs_over_open J G E (finite_free_coherent Z r)
  have hVU : V = U := by
    apply TopologicalSpace.Opens.ext
    ext x
    change (x ∈ V) ↔ (x ∈ U)
    have hrange := (IdealSheafData.reduced_induced_closed_subscheme Z T).2.2.2.2.2.1
    have hz := (quasi_coherent_ideal_zero_set_affine Z J).2.2.2.2 J.subscheme
      J.subschemeι (IdealSheafData.ker_subschemeι J)
    have hnot : (¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor Z.toRingedSpace x).map J.toModulesι).hom) ↔
        x ∉ U := by
      have he := Set.ext_iff.mp (hrange.symm.trans hz) x
      exact he.symm
    exact (hV x).trans (by simpa only [not_not] using not_congr hnot)
  subst V
  let H := SheafOfModules.overFunctor Z.ringCatSheaf U
  let K := (overEquiv (X := Z) U).functor
  let e := overFunctorEquiv (X := Z) U
  let ψ : H.obj E ⟶ H.obj G := K.preimage (e.hom.app E ≫ φ ≫ e.inv.app G)
  obtain ⟨n, χ, hχ⟩ := hExt ψ
  let P := idealModuleProduct (idealSheafPower J.toModulesι n).2 E
  let i : P ⟶ E := idealModuleProductι (idealSheafPower J.toModulesι n).2 E
  have hψ : K.map ψ = e.hom.app E ≫ φ ≫ e.inv.app G := K.map_preimage _
  have hr : (restrictFunctor U.ι).map i ≫ φ = (restrictFunctor U.ι).map χ := by
    have hh := congrArg (fun f ↦ K.map f) hχ
    rw [Functor.map_comp, hψ] at hh
    have hi := e.hom.naturality i
    have hc := e.hom.naturality χ
    dsimp only [Functor.comp_map] at hi hc
    apply (cancel_mono (e.inv.app G)).mp
    apply (cancel_epi (e.hom.app P)).mp
    have hi' := congrArg (fun f ↦ f ≫ φ ≫ e.inv.app G) hi
    have hc' := congrArg (fun f ↦ f ≫ e.inv.app G) hc
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hc'
    calc
      e.hom.app P ≫ (restrictFunctor U.ι).map i ≫ φ ≫ e.inv.app G =
          K.map (H.map i) ≫ e.hom.app E ≫ φ ≫ e.inv.app G := by
        simpa only [Category.assoc] using hi'.symm
      _ = K.map (H.map χ) := hh
      _ = e.hom.app P ≫ (restrictFunctor U.ι).map χ ≫ e.inv.app G := hc'
  have : IsIso (H.map i) := hIso n
  have : IsIso ((restrictFunctor U.ι).map i) := by
    have he : (restrictFunctor U.ι).map i = e.inv.app P ≫ K.map (H.map i) ≫
        e.hom.app E := by
      have hi := congrArg (fun f ↦ e.inv.app P ≫ f) (e.hom.naturality i)
      simpa only [Functor.comp_map, Category.assoc, Iso.inv_hom_id_app_assoc] using hi.symm
    rw [he]
    infer_instance
  have : IsIso ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
      (⟨genericPoint Z, hx⟩ : U.toScheme)).map ((restrictFunctor U.ι).map χ)) := by
    rw [← hr, Functor.map_comp]
    infer_instance
  have hχiso := isIso_stalk_of_restrict χ U (genericPoint Z) hx inferInstance
  obtain ⟨a⟩ := ideal_power_finite_free_lattice Z J n r
  refine ⟨J ^ n, ideal_coherent Z _, a.hom ≫ χ, ?_⟩
  have := hχiso
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
