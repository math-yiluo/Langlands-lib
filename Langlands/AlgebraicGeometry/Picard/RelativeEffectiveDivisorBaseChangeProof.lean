import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.StructureKernelFlatBaseChange
import Mathlib.Topology.Sheaves.LocallySurjective
import Langlands.AlgebraicGeometry.Modules.AffineCartesianSectionsBaseChange
import Mathlib.RingTheory.Flat.Equalizer
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AlgebraicGeometry.Picard.LineBundleFiniteMonoDetector
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial

/-! # Arbitrary base change of relative effective Cartier divisors: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules (unitToPushforwardUnit)

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof

open StructureKernelModule

/-- For a closed immersion `i`, the structure map `𝒪_X ⟶ i_* 𝒪_Y` is an epimorphism: it is
surjective on sections over affine opens, hence locally surjective. -/
lemma epi_unitToPushforwardUnit {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] :
    Epi (unitToPushforwardUnit i) := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  suffices Epi (F.map (unitToPushforwardUnit i)) from F.epi_of_epi_map this
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi (X := X.toTopCat)
    (C := AddCommGrpCat.{u}) (F.map (unitToPushforwardUnit i))).1 ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  have hVU' : V ≤ U := hVU
  exact ⟨V, hVU', i.app_surjective V hV _, hxV⟩

section KernelBaseChange

open StructureKernelFlatBaseChange Langlands.Scheme.Modules

variable {X Y X' Y' : Scheme.{u}} (b : X' ⟶ X) (i : Y ⟶ X) (i' : Y' ⟶ X') (p : Y' ⟶ Y)
  [IsClosedImmersion i] (h : IsPullback p i' i b)
  [hm : Mono ((Scheme.Modules.pullback b).map (kernelModuleι i))]

/-- The pulled-back ideal inclusion is a kernel of the pulled-back structure map, once it is a
monomorphism: pullback is right exact and the structure map of a closed immersion is an
epimorphism. -/
def pullbackKernelIsKernel :
    IsLimit (KernelFork.ofι ((Scheme.Modules.pullback b).map (kernelModuleι i))
      (by rw [← Functor.map_comp, kernelModule_condition, Functor.map_zero]) :
        KernelFork ((Scheme.Modules.pullback b).map (unitToPushforwardUnit i))) := by
  let S := ShortComplex.mk (kernelModuleι i) (unitToPushforwardUnit i) (kernelModule_condition i)
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S (kernelModuleIsKernel i)
  have hepi : Epi S.g := epi_unitToPushforwardUnit i
  have hFS := hS.map_of_epi_of_preservesCokernel (Scheme.Modules.pullback b) hepi inferInstance
  have : Mono (S.map (Scheme.Modules.pullback b)).f := hm
  exact hFS.fIsKernel

/-- The comparison from the pulled-back ideal module to the ideal module of the base change. -/
def pullbackKernelToKernel [IsAffineHom i] :
    (Scheme.Modules.pullback b).obj (kernelModule i) ⟶ kernelModule i' :=
  kernelModuleLift i' ((Scheme.Modules.pullback b).map (kernelModuleι i) ≫ (pullbackUnitIso b).hom)
    (by
      rw [Category.assoc, ← structureMap_baseChange b i i' p h.w, ← Category.assoc,
        ← Functor.map_comp, kernelModule_condition, Functor.map_zero, zero_comp])

omit [IsClosedImmersion i] hm in
lemma pullbackKernelToKernel_ι [IsAffineHom i] :
    pullbackKernelToKernel b i i' p h ≫ kernelModuleι i' =
      (Scheme.Modules.pullback b).map (kernelModuleι i) ≫ (pullbackUnitIso b).hom :=
  kernelModuleLift_ι _ _ _

omit [IsClosedImmersion i] hm in
lemma unitIso_inv_comp_structureMap [IsAffineHom i] :
    (pullbackUnitIso b).inv ≫ (Scheme.Modules.pullback b).map (unitToPushforwardUnit i) =
      unitToPushforwardUnit i' ≫ (structurePushforwardBaseChangeIso b i i' p h).inv := by
  rw [Iso.eq_comp_inv, Category.assoc]
  change (pullbackUnitIso b).inv ≫ (Scheme.Modules.pullback b).map (unitToPushforwardUnit i) ≫
    structurePushforwardBaseChange b i i' p h.w = _
  rw [structureMap_baseChange, Iso.inv_hom_id_assoc]

/-- The inverse comparison, from the kernel property of the pulled-back inclusion. -/
def kernelToPullbackKernel [IsAffineHom i] :
    kernelModule i' ⟶ (Scheme.Modules.pullback b).obj (kernelModule i) :=
  (KernelFork.IsLimit.lift' (pullbackKernelIsKernel b i)
    (kernelModuleι i' ≫ (pullbackUnitIso b).inv) (by
      rw [Category.assoc, unitIso_inv_comp_structureMap b i i' p h, ← Category.assoc,
        kernelModule_condition, zero_comp])).1

lemma kernelToPullbackKernel_comp [IsAffineHom i] :
    kernelToPullbackKernel b i i' p h ≫ (Scheme.Modules.pullback b).map (kernelModuleι i) =
      kernelModuleι i' ≫ (pullbackUnitIso b).inv :=
  (KernelFork.IsLimit.lift' (pullbackKernelIsKernel b i) _ _).2

/-- **Base change of the ideal module.** If the pulled-back ideal inclusion is a monomorphism,
the pullback of the ideal module of a closed immersion is the ideal module of its base change,
compatibly with the inclusions into the structure modules. -/
def kernelModuleBaseChangeIso [IsAffineHom i] :
    (Scheme.Modules.pullback b).obj (kernelModule i) ≅ kernelModule i' where
  hom := pullbackKernelToKernel b i i' p h
  inv := kernelToPullbackKernel b i i' p h
  hom_inv_id := by
    rw [← cancel_mono ((Scheme.Modules.pullback b).map (kernelModuleι i)), Category.assoc,
      kernelToPullbackKernel_comp, ← Category.assoc, pullbackKernelToKernel_ι, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    have : Mono (kernelModuleι i') := Fork.IsLimit.mono (kernelModuleIsKernel i')
    rw [← cancel_mono (kernelModuleι i'), Category.assoc, pullbackKernelToKernel_ι,
      ← Category.assoc, kernelToPullbackKernel_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

end KernelBaseChange

section MonoDetection

/-- On an affine scheme, a morphism of invertible modules injective on global sections is a
monomorphism: sections over basic opens are localizations of global sections. -/
lemma mono_of_injective_top {Y : Scheme.{u}} [IsAffine Y] {M N : Y.Modules} (φ : M ⟶ N)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (hinj : Function.Injective (φ.app ⊤)) : Mono φ := by
  apply Langlands.SchemeModule.mono_of_stalk_injective
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis (isBasis_basicOpen Y)
  rintro U ⟨r, rfl⟩
  change Function.Injective (φ.app (Y.basicOpen r))
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨hM₁, -⟩ := Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M
    hM.exists_trivialization ⟨⊤, isAffineOpen_top Y⟩ r
  obtain ⟨-, hN₂⟩ := Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial N
    hN.exists_trivialization ⟨⊤, isAffineOpen_top Y⟩ r
  obtain ⟨n, y, hy⟩ := hM₁ x
  let res := (homOfLE (Y.basicOpen_le r) : Y.basicOpen r ⟶ ⊤)
  have hφy : N.presheaf.map res.op (φ.app ⊤ y) = 0 := by
    have hnat := congrArg (fun k => k y) (φ.mapPresheaf.naturality res.op)
    simp only [Scheme.Modules.mapPresheaf_app] at hnat
    change N.presheaf.map res.op (φ.app ⊤ y) = _
    rw [← ConcreteCategory.comp_apply, ← hnat, ConcreteCategory.comp_apply]
    change φ.app (Y.basicOpen r) (M.presheaf.map res.op y) = 0
    rw [hy, Scheme.Modules.Hom.app_smul, hx, smul_zero]
  obtain ⟨m, hm⟩ := hN₂ (φ.app ⊤ y) hφy
  have hy0 : (r ^ m : Γ(Y, ⊤)) • y = 0 := hinj (by
    rw [Scheme.Modules.Hom.app_smul, hm, map_zero])
  have h0 : Y.presheaf.map res.op (r ^ m) • Y.presheaf.map res.op (r ^ n) • x = 0 := by
    rw [← hy, ← Scheme.Modules.map_smul, hy0, map_zero]
  have hu : IsUnit (Y.presheaf.map res.op r) := Y.toRingedSpace.isUnit_res_basicOpen r
  rw [← mul_smul, ← map_mul, ← pow_add] at h0
  exact ((hu.pow (m + n)).map (RingHom.id _)).smul_eq_zero.1 (by simpa using h0)

end MonoDetection

section Chart

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Invertible modules are quasi-coherent. -/
lemma isQuasicoherent_of_isInvertible {X : Scheme.{u}} {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) : M.IsQuasicoherent :=
  IsLocallyFreeRankOne.isQuasicoherent (fun x => by
    obtain ⟨U, hx, ⟨e⟩⟩ := hM.exists_trivialization x
    exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫ e⟩⟩)

/-- **Monomorphism on an affine cartesian chart.** Let `ι : M ⟶ N` be a morphism of invertible
modules on an affine `U ⟶ Spec R` whose `R`-linear map on sections is injective with flat
cokernel `C`. Then its pullback along any affine cartesian base change `Y ⟶ U` over
`Spec R' ⟶ Spec R` is a monomorphism. -/
lemma mono_pullback_of_affine_square {U Y : Scheme.{u}} [IsAffine U] [IsAffine Y]
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : U ⟶ Spec R) (f' : Y ⟶ Spec R') (g : Y ⟶ U)
    (hsq : IsPullback g f' f (Spec.map φ)) {M N : U.Modules} (ι : M ⟶ N)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    {C : Type u} [AddCommGroup C] [Module R C] [Module.Flat R C]
    (q : (relativeGlobalSections f).obj N →ₗ[R] C) (hq : Function.Surjective q)
    (hι : Function.Injective ((relativeGlobalSections f).map ι))
    (hex : Function.Exact ((relativeGlobalSections f).map ι) q) :
    Mono ((Scheme.Modules.pullback g).map ι) := by
  have : M.IsQuasicoherent := isQuasicoherent_of_isInvertible hM
  have : N.IsQuasicoherent := isQuasicoherent_of_isInvertible hN
  have hext : Function.Injective
      ((ModuleCat.extendScalars φ.hom).map ((relativeGlobalSections f).map ι)) := by
    let := φ.hom.toAlgebra
    exact LinearMap.lTensor_injective_of_exact_of_flat q hq _ hι hex R'
  have iM := isIso_scalarSectionsBaseChangeMap_of_isPullback_affine φ f f' g hsq.w hsq M
  have iN := isIso_scalarSectionsBaseChangeMap_of_isPullback_affine φ f f' g hsq.w hsq N
  have hnat := scalarSectionsBaseChangeMap_naturality φ f f' g hsq.w ι
  have htop : Function.Injective
      ((relativeGlobalSections f').map ((Scheme.Modules.pullback g).map ι)) := by
    have heq : (relativeGlobalSections f').map ((Scheme.Modules.pullback g).map ι) =
        inv (scalarSectionsBaseChangeMap φ f f' g hsq.w M) ≫
          (ModuleCat.extendScalars φ.hom).map ((relativeGlobalSections f).map ι) ≫
            scalarSectionsBaseChangeMap φ f f' g hsq.w N := by
      rw [hnat, IsIso.inv_hom_id_assoc]
    rw [heq]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso
        (scalarSectionsBaseChangeMap φ f f' g hsq.w N)).1.comp
      (hext.comp (ConcreteCategory.bijective_of_isIso
        (inv (scalarSectionsBaseChangeMap φ f f' g hsq.w M))).1)
  exact mono_of_injective_top _ (hM.pullback g) (hN.pullback g) htop

end Chart

section StalkTransfer

/-- A morphism whose pullback along an open immersion `j` is a monomorphism is injective on
stalks at the points of the image of `j`. -/
lemma stalk_injective_of_mono_pullback {W Z : Scheme.{u}} (j : W ⟶ Z) [IsOpenImmersion j]
    {M N : Z.Modules} (α : M ⟶ N) [Mono ((Scheme.Modules.pullback j).map α)] (w : W) :
    Function.Injective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} (j w)).map α.mapPresheaf) := by
  have : Mono ((Scheme.Modules.restrictFunctor j).map α) := by
    let e := Scheme.Modules.restrictFunctorIsoPullback j
    have he : (Scheme.Modules.restrictFunctor j).map α =
        e.hom.app M ≫ (Scheme.Modules.pullback j).map α ≫ e.inv.app N := by
      rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id]
    rw [he]
    infer_instance
  let G := Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.toPresheaf W ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} w
  let F := Scheme.Modules.toPresheaf Z ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (j w)
  let e : G ≅ F := Scheme.Modules.restrictStalkNatIso j w
  have : Mono (G.map α) :=
    ConcreteCategory.mono_of_injective _
      (Langlands.SchemeModule.stalk_injective_of_mono
        ((Scheme.Modules.restrictFunctor j).map α) w)
  have heq : F.map α = e.inv.app M ≫ G.map α ≫ e.hom.app N := by
    rw [e.hom.naturality, ← Category.assoc, e.inv_hom_id_app]
    simp
  have : Mono (F.map α) := by
    rw [heq]
    infer_instance
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (F.map α)

end StalkTransfer

section ConcreteChart

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Ring-hom form of `mono_pullback_of_affine_square`: the cokernel of the sections map is a
flat `R`-algebra `B`, the sections map to it being `R`-semilinear along `ρ`. -/
lemma mono_pullback_of_affine_square_ring {U Y : Scheme.{u}} [IsAffine U] [IsAffine Y]
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : U ⟶ Spec R) (f' : Y ⟶ Spec R') (g : Y ⟶ U)
    (hsq : IsPullback g f' f (Spec.map φ)) {M N : U.Modules} (ι : M ⟶ N)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    {B : CommRingCat.{u}} (ρ : R ⟶ B) (hρ : ρ.hom.Flat)
    (q : (relativeGlobalSections f).obj N →+ B)
    (hq_smul : ∀ (r : R) (n : (relativeGlobalSections f).obj N), q (r • n) = ρ r * q n)
    (hq : Function.Surjective q)
    (hι : Function.Injective ((relativeGlobalSections f).map ι))
    (hex : Function.Exact ((relativeGlobalSections f).map ι) q) :
    Mono ((Scheme.Modules.pullback g).map ι) := by
  let := ρ.hom.toAlgebra
  have : Module.Flat R B := hρ
  exact mono_pullback_of_affine_square φ f f' g hsq ι hM hN
    { toFun := q, map_add' := q.map_add, map_smul' := fun r n => by
        rw [hq_smul]; rfl } hq hι hex

/-- Invertibility is invariant under isomorphism. -/
lemma isInvertible_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (e : M ≅ N) : Scheme.Modules.IsInvertible N :=
  ⟨fun x => by
    obtain ⟨U, hx, ⟨eU⟩⟩ := hM.exists_trivialization x
    exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ eU⟩⟩⟩

/-- Restriction along an open immersion preserves invertibility. -/
lemma isInvertible_restrict {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) : Scheme.Modules.IsInvertible (M.restrict j) :=
  isInvertible_of_iso (hM.pullback j) ((Scheme.Modules.restrictFunctorIsoPullback j).app M).symm

variable {S X E : Scheme.{u}} (f : X ⟶ S) (i : E ⟶ X)

/-- The affine chart `U₀ ⟶ Spec Γ(S, V)` of `f` over an affine open `V` of the base. -/
def chartMap {V : S.Opens} (U₀ : X.Opens) (e : U₀ ≤ f ⁻¹ᵁ V) : U₀.toScheme ⟶ Spec Γ(S, V) :=
  U₀.toSpecΓ ≫ Spec.map (f.appLE V U₀ e)

lemma chartMap_fromSpec {V : S.Opens} (hV : IsAffineOpen V) {U₀ : X.Opens}
    (hU₀ : IsAffineOpen U₀) (e : U₀ ≤ f ⁻¹ᵁ V) :
    chartMap f U₀ e ≫ hV.fromSpec = U₀.ι ≫ f := by
  rw [chartMap, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hU₀ e,
    IsAffineOpen.toSpecΓ_fromSpec_assoc]

lemma structureRingHom_chartMap {V : S.Opens} (U₀ : X.Opens) (e : U₀ ≤ f ⁻¹ᵁ V) :
    structureRingHom (chartMap f U₀ e) = f.appLE V U₀ e ≫ U₀.topIso.inv := by
  rw [structureRingHom, chartMap, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc]

lemma chart_ringHom_eq {V : S.Opens} (U₀ : X.Opens) (e : U₀ ≤ f ⁻¹ᵁ V)
    (e' : i ⁻¹ᵁ (U₀.ι ''ᵁ ⊤) ≤ (i ≫ f) ⁻¹ᵁ V) :
    f.appLE V U₀ e ≫ U₀.topIso.inv ≫ i.app (U₀.ι ''ᵁ ⊤) =
      (i ≫ f).appLE V (i ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) e' := by
  rw [Scheme.Opens.topIso_inv, Scheme.Hom.appLE_map_assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]

variable [IsClosedImmersion i] [Flat (i ≫ f)]

/-- **The chart monomorphism.** On an affine chart `U₀ ⟶ Spec Γ(S, V)` of `f`, the restricted
ideal inclusion stays a monomorphism after any affine base change: its sections are the
inclusion of the ideal into `Γ(X, U₀)`, whose cokernel `Γ(E, i⁻¹ U₀)` is flat over `Γ(S, V)`
because `i ≫ f` is flat. -/
lemma mono_chart (hK : Scheme.Modules.IsInvertible (kernelModule i)) {V : S.Opens}
    (hV : IsAffineOpen V) {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀) (e : U₀ ≤ f ⁻¹ᵁ V)
    {R' : CommRingCat.{u}} (ψ : Γ(S, V) ⟶ R') {Y : Scheme.{u}} [IsAffine Y] (f' : Y ⟶ Spec R')
    (g' : Y ⟶ U₀) (hsq : IsPullback g' f' (chartMap f U₀ e) (Spec.map ψ)) :
    Mono ((Scheme.Modules.pullback g').map
      ((Scheme.Modules.restrictFunctor U₀.ι).map (kernelModuleι i))) := by
  have : IsAffine U₀ := hU₀
  have hW : IsAffineOpen (U₀.ι ''ᵁ ⊤) := by rw [Scheme.Opens.ι_image_top]; exact hU₀
  have hEW : IsAffineOpen (i ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) := hW.preimage i
  have e' : i ⁻¹ᵁ (U₀.ι ''ᵁ ⊤) ≤ (i ≫ f) ⁻¹ᵁ V := by
    intro x hx
    have h1 : i x ∈ U₀.ι ''ᵁ ⊤ := hx
    rw [Scheme.Opens.ι_image_top] at h1
    exact e h1
  refine mono_pullback_of_affine_square_ring ψ (chartMap f U₀ e) f' g' hsq _
    (isInvertible_restrict U₀.ι hK)
    (isInvertible_restrict U₀.ι (Scheme.Modules.isInvertible_unit X))
    ((i ≫ f).appLE V (i ⁻¹ᵁ (U₀.ι ''ᵁ ⊤)) e')
    (HasRingHomProperty.appLE (P := @Flat) _ inferInstance ⟨V, hV⟩ ⟨_, hEW⟩ e')
    (AddMonoidHom.mk' (fun a => i.app (U₀.ι ''ᵁ ⊤) a) (fun a b => map_add _ a b)) ?_ ?_ ?_ ?_
  · intro r a
    have h1 : r • a = (show Γ(X, U₀.ι ''ᵁ ⊤) from (U₀.ι.appIso ⊤).inv
        (structureRingHom (chartMap f U₀ e) r)) * (show Γ(X, U₀.ι ''ᵁ ⊤) from a) := rfl
    rw [h1]
    simp only [AddMonoidHom.mk'_apply, map_mul, Scheme.Opens.ι_appIso, Iso.refl_inv]
    congr 1
    rw [structureRingHom_chartMap, ← chart_ringHom_eq f i U₀ e e']
    rfl
  · exact i.app_surjective _ hW
  · intro a b h
    exact Subtype.ext h
  · intro a
    constructor
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2

end ConcreteChart

section GlobalMono

/-- A functor naturally isomorphic to one sending `α` to a monomorphism sends `α` to a
monomorphism. -/
lemma mono_map_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    {A B : C} (α : A ⟶ B) [Mono (G.map α)] : Mono (F.map α) := by
  rw [← NatIso.naturality_2 e α]
  infer_instance

/-- **Tor vanishing for relative effective Cartier divisors.** If the ideal module of a closed
immersion `i : E ⟶ X` is invertible and `i ≫ f` is flat, then the pullback of the ideal
inclusion along `pullback.snd g f` is a monomorphism, for every `g : T ⟶ S`. -/
lemma mono_pullback_snd_kernelModuleι {S X T E : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (i : E ⟶ X) [IsClosedImmersion i] [Flat (i ≫ f)]
    (hK : Scheme.Modules.IsInvertible (kernelModule i)) :
    Mono ((Scheme.Modules.pullback (pullback.snd g f)).map (kernelModuleι i)) := by
  apply Langlands.SchemeModule.mono_of_stalk_injective
  intro x
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (pullback.snd g f x)) (U := ⊤) trivial
  obtain ⟨U₀, hU₀, hxU₀, hU₀V⟩ := exists_isAffineOpen_mem_and_subset
    (x := pullback.snd g f x) (U := f ⁻¹ᵁ V) hxV
  have hgx : g (pullback.fst g f x) ∈ V := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact hxV
  obtain ⟨VT, hVT, hxVT, hVTV⟩ := exists_isAffineOpen_mem_and_subset
    (x := pullback.fst g f x) (U := g ⁻¹ᵁ V) hgx
  have e : U₀ ≤ f ⁻¹ᵁ V := hU₀V
  have eT : VT ≤ g ⁻¹ᵁ V := hVTV
  have : IsAffine U₀ := hU₀
  let ψ := g.appLE V VT eT
  let c := chartMap f U₀ e
  have hsq : IsPullback (pullback.snd (Spec.map ψ) c) (pullback.fst (Spec.map ψ) c) c
      (Spec.map ψ) := (IsPullback.of_hasPullback (Spec.map ψ) c).flip
  have hmono := mono_chart f i hK hV hU₀ e ψ _ _ hsq
  have e₁ : Spec.map ψ ≫ hV.fromSpec = hVT.fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hV hVT eT
  have e₂ : c ≫ hV.fromSpec = U₀.ι ≫ f := chartMap_fromSpec f hV hU₀ e
  let j := pullback.map (Spec.map ψ) c g f hVT.fromSpec U₀.ι hV.fromSpec e₁ e₂
  have hj : j ≫ pullback.snd g f = pullback.snd (Spec.map ψ) c ≫ U₀.ι := by
    simp [j]
  have hx : x ∈ Set.range j := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · change pullback.fst g f x ∈ Set.range hVT.fromSpec
      rw [IsAffineOpen.range_fromSpec]
      exact hxVT
    · change pullback.snd g f x ∈ Set.range U₀.ι
      rw [Scheme.Opens.range_ι]
      exact hxU₀
  obtain ⟨w, rfl⟩ := hx
  let eF : Scheme.Modules.pullback (pullback.snd g f) ⋙ Scheme.Modules.pullback j ≅
      Scheme.Modules.restrictFunctor U₀.ι ⋙
        Scheme.Modules.pullback (pullback.snd (Spec.map ψ) c) :=
    Scheme.Modules.pullbackComp j (pullback.snd g f) ≪≫ Scheme.Modules.pullbackCongr hj ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd (Spec.map ψ) c) U₀.ι).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U₀.ι).symm _
  have : Mono ((Scheme.Modules.restrictFunctor U₀.ι ⋙
      Scheme.Modules.pullback (pullback.snd (Spec.map ψ) c)).map (kernelModuleι i)) := hmono
  have : Mono ((Scheme.Modules.pullback j).map
      ((Scheme.Modules.pullback (pullback.snd g f)).map (kernelModuleι i))) :=
    mono_map_of_iso eF (kernelModuleι i)
  exact stalk_injective_of_mono_pullback j _ w

end GlobalMono

/-- **Arbitrary base change of relative effective Cartier divisors.** -/
theorem relativeEffectiveDivisorBaseChange : RelativeEffectiveDivisorBaseChangeStatement.{u} := by
  intro S X f I hI T g
  have hK : Scheme.Modules.IsInvertible (kernelModule I.subschemeι) :=
    isInvertible_of_isLocallyFreeRankOne hI.1
  have : Flat (I.subschemeι ≫ f) := hI.2
  have hm := mono_pullback_snd_kernelModuleι f g I.subschemeι hK
  have hsq : IsPullback
      ((I.comapIso (pullback.snd g f)).hom ≫ pullback.snd (pullback.snd g f) I.subschemeι)
      (I.comap (pullback.snd g f)).subschemeι I.subschemeι (pullback.snd g f) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩
      (I.comapIso (pullback.snd g f) ≪≫ pullbackSymmetry (pullback.snd g f) I.subschemeι) ?_ ?_
    · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
        Scheme.IdealSheafData.comapIso_hom_fst]
    · simp
    · simp
  exact ⟨RelativeEffectiveDivisorBaseChange.isRelativeEffectiveCartierIdeal_of_kernelIso f I g hI
      (kernelModuleBaseChangeIso (pullback.snd g f) I.subschemeι
        (I.comap (pullback.snd g f)).subschemeι _ hsq),
    kernelModuleBaseChangeIso (pullback.snd g f) I.subschemeι
        (I.comap (pullback.snd g f)).subschemeι _ hsq,
    pullbackKernelToKernel_ι _ _ _ _ hsq⟩

end Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof
