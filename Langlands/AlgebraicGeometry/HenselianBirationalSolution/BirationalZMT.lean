import Langlands.AlgebraicGeometry.NormalDominantMono
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Zariski's Main Theorem for birational quasi-finite morphisms

A separated quasi-finite morphism of finite type from a reduced scheme to a locally noetherian
normal scheme which restricts to an open immersion on a dense open subscheme is
an open immersion (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §2.3 Theorem 2').
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

private theorem isIntegrallyClosed_affineSections_of_hasNormalStalks'
    {Y : Scheme.{u}} [IsIntegral Y] (hY : HasNormalStalks Y)
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(Y, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let y : PrimeSpectrum Γ(Y, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv p.primeCompl
    (Y.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)
  exact (hY (hU.fromSpec y)).2.of_equiv e.toRingEquiv

section Integral

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsDominant f]

set_option backward.isDefEq.respectTransparency false in
omit [LocallyOfFiniteType f] in
private theorem isIso_fromNormalization_of_surjective_stalkMap (hY : HasNormalStalks Y)
    (hη : Function.Surjective (f.stalkMap (genericPoint X))) :
    IsIso f.fromNormalization := by
  have hη' : f (genericPoint X) = genericPoint Y := by
    apply IsGenericPoint.eq _ (genericPoint_spec Y)
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
    (iSup_affineOpens_eq_top Y)).mpr fun U => ?_
  change IsIso (f.fromNormalization ∣_ U.1)
  by_cases hU : Nonempty U.1
  · rw [isIso_morphismRestrict_iff_isIso_app _ U.2, f.fromNormalization_app U.2]
    let A := Γ(Y, U.1)
    let V := f ⁻¹ᵁ U.1
    let B := Γ(X, V)
    let K := X.functionField
    have hUY : genericPoint Y ∈ U.1 :=
      ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr (by simpa using hU)
    have hUX : genericPoint X ∈ V := by
      change f (genericPoint X) ∈ U.1
      exact hη'.symm ▸ hUY
    let : Nonempty V := ⟨⟨_, hUX⟩⟩
    let : Algebra A B := (f.app U.1).hom.toAlgebra
    let : Algebra A K :=
      ((X.germToFunctionField V).hom.comp (f.app U.1).hom).toAlgebra
    have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let g := (Y.presheaf.stalkCongr (.of_eq hη'.symm)).hom
    let e : Y.functionField →ₐ[A] K :=
      { (g ≫ f.stalkMap (genericPoint X)).hom with
        commutes' := fun a => by
          change ((Y.germToFunctionField U.1 ≫ g ≫ f.stalkMap (genericPoint X)) a) =
            ((f.app U.1 ≫ X.germToFunctionField V) a)
          have hg : Y.germToFunctionField U.1 ≫ g =
              Y.presheaf.germ U.1 (f (genericPoint X)) hUX :=
            Y.presheaf.germ_stalkSpecializes hUY (.of_eq hη')
          rw [← Category.assoc, hg, f.germ_stalkMap] }
    have : IsFractionRing A Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y U.1 U.2
    have he : Function.Bijective e :=
      ⟨e.toRingHom.injective, hη.comp (ConcreteCategory.bijective_of_isIso g).2⟩
    have : IsFractionRing A K := IsFractionRing.of_algEquiv (AlgEquiv.ofBijective e he)
    have hA : IsIntegrallyClosed A :=
      isIntegrallyClosed_affineSections_of_hasNormalStalks' hY U.2
    have hj : Function.Injective (algebraMap B K) := X.germToFunctionField_injective V
    have h : IsIso (CommRingCat.ofHom (algebraMap A (integralClosure A B))) := by
      refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
      · intro a b hab
        apply IsFractionRing.injective A K
        exact congrArg (fun z : integralClosure A B => algebraMap B K z) hab
      · rintro ⟨b, hb⟩
        obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff K).mp hA
          (hb.map (IsScalarTower.toAlgHom A B K))
        exact ⟨a, Subtype.ext (hj ha)⟩
    infer_instance
  · have : IsEmpty U.1 := not_nonempty_iff.mp hU
    infer_instance

/-- A separated quasi-finite dominant morphism of finite type between integral schemes whose
target has normal stalks, and whose map of generic stalks is surjective, is an open
immersion. -/
theorem isOpenImmersion_of_surjective_genericStalkMap [LocallyQuasiFinite f]
    (hY : HasNormalStalks Y) (hη : Function.Surjective (f.stalkMap (genericPoint X))) :
    IsOpenImmersion f := by
  have := isIso_fromNormalization_of_surjective_stalkMap f hY hη
  rw [← f.toNormalization_fromNormalization]
  infer_instance

end Integral

/-- Over an integral target with normal stalks, a separated quasi-finite morphism of finite type
from a reduced scheme which restricts to an open immersion on a dense open subscheme is an open
immersion. -/
theorem isOpenImmersion_of_integral_target {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [LocallyQuasiFinite f]
    [IsReduced X] (hY : HasNormalStalks Y) (U : X.Opens) (hU : Dense (U : Set X))
    [IsOpenImmersion (U.ι ≫ f)] : IsOpenImmersion f := by
  by_cases hX : IsEmpty X
  · infer_instance
  have : Nonempty X := not_isEmpty_iff.mp hX
  have hUne : (U : Set X).Nonempty := hU.nonempty
  set e := U.ι ≫ f with he
  have hrangeOpen : IsOpen (Set.range e) := e.isOpenEmbedding.isOpen_range
  have hrangeNe : (Set.range e).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    exact ⟨e ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
  have hrange : IsPreirreducible (Set.range e) :=
    (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset hrangeOpen
      (Set.subset_univ _)
  have hUirr : IsPreirreducible (Set.univ : Set U.toScheme) := by
    have := hrange.preimage e.isOpenEmbedding
    simpa only [Set.preimage_range] using this
  have hUirr' : IsPreirreducible (U : Set X) := by
    have := hUirr.image U.ι (U.ι.continuous.continuousOn)
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using this
  have hXirr : IsIrreducible (Set.univ : Set X) := by
    rw [← hU.closure_eq]
    exact isIrreducible_iff_closure.mpr ⟨hUne, hUirr'⟩
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr hXirr
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have : IsDominant f := by
    constructor
    have hd : Dense (Set.range e) :=
      (preirreducibleSpace_iff_open_dense Y).mp inferInstance hrangeOpen hrangeNe
    refine hd.mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨U.ι x, rfl⟩
  apply isOpenImmersion_of_surjective_genericStalkMap f hY
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)
  let x₀ : U.toScheme := ⟨genericPoint X, hgen⟩
  have h1 : IsIso ((U.ι ≫ f).stalkMap x₀) := inferInstance
  have h2 : IsIso (f.stalkMap (U.ι x₀) ≫ U.ι.stalkMap x₀) := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact h1
  have h3 : IsIso (f.stalkMap (U.ι x₀)) :=
    IsIso.of_isIso_comp_right (f.stalkMap (U.ι x₀)) (U.ι.stalkMap x₀)
  exact (ConcreteCategory.bijective_of_isIso (f.stalkMap (U.ι x₀))).2

/-- In a locally noetherian scheme whose stalks are domains every point has an irreducible open
neighbourhood. -/
theorem exists_isIrreducible_open_nhds {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ IsIrreducible (W : Set Y) := by
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsNoetherianRing Γ(Y, W₀) := IsLocallyNoetherian.component_noetherian ⟨W₀, hW₀⟩
  have : NoetherianSpace W₀ := noetherianSpace_of_isAffineOpen W₀ hW₀
  have : QuasiSober W₀ := W₀.isOpenEmbedding'.quasiSober
  let y' : W₀ := ⟨y, hyW₀⟩
  -- the generizations of `y'` form an irreducible set
  have hG : IsPreirreducible {z : W₀ | z ⤳ y'} := by
    have := hY y
    have hGY : IsPreirreducible {z : Y | z ⤳ y} := by
      rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.image _
        (Y.fromSpecStalk y).continuous.continuousOn
    have := hGY.preimage W₀.isOpenEmbedding'
    convert this using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact (W₀.isOpenEmbedding'.toIsInducing.specializes_iff).symm
  have hGirr : IsIrreducible (closure {z : W₀ | z ⤳ y'}) :=
    isIrreducible_iff_closure.mpr ⟨⟨y', specializes_rfl⟩, hG⟩
  -- every component through `y'` is the closure of the generizations
  have hcomp : ∀ C ∈ irreducibleComponents W₀, y' ∈ C → C = closure {z : W₀ | z ⤳ y'} := by
    intro C hC hyC
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    have hξy : ξ ⤳ y' := hξ.specializes hyC
    have hsub : C ⊆ closure {z : W₀ | z ⤳ y'} := by
      rw [← hξ.def]
      exact closure_mono (Set.singleton_subset_iff.mpr hξy)
    exact le_antisymm hsub (hC.2 hGirr hsub)
  set Z := irreducibleComponent y'
  have hZ : Z ∈ irreducibleComponents W₀ := irreducibleComponent_mem_irreducibleComponents y'
  let O : Set W₀ := (⋃₀ (irreducibleComponents W₀ \ {Z}))ᶜ
  have hOopen : IsOpen O := by
    show IsOpen (⋃₀ (irreducibleComponents W₀ \ {Z}))ᶜ
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hyO : y' ∈ O := by
    intro h
    obtain ⟨C, ⟨hC, hCZ⟩, hyC⟩ := Set.mem_sUnion.mp h
    exact hCZ (Set.mem_singleton_iff.mpr
      ((hcomp C hC hyC).trans (hcomp Z hZ mem_irreducibleComponent).symm))
  have hOZ : O ⊆ Z := by
    intro z hz
    obtain ⟨C, hC, hzC⟩ := Set.mem_sUnion.mp
      (show z ∈ ⋃₀ irreducibleComponents W₀ by rw [sUnion_irreducibleComponents]; trivial)
    by_cases hCZ : C = Z
    · exact hCZ ▸ hzC
    · exact absurd (Set.mem_sUnion.mpr ⟨C, show C ∈ irreducibleComponents W₀ \ {Z} from
        ⟨hC, hCZ⟩, hzC⟩) hz
  have hOirr : IsIrreducible O :=
    isIrreducible_irreducibleComponent.isPreirreducible.subset_irreducible (S := O) (U := O)
      ⟨y', hyO⟩ hOopen subset_rfl hOZ
  refine ⟨⟨Subtype.val '' O, W₀.isOpenEmbedding'.isOpenMap _ hOopen⟩,
    show y ∈ Subtype.val '' O from ⟨y', hyO, rfl⟩, ?_⟩
  exact hOirr.image _ continuous_subtype_val.continuousOn

/-- **Zariski's Main Theorem, birational form.** A separated quasi-finite morphism of finite type
from a reduced scheme to a locally noetherian normal scheme which restricts to an open immersion
on a dense open subscheme is an open immersion. -/
theorem isOpenImmersion_of_birational {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [LocallyQuasiFinite f]
    [IsReduced X] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsOpenImmersion f := by
  choose W hyW hWirr using exists_isIrreducible_open_nhds (fun y => (hY y).1)
  have hcov : iSup W = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsOpenImmersion) W hcov]
  intro y
  have : IsReduced Y := by
    have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
      have := (hY y).1
      infer_instance
    exact isReduced_of_isReduced_stalk Y
  have : IrreducibleSpace (W y).toScheme := Subtype.irreducibleSpace (hWirr y)
  have : IsIntegral (W y).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hWn : HasNormalStalks (W y).toScheme := by
    intro w
    let e := ((W y).stalkIso w).commRingCatIsoToRingEquiv
    have h1 := (hY w.1).1
    have h2 := (hY w.1).2
    exact ⟨MulEquiv.isDomain _ e.toMulEquiv, h2.of_equiv e.symm⟩
  let U' : (f ⁻¹ᵁ W y).toScheme.Opens := (f ⁻¹ᵁ W y).ι ⁻¹ᵁ U
  have hU' : Dense (U' : Set (f ⁻¹ᵁ W y).toScheme) :=
    hU.preimage (f ⁻¹ᵁ W y).ι.isOpenEmbedding.isOpenMap
  have hrange : Set.range (U'.ι ≫ (f ⁻¹ᵁ W y).ι) ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨_, x.2⟩, rfl⟩
  let ℓ := IsOpenImmersion.lift U.ι (U'.ι ≫ (f ⁻¹ᵁ W y).ι) hrange
  have hℓ : ℓ ≫ U.ι = U'.ι ≫ (f ⁻¹ᵁ W y).ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion ℓ := by
    have : IsOpenImmersion (ℓ ≫ U.ι) := by rw [hℓ]; infer_instance
    exact IsOpenImmersion.of_comp ℓ U.ι
  have : IsOpenImmersion ((U'.ι ≫ (f ∣_ W y)) ≫ (W y).ι) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ← hℓ, Category.assoc]
    infer_instance
  have : IsOpenImmersion (U'.ι ≫ (f ∣_ W y)) := IsOpenImmersion.of_comp _ (W y).ι
  exact isOpenImmersion_of_integral_target (f ∣_ W y) hWn U' hU'

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
