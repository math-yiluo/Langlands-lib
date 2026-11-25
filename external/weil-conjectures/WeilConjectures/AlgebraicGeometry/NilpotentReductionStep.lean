/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLisseRestriction
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLisseTriangle
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLocalModelsComparison
import WeilConjectures.AlgebraicGeometry.LocallyConstantTensor
import WeilConjectures.AlgebraicGeometry.SiteFiniteFreeTruncationModels
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # One step of the coefficient-ideal filtration

Source: Stacks Project, Cohomology on Sites, Tag 094I.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace SheafOfModules

attribute [local irreducible] monoidalCategory in
private theorem tensor_additivity
    {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
    (R : Sheaf T CommRingCat.{u}) :
    letI := monoidalCategory R
    MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) := by
  let := monoidalCategory R
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (MonoidalCategory.tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (MonoidalCategory.tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (MonoidalCategory.tensorLeft X).map_add
        (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (MonoidalCategory.tensorRight X).map_add
        (f := f) (g := g) }

private noncomputable def coefficientMap
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D) :
    constantCoefficientRing T B ⟶ constantCoefficientRing T D :=
  (sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).map
    ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f))

private theorem lisse_of_iso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    {F G : SheafOfModules.{u} (constantCoefficientRing T B)}
    (e : F ≅ G) (h : IsLocallyConstantFiniteTypeModules T B G) :
    IsLocallyConstantFiniteTypeModules T B F := by
  intro V
  obtain ⟨S, hS, hs⟩ := h V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨M, hM, ⟨eM⟩⟩ := hs U f hf
  exact ⟨M, hM, ⟨(overFunctor _ U).mapIso e ≪≫ eM⟩⟩

private noncomputable def constantRestrictionIso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    (M : ModuleCat.{u} D) :
    (constantCoefficientModule T B).obj ((ModuleCat.restrictScalars f).obj M) ≅
      (restrictScalars (coefficientMap T f)).obj ((constantCoefficientModule T D).obj M) := by
  let f₀ : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶
      (Functor.const Cᵒᵖ).obj (RingCat.of D) :=
    (Functor.const Cᵒᵖ).map (RingCat.ofHom f)
  have hsq : f₀ ≫ constantCoefficientUnit T D =
      constantCoefficientUnit T B ≫ (coefficientMap T f).hom := by
    exact congrArg (fun η ↦ Functor.whiskerRight η (forget₂ CommRingCat.{u} RingCat.{u}))
      (toSheafify_naturality T ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f)))
  let P := (strictPerfectConstantPresheaf (C := C) D).obj M
  let e : ((PresheafOfModules.restrictScalars f₀).obj P) ≅
      (strictPerfectConstantPresheaf (C := C) B).obj
        ((ModuleCat.restrictScalars f).obj M) := Iso.refl _
  have := restrictSheafificationComparison_isIso T
    (constantCoefficientUnit T B) (constantCoefficientUnit T D) f₀
    (coefficientMap T f) hsq P
  exact (PresheafOfModules.sheafification.{u} (constantCoefficientUnit T B)).mapIso e.symm ≪≫
    asIso (restrictSheafificationComparison T
      (constantCoefficientUnit T B) (constantCoefficientUnit T D) f₀
      (coefficientMap T f) hsq P)

private theorem restriction_exact
    {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
    {R S : Sheaf T RingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{u} f) ∧
      PreservesFiniteColimits (restrictScalars.{u} f) := by
  let U := restrictScalars.{u} f
  have : PreservesFiniteLimits (U ⋙ toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf S))
  have : PreservesFiniteColimits (U ⋙ toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves U (toSheaf R)⟩

private noncomputable def restriction_fullyFaithful
    {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
    {R S : Sheaf T RingCat.{u}} (f : R ⟶ S)
    [Presheaf.IsLocallySurjective T f.hom] :
    (restrictScalars.{u} f).FullyFaithful := by
  refine ⟨(fun {M N} g ↦
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective f.hom N.isSheaf).symm
      g.val⟩), ?_, ?_⟩
  · intro M N g
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      f.hom N.isSheaf).apply_symm_apply g.val
  · intro M N g
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      f.hom N.isSheaf).symm_apply_apply g.val

private theorem coefficientMap_locallySurjective
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    (hf : Function.Surjective f) :
    Presheaf.IsLocallySurjective T (coefficientMap T f).hom := by
  let f₀ : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶
      (Functor.const Cᵒᵖ).obj (RingCat.of D) :=
    (Functor.const Cᵒᵖ).map (RingCat.ofHom f)
  have : Presheaf.IsLocallySurjective T f₀ :=
    Presheaf.isLocallySurjective_of_surjective T f₀ (fun _ ↦ hf)
  have hsq : f₀ ≫ constantCoefficientUnit T D =
      constantCoefficientUnit T B ≫ (coefficientMap T f).hom := by
    exact congrArg (fun η ↦ Functor.whiskerRight η (forget₂ CommRingCat.{u} RingCat.{u}))
      (toSheafify_naturality T ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f)))
  have : Presheaf.IsLocallySurjective T (f₀ ≫ constantCoefficientUnit T D) :=
    inferInstance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac T hsq.symm

private noncomputable def constantUnitIso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B] :
    (constantCoefficientModule T B).obj (ModuleCat.of B B) ≅
      unit (constantCoefficientRing T B) := by
  let R := constantCoefficientRing T B
  let P := (strictPerfectConstantPresheaf (C := C) B).obj (ModuleCat.of B B)
  let η := constantCoefficientUnit T B
  let a : P ⟶ (PresheafOfModules.restrictScalars η).obj (unit R).val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars η).obj (unit R).val).obj U)
        { toFun := η.app U
          map_add' := (η.app U).hom.map_add
          map_smul' := (η.app U).hom.map_mul }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        exact (ConcreteCategory.congr_hom (η.naturality f) b) }
  let g : P.presheaf ⟶ (unit R).val.presheaf :=
    (PresheafOfModules.toPresheaf.{u} _).map a
  have : Presheaf.IsLocallyInjective T g := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem T η x y h
  have : Presheaf.IsLocallySurjective T g := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem T η x
  let e : (constantCoefficientModule T B).obj (ModuleCat.of B B) ⟶ unit R :=
    (PresheafOfModules.sheafificationHomEquiv.{u} η (P := P) (F := unit R)).symm a
  let q := (toSheaf R).map e
  have hfac : toSheafify T P.presheaf ≫ q.hom = g := by
    have h := congrArg ((PresheafOfModules.toPresheaf.{u} _).map)
      ((PresheafOfModules.sheafificationHomEquiv.{u} η
        (P := P) (F := unit R)).apply_symm_apply a)
    exact h
  have : Presheaf.IsLocallyInjective T q.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac T g hfac
  have : Presheaf.IsLocallySurjective T q.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac T hfac
  have : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).1 ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (toSheaf R)
  exact asIso e

section CoefficientTensor

open MonoidalCategory

variable {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
  {R S A : Sheaf T CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡(" E ")" => (sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻(" f ")" => (sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).map f

private noncomputable def restrictionCompIso
    (α : 𝓡(R) ⟶ 𝓡(S)) (β : 𝓡(S) ⟶ 𝓡(A)) (γ : 𝓡(R) ⟶ 𝓡(A))
    (h : α ≫ β = γ) :
    restrictScalars β ⋙ restrictScalars α ≅ restrictScalars γ := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      (γ.hom.app U).hom :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (γ.hom.app U).hom (hU U).symm (M.val.obj U)).symm) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem cancellationComplexIso
    (φ : R ⟶ S) (N : SheafOfModules.{u} (𝓡(S)))
    (P : CochainComplex (SheafOfModules.{u} (𝓡(R))) ℤ) :
    letI := monoidalCategory R
    letI := monoidalCategory S
    let U := restrictScalars (𝓻(φ))
    Nonempty ((U.mapHomologicalComplex (.up ℤ)).obj
      (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (changeOfRingsComplex.{u, u} φ P)) ≅
    (((tensorLeft (U.obj N)).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let := monoidalCategory R
  let := monoidalCategory S
  let e := (exists_changeOfRings_tensorCancellation.{u, u} φ).choose
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun i ↦ e N (P.X i)) ?_⟩
  intro i j hij
  change (e N (P.X i)).hom ≫
      ((restrictScalars (𝓻(φ))).obj N ◁ P.d i j) =
    (restrictScalars (𝓻(φ))).map (N ◁ changeOfRingsHom φ (P.X i) (P.d i j)) ≫
      (e N (P.X j)).hom
  have hh := ((exists_changeOfRings_tensorCancellation.{u, u} φ).choose_spec
    (𝟙 N) (P.d i j)).symm
  erw [(restrictScalars (𝓻(φ))).map_id] at hh
  simpa only [e, id_tensorHom] using hh

private theorem coefficientTensorIso
    (φ : R ⟶ S) (ψ : S ⟶ A) (χ : R ⟶ A) (h : φ ≫ ψ = χ)
    [Presheaf.IsLocallySurjective T (𝓻(φ)).hom]
    (N : SheafOfModules.{u} (𝓡(A)))
    (P : CochainComplex (SheafOfModules.{u} (𝓡(R))) ℤ) :
    letI := monoidalCategory S
    letI := monoidalCategory A
    let V := restrictScalars (𝓻(ψ))
    Nonempty ((((tensorLeft (V.obj N)).mapHomologicalComplex (.up ℤ)).obj
      (changeOfRingsComplex.{u, u} φ P)) ≅
    ((V.mapHomologicalComplex (.up ℤ)).obj
      (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (changeOfRingsComplex.{u, u} χ P)))) := by
  let := monoidalCategory R
  let := monoidalCategory S
  let := monoidalCategory A
  let U := restrictScalars (𝓻(φ))
  let V := restrictScalars (𝓻(ψ))
  let W := restrictScalars (𝓻(χ))
  let f := restriction_fullyFaithful (𝓻(φ))
  have : U.Full := f.full
  have : U.Faithful := f.faithful
  let c := restrictionCompIso (𝓻(φ)) (𝓻(ψ)) (𝓻(χ))
    (by rw [← Functor.map_comp, h])
  let X := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (changeOfRingsComplex.{u, u} χ P)
  let d : ((tensorLeft (U.obj (V.obj N))).mapHomologicalComplex (.up ℤ)).obj P ≅
      ((tensorLeft (W.obj N)).mapHomologicalComplex (.up ℤ)).obj P :=
    (NatIso.mapHomologicalComplex ((curriedTensor _).mapIso (c.app N)) (.up ℤ)).app P
  let z : (U.mapHomologicalComplex (.up ℤ)).obj
      ((V.mapHomologicalComplex (.up ℤ)).obj X) ≅
      (W.mapHomologicalComplex (.up ℤ)).obj X :=
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (V ⋙ U)) (.up ℤ)).app X) ≪≫
      (NatIso.mapHomologicalComplex c (.up ℤ)).app X
  obtain ⟨cφ⟩ := cancellationComplexIso φ (V.obj N) P
  obtain ⟨cχ⟩ := cancellationComplexIso χ N P
  exact ⟨(U.mapHomologicalComplex (.up ℤ)).preimageIso
    (cφ ≪≫ d ≪≫ cχ.symm ≪≫ z.symm)⟩

end CoefficientTensor

private theorem quotient_layer_sequence
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (n : ℕ) (hn : 1 ≤ n) :
    let D := B ⧸ J ^ (n + 1)
    let A := B ⧸ J
    let E := B ⧸ J ^ n
    let a : D →+* A := Ideal.Quotient.factor (Ideal.pow_le_self (by omega))
    let e : D →+* E := Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))
    ∃ (Q : ModuleCat.{u} A) (_ : Module.Finite A Q)
      (f : (ModuleCat.restrictScalars a).obj Q ⟶ ModuleCat.of D D)
      (g : ModuleCat.of D D ⟶ (ModuleCat.restrictScalars e).obj (ModuleCat.of E E))
      (h : f ≫ g = 0), (ShortComplex.mk f g h).ShortExact := by
  dsimp only
  let D := B ⧸ J ^ (n + 1)
  let A := B ⧸ J
  let E := B ⧸ J ^ n
  let a : D →+* A := Ideal.Quotient.factor (Ideal.pow_le_self (by omega))
  let e : D →+* E := Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))
  let V := (J ^ n : Ideal B) ⧸ (J • ⊤ : Submodule B (J ^ n : Ideal B))
  have hfinite : Module.Finite B (J ^ n : Ideal B) := inferInstance
  have hV : Module.Finite B V := inferInstance
  have hVA : Module.Finite A V := Module.Finite.of_restrictScalars_finite B A V
  let Q : ModuleCat.{u} A := ModuleCat.of A V
  let l := J.powQuotPowSuccLinearEquivMapMkPowSuccPow n
  let f : (ModuleCat.restrictScalars a).obj Q ⟶ ModuleCat.of D D :=
    ModuleCat.ofHom (X := (ModuleCat.restrictScalars a).obj Q) (Y := ModuleCat.of D D)
      { toFun := fun x ↦ (l x).val
        map_add' := fun x y ↦ congrArg Subtype.val (l.map_add x y)
        map_smul' := by
          intro d x
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
          exact congrArg Subtype.val (l.map_smul r x) }
  let g : ModuleCat.of D D ⟶ (ModuleCat.restrictScalars e).obj (ModuleCat.of E E) :=
    ModuleCat.ofHom (X := ModuleCat.of D D)
      (Y := (ModuleCat.restrictScalars e).obj (ModuleCat.of E E))
      { toFun := e
        map_add' := e.map_add
        map_smul' := fun r x ↦ e.map_mul r x }
  have hf : Function.Injective f := by
    intro x y h
    exact l.injective (Subtype.ext h)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk (J ^ (n + 1)) b, rfl⟩
  have hex : Function.Exact f g := by
    intro d
    change e d = 0 ↔ ∃ x, (l x).val = d
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
    change Ideal.Quotient.mk (J ^ n) b = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hb
      have hd : Ideal.Quotient.mk (J ^ (n + 1)) b ∈
          Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ n) := Ideal.mem_map_of_mem _ hb
      exact ⟨l.symm ⟨_, hd⟩, congrArg Subtype.val (l.apply_symm_apply ⟨_, hd⟩)⟩
    · rintro ⟨x, hx⟩
      have hd := (l x).property
      rw [hx, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hd
      obtain ⟨c, hc, heq⟩ := hd
      have hbc : c - b ∈ J ^ (n + 1) := Ideal.Quotient.eq.mp heq
      have hbc' : c - b ∈ J ^ n := Ideal.pow_le_pow_right (by omega) hbc
      simpa only [sub_sub_cancel] using (J ^ n).sub_mem hc hbc'
  have hz : f ≫ g = 0 := by
    ext x
    exact (hex (f x)).2 ⟨x, rfl⟩
  refine ⟨Q, hVA, f, g, hz, ?_⟩
  have : Mono f := (ModuleCat.mono_iff_injective f).2 hf
  have : Epi g := (ModuleCat.epi_iff_surjective g).2 hg
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hex⟩

private theorem bounded_flat_representative
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T B))]
    (K : DerivedCategory (SheafOfModules.{u} (constantCoefficientRing T B)))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    ∃ P : CochainComplex (SheafOfModules.{u} (constantCoefficientRing T B)) ℤ,
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, IsFlat (P.X i)) ∧ P.IsKFlatTensor := by
  classical
  let G := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨b, hb⟩ := hK
  have hG : G.IsLE b := by
    apply (G.isLE_iff b).2
    intro i hi
    apply (HomologicalComplex.exactAt_iff_isZero_homology G i).2
    exact (hb i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors _ i).app G).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e)
  let := hG
  have : QuasiIso (G.ιTruncLE b) := by infer_instance
  obtain ⟨F, ε, hF⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    T ((constantSheaf T CommRingCat.{u}).obj (CommRingCat.of B)) b
  let X := ObjectProperty.FullSubcategory.mk
    (P := fun H : CochainComplex (SheafOfModules.{u} (constantCoefficientRing T B)) ℤ ↦
      ∀ i : ℤ, b < i → IsZero (H.X i)) (G.truncLE b)
    (fun i hi ↦ (G.truncLE b).isZero_of_isStrictlyLE b i hi)
  have hf := (hF X).2.2.2
  let := hf
  refine ⟨F.obj X, ⟨asIso (DerivedCategory.Q.map (ε.app X)) ≪≫
    asIso (DerivedCategory.Q.map (G.ιTruncLE b)) ≪≫ e⟩,
    ⟨b, (hF X).2.1⟩, (hF X).1, ?_⟩
  exact CochainComplex.isKFlat_of_boundedAbove_flat _ ⟨b, (hF X).2.1⟩ (hF X).1

private theorem leftDerived_model
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    [HasDerivedCategory.{w} V] [HasDerivedCategory.{w} W]
    (E : V ⥤ W) [E.Additive] (LF : DerivedCategory V ⥤ DerivedCategory W)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex V ℤ)
    [IsIso (ε.app ((HomotopyCategory.quotient V (.up ℤ)).obj P))] :
    Nonempty (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P) ≅
      LF.obj (DerivedCategory.Q.obj P)) := by
  exact ⟨((DerivedCategory.quotientCompQhIso W).app
    ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
  (DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P)).symm ≪≫
  (asIso (ε.app ((HomotopyCategory.quotient V (.up ℤ)).obj P))).symm ≪≫
  LF.mapIso ((DerivedCategory.quotientCompQhIso V).app P)⟩

private theorem reduction_model
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T B))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T D))]
    (P : CochainComplex (SheafOfModules.{u} (constantCoefficientRing T B)) ℤ)
    (hP : P.IsKFlatTensor) :
    ∃ (E : SheafOfModules.{u} (constantCoefficientRing T B) ⥤
        SheafOfModules.{u} (constantCoefficientRing T D))
      (ho : ∀ M, E.obj M = changeOfRings
        ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)) M)
      (_ : ∀ {M N} (a : M ⟶ N), E.map a = eqToHom (ho M) ≫
        changeOfRingsHom ((constantSheaf T CommRingCat.{u}).map
          (CommRingCat.ofHom f)) M a ≫ eqToHom (ho N).symm)
      (_ : E.Additive),
      Nonempty (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P) ≅
        (constantCoefficientScalarExtension T f).obj (DerivedCategory.Q.obj P)) := by
  classical
  let φ := (constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)
  let data := derivedChangeOfRings.{w, u} φ
  let E := data.choose
  obtain ⟨ho, hm, hadd, hdata⟩ := data.choose_spec
  let : E.Additive := hadd
  let LF : DerivedCategory (SheafOfModules.{u} (constantCoefficientRing T B)) ⥤
      DerivedCategory (SheafOfModules.{u} (constantCoefficientRing T D)) :=
    hdata.2.2.choose
  let ε : DerivedCategory.Qh ⋙ LF ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    hdata.2.2.choose_spec.choose
  have hε := hdata.2.2.choose_spec.choose_spec.2.2
  have := hε P hP
  obtain ⟨e⟩ := leftDerived_model E LF ε P
  exact ⟨E, ho, hm, hadd, ⟨e⟩⟩

private theorem reduction_model_raw
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T B))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T D))]
    (P : CochainComplex (SheafOfModules.{u} (constantCoefficientRing T B)) ℤ)
    (hP : P.IsKFlatTensor)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) :
    Nonempty (DerivedCategory.Q.obj
      (changeOfRingsComplex.{u, u}
        ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)) P) ≅
      (constantCoefficientScalarExtension T f).obj (DerivedCategory.Q.obj P)) ∧
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
      ((changeOfRingsComplex.{u, u}
        ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)) P).X i) := by
  obtain ⟨E, ho, hm, hE, ⟨e⟩⟩ := reduction_model T f P hP
  let := hE
  let φ := (constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)
  let q : (E.mapHomologicalComplex (.up ℤ)).obj P ≅ changeOfRingsComplex.{u, u} φ P :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (ho (P.X i))) (by
      intro i j hij
      symm
      change E.map (P.d i j) ≫ eqToHom (ho (P.X j)) =
        eqToHom (ho (P.X i)) ≫ changeOfRingsHom φ (P.X i) (P.d i j)
      rw [hm]
      simp
      rfl)
  refine ⟨⟨DerivedCategory.Q.mapIso q.symm ≪≫ e⟩, ?_⟩
  obtain ⟨b, hb⟩ := hb
  exact ⟨b, fun i hi ↦ (E.map_isZero (hb i hi)).of_iso
    ((HomologicalComplex.eval _ _ i).mapIso q).symm⟩

private theorem homology_bound
    {V : Type*} [Category V] [Abelian V] [HasDerivedCategory.{w} V]
    (P : CochainComplex V ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor V i).obj (DerivedCategory.Q.obj P)) := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun i hi ↦ ?_⟩
  exact ((P.sc i).isZero_homology_of_isZero_X₂ (hb i hi)).of_iso
    ((DerivedCategory.homologyFunctorFactors V i).app P)

private theorem constant_lisse
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B] (M : ModuleCat.{u} B) (hM : Module.Finite B M) :
    IsLocallyConstantFiniteTypeModules T B ((constantCoefficientModule T B).obj M) := by
  intro V
  exact ⟨⊤, T.top_mem V, fun _ _ _ ↦ ⟨M, hM, ⟨Iso.refl _⟩⟩⟩

private theorem constant_exact
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B] :
    PreservesFiniteLimits (constantCoefficientModule T B) ∧
      PreservesFiniteColimits (constantCoefficientModule T B) := by
  let := constant_preservesFiniteLimits (C := C) B
  let := constant_preservesFiniteColimits (C := C) B
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

private theorem zero_lisse
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    (F : SheafOfModules.{u} (constantCoefficientRing T B)) (hF : IsZero F) :
    IsLocallyConstantFiniteTypeModules T B F := by
  let c := constantCoefficientModule T B
  have := (constant_exact T B).2
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts c
  have : c.Additive := Functor.additive_of_preservesBinaryBiproducts c
  let e := hF.iso (c.map_isZero (isZero_zero (ModuleCat.{u} B)))
  have : Subsingleton (0 : ModuleCat.{u} B) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  have : Module.Finite B (0 : ModuleCat.{u} B) :=
    Module.Finite.of_surjective (0 : B →ₗ[B] (0 : ModuleCat.{u} B))
      (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
  exact lisse_of_iso T B e (constant_lisse T B 0 inferInstance)

private theorem finite_tensor_lisse
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    (N : ModuleCat.{u} B) (hN : Module.Finite B N)
    (P : CochainComplex (SheafOfModules.{u}
      (constantCoefficientRing T.toGrothendieck B)) ℤ)
    (hP : P.IsKFlatTensor)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hl : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck B (P.homology i)) :
    letI := monoidalCategory ((constantSheaf T.toGrothendieck CommRingCat.{u}).obj
      (CommRingCat.of B))
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck B
      ((((MonoidalCategory.tensorLeft
        ((constantCoefficientModule T.toGrothendieck B).obj N)).mapHomologicalComplex
          (.up ℤ)).obj P).homology i) := by
  let R := ((constantSheaf T.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B))
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensor_additivity R
  let A := SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)
  let M := (constantCoefficientModule T.toGrothendieck B).obj N
  let L := (HomologicalComplex.single A (.up ℤ) 0).obj M
  obtain ⟨F, s, hF, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution L
  have := hs
  have hLb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (L.X i) :=
    ⟨0, fun i hi ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  have hLl (i : ℤ) : IsLocallyConstantFiniteTypeModules T.toGrothendieck B
      (L.homology i) := by
    by_cases hi : i = 0
    · subst i
      exact lisse_of_iso T.toGrothendieck B
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M)
        (constant_lisse T.toGrothendieck B N hN)
    · exact zero_lisse T.toGrothendieck B _
        (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M i hi)
  have htot := locallyConstantFiniteType_derivedTensor T B
    (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj P)
    (homology_bound L hLb) (homology_bound P hb)
    (fun i ↦ lisse_of_iso T.toGrothendieck B
      ((DerivedCategory.homologyFunctorFactors A i).app L) (hLl i))
    (fun i ↦ lisse_of_iso T.toGrothendieck B
      ((DerivedCategory.homologyFunctorFactors A i).app P) (hl i))
    F P hF hP (asIso (DerivedCategory.Q.map s)) (Iso.refl _)
  let t := HomologicalComplex.mapBifunctorMap s (𝟙 P)
    (MonoidalCategory.curriedTensor A) (.up ℤ)
  have ht : QuasiIso t := by
    have hc := hP (CochainComplex.mappingCone s)
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic s).1 hs)
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic t).2
    intro i
    exact (hc i).of_iso
      (CochainComplex.mapBifunctorMappingCone₁Iso s P (MonoidalCategory.curriedTensor A))
  let := ht
  intro i
  let e := CochainComplex.mapBifunctorSingle₁Iso (MonoidalCategory.curriedTensor A) M P
  exact lisse_of_iso T.toGrothendieck B
    (((HomologicalComplex.homologyFunctor A (.up ℤ) i).mapIso e).symm ≪≫
      (asIso (HomologicalComplex.homologyMap t i)).symm) (htot i)

section TensorSequence

open MonoidalCategory

variable {V : Type*} [Category V] [Abelian V] [MonoidalCategory V]
  [MonoidalPreadditive V]

private noncomputable def tensorComplex (P : CochainComplex V ℤ) :
    V ⥤ CochainComplex V ℤ where
  obj N := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj P
  map f :=
    { f := fun i ↦ f ▷ P.X i
      comm' := fun i j _ ↦ (whisker_exchange f (P.d i j)).symm }
  map_id N := by ext i; change (𝟙 N) ▷ P.X i = 𝟙 _; simp
  map_comp f g := by ext i; simp

private theorem tensorComplex_additive (P : CochainComplex V ℤ) :
    (tensorComplex P).Additive := by
  constructor
  intro M N f g
  ext i
  exact (tensorRight (P.X i)).map_add

attribute [local instance] tensorComplex_additive

private theorem tensorComplex_shortExact (P : CochainComplex V ℤ)
    (hP : ∀ i : ℤ, exactFunctor V V (tensorRight (P.X i)))
    (S : ShortComplex V) (hS : S.ShortExact) :
    (S.map (tensorComplex P)).ShortExact := by
  have := tensorComplex_additive P
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have : PreservesFiniteLimits (tensorRight (P.X i)) := (hP i).1
  have : PreservesFiniteColimits (tensorRight (P.X i)) := (hP i).2
  exact hS.map_of_exact (tensorRight (P.X i))

private noncomputable def unitTensorComplexIso (P : CochainComplex V ℤ) :
    (tensorComplex P).obj (𝟙_ V) ≅ P :=
  (NatIso.mapHomologicalComplex (leftUnitorNatIso V) (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexIdIso V (.up ℤ)).app P

end TensorSequence

private theorem quotient_tensor_iso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D A : Type u} [CommRing B] [CommRing D] [CommRing A]
    (f : B →+* D) (g : D →+* A) (k : B →+* A) (h : g.comp f = k)
    (hf : Function.Surjective f) (N : ModuleCat.{u} A)
    (P : CochainComplex (SheafOfModules.{u} (constantCoefficientRing T B)) ℤ) :
    let R := (constantSheaf T CommRingCat.{u}).obj (CommRingCat.of D)
    let S := (constantSheaf T CommRingCat.{u}).obj (CommRingCat.of A)
    letI := monoidalCategory R
    letI := monoidalCategory S
    Nonempty
      ((((MonoidalCategory.tensorLeft ((constantCoefficientModule T D).obj
        ((ModuleCat.restrictScalars g).obj N))).mapHomologicalComplex (.up ℤ)).obj
          (changeOfRingsComplex.{u, u}
            ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)) P)) ≅
        (((restrictScalars (coefficientMap T g)).mapHomologicalComplex (.up ℤ)).obj
          (((MonoidalCategory.tensorLeft
            ((constantCoefficientModule T A).obj N)).mapHomologicalComplex (.up ℤ)).obj
              (changeOfRingsComplex.{u, u}
                ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom k)) P)))) := by
  let R := (constantSheaf T CommRingCat.{u}).obj (CommRingCat.of D)
  let S := (constantSheaf T CommRingCat.{u}).obj (CommRingCat.of A)
  let := monoidalCategory R
  let := monoidalCategory S
  let φ := (constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)
  let ψ := (constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom g)
  let χ := (constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom k)
  have hc : φ ≫ ψ = χ := by
    rw [← Functor.map_comp]
    exact congrArg ((constantSheaf T CommRingCat.{u}).map)
      (CommRingCat.hom_ext h)
  have : Presheaf.IsLocallySurjective T
      ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).map φ).hom :=
    coefficientMap_locallySurjective T f hf
  let q := constantRestrictionIso T g N
  let d := changeOfRingsComplex.{u, u} φ P
  obtain ⟨c⟩ := coefficientTensorIso φ ψ χ hc ((constantCoefficientModule T A).obj N) P
  exact ⟨(NatIso.mapHomologicalComplex
    ((MonoidalCategory.curriedTensor _).mapIso q) (.up ℤ)).app d ≪≫ c⟩

private theorem restriction_lisse_homology
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    (hf : Function.Surjective f)
    (P : CochainComplex (SheafOfModules.{u} (constantCoefficientRing T D)) ℤ)
    (hP : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T D (P.homology i)) :
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((((restrictScalars (coefficientMap T f)).mapHomologicalComplex (.up ℤ)).obj
        P).homology i) := by
  have := (restriction_exact (coefficientMap T f)).1
  have := (restriction_exact (coefficientMap T f)).2
  intro i
  exact lisse_of_iso T B ((P.sc i).mapHomologyIso (restrictScalars (coefficientMap T f)))
    (locallyConstantFiniteTypeModules_restrictScalars_surjective T f hf _ (hP i))

/-- The quotient triangle advances finite locally constant cohomology from J^n to
J^(n+1). Source: Stacks Project, Cohomology on Sites, Tag 094I
(auxiliary; not a blueprint node).

Proof: put D = B/J^(n+1) and Q = J^n/J^(n+1). Regard the exact coefficient
sequence 0 to Q to D to B/J^n to 0 as a sequence of D-modules. A flat K-flat
representative of K tensors it to a distinguished triangle of D-module complexes.
Its middle term computes the reduction modulo J^(n+1); its last term is the
restriction of the reduction modulo J^n. Balancing identifies the first term with
the restriction to D of the tensor of the reduction modulo J and the finite
B/J-module Q. The ideal J annihilates Q; generators of the finite ideal J^n
project to generators over B/J. This quotient ring is Noetherian. The reduction
modulo J is bounded above, by a bounded-above flat
replacement of K. Tag 094H gives finite locally constant cohomology for this tensor.
The two quotient homomorphisms D to B/J and D to B/J^n are surjective, so the
scalar-restriction theorem preserves their finite constant local models. Restriction
is exact and hence commutes with cohomology. The
previous reduction supplies the other outer term. Since D is Noetherian, the
proved triangle-closure theorem over D gives the middle term's finite locally
constant cohomology over D itself. This avoids descending B-module local models
back to D-module local models. -/
theorem locallyConstantFiniteTypeModules_reduction_succ
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    [∀ I : Ideal B, HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck (B ⧸ I)))]
    (K : DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk J)).obj K)))
    (n : ℕ) (hn : 1 ≤ n)
    (hprevious : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ n))).obj K))) :
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ (n + 1))
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ (n + 1)))).obj K)) := by
  classical
  let τ := T.toGrothendieck
  let D := B ⧸ J ^ (n + 1)
  let A := B ⧸ J
  let E := B ⧸ J ^ n
  let a : D →+* A := Ideal.Quotient.factor (Ideal.pow_le_self (by omega))
  let e : D →+* E := Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk (J ^ (n + 1)) b, rfl⟩
  have he : Function.Surjective e := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk (J ^ (n + 1)) b, rfl⟩
  have : IsNoetherianRing D :=
    isNoetherianRing_of_surjective B D _ Ideal.Quotient.mk_surjective
  have : IsNoetherianRing A :=
    isNoetherianRing_of_surjective B A _ Ideal.Quotient.mk_surjective
  obtain ⟨P, ⟨eP⟩, hb, hflat, hP⟩ := bounded_flat_representative τ B K hbounded
  let φ (I : Ideal B) := (constantSheaf τ CommRingCat.{u}).map
    (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let Pq (I : Ideal B) := changeOfRingsComplex.{u, u} (φ I) P
  have hmodel (I : Ideal B) : Nonempty (DerivedCategory.Q.obj (Pq I) ≅
      (constantCoefficientScalarExtension τ (Ideal.Quotient.mk I)).obj K) ∧
      ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((Pq I).X i) := by
    obtain ⟨⟨q⟩, hq⟩ := reduction_model_raw τ (Ideal.Quotient.mk I) P hP hb
    exact ⟨⟨q ≪≫ (constantCoefficientScalarExtension τ (Ideal.Quotient.mk I)).mapIso eP⟩,
      hq⟩
  let PD := Pq (J ^ (n + 1))
  let PA := Pq J
  let PE := Pq (J ^ n)
  let RD := (constantSheaf τ CommRingCat.{u}).obj (CommRingCat.of D)
  let RA := (constantSheaf τ CommRingCat.{u}).obj (CommRingCat.of A)
  let := monoidalCategory RD
  let := monoidalCategory RA
  let := symmetricCategory RD
  let := tensor_additivity RD
  have hD := changeOfRings_isKFlat_of_flat_terms.{u, u} (φ (J ^ (n + 1))) P hP hflat
  have hA := changeOfRings_isKFlat_of_flat_terms.{u, u} (φ J) P hP hflat
  have hlA (i : ℤ) : IsLocallyConstantFiniteTypeModules τ A (PA.homology i) :=
    lisse_of_iso τ A
      (((DerivedCategory.homologyFunctorFactors _ i).app PA).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso (hmodel J).1.some) (hmod i)
  have hlE (i : ℤ) : IsLocallyConstantFiniteTypeModules τ E (PE.homology i) :=
    lisse_of_iso τ E
      (((DerivedCategory.homologyFunctorFactors _ i).app PE).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso (hmodel (J ^ n)).1.some)
      (hprevious i)
  obtain ⟨N, hN, f, g, hz, hS⟩ := quotient_layer_sequence B J n hn
  let S₀ := ShortComplex.mk f g hz
  have := (constant_exact τ D).1
  have := (constant_exact τ D).2
  have := tensorComplex_additive PD
  let S := (S₀.map (constantCoefficientModule τ D)).map (tensorComplex PD)
  have hseq : S.ShortExact := tensorComplex_shortExact PD hD.2 _
    (hS.map_of_exact (constantCoefficientModule τ D))
  obtain ⟨q₁⟩ := quotient_tensor_iso τ (Ideal.Quotient.mk (J ^ (n + 1))) a
    (Ideal.Quotient.mk J) (by ext b; rfl) Ideal.Quotient.mk_surjective N P
  have h₁ (i : ℤ) : IsLocallyConstantFiniteTypeModules τ D (S.X₁.homology i) :=
    lisse_of_iso τ D ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso q₁)
      (restriction_lisse_homology τ a ha _
        (finite_tensor_lisse T A N hN PA hA.1 (hmodel J).2 hlA) i)
  let RE := (constantSheaf τ CommRingCat.{u}).obj (CommRingCat.of E)
  let := monoidalCategory RE
  let := symmetricCategory RE
  let := tensor_additivity RE
  obtain ⟨q₃⟩ := quotient_tensor_iso τ (Ideal.Quotient.mk (J ^ (n + 1))) e
    (Ideal.Quotient.mk (J ^ n)) (by ext b; rfl) Ideal.Quotient.mk_surjective
      (ModuleCat.of E E) P
  let uE := (tensorComplex PE).mapIso (constantUnitIso τ E) ≪≫ unitTensorComplexIso PE
  let vE := ((restrictScalars (coefficientMap τ e)).mapHomologicalComplex (.up ℤ)).mapIso uE
  have h₃ (i : ℤ) : IsLocallyConstantFiniteTypeModules τ D (S.X₃.homology i) :=
    lisse_of_iso τ D
      ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso (q₃ ≪≫ vE))
      (restriction_lisse_homology τ e he PE hlE i)
  have ht := locallyConstantFiniteTypeModules_of_distinguished τ D
    (DerivedCategory.triangleOfSES hseq) (DerivedCategory.triangleOfSES_distinguished hseq)
    (fun i ↦ lisse_of_iso τ D ((DerivedCategory.homologyFunctorFactors _ i).app S.X₁)
      (h₁ i))
    (fun i ↦ lisse_of_iso τ D ((DerivedCategory.homologyFunctorFactors _ i).app S.X₃)
      (h₃ i))
  let uD := (tensorComplex PD).mapIso (constantUnitIso τ D) ≪≫ unitTensorComplexIso PD
  let q₂ := DerivedCategory.Q.mapIso uD ≪≫ (hmodel (J ^ (n + 1))).1.some
  intro i
  exact lisse_of_iso τ D ((DerivedCategory.homologyFunctor _ i).mapIso q₂).symm (ht i)

end SheafOfModules
