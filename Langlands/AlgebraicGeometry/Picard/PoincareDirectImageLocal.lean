import Langlands.AlgebraicGeometry.Picard.PoincareDirectImageLocalAlgebra
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareTangentSectionsStatement
import Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsStatement
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSeparatedProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Langlands.Cohomology.PerfectModuleComplexBaseChange
import Langlands.AlgebraicGeometry.Modules.PerfectFibreVanishing
import Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingProof
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.Picard.DualSchemeTensor
import Langlands.AlgebraicGeometry.Picard.DualKernelPullback
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected

/-! # The perfect complex of the Poincaré bundle at the origin of the dual -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Langlands.AbelianScheme.PoincareDirectImage

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.Cohomology.ModuleComplex Langlands.Cohomology.DerivedPlus

attribute [local instance] HasDerivedCategory.standard

variable {K : Type u} [Field K] {A : AbelianScheme (Spec (CommRingCat.of K))}
  (hA : HasDualScheme A)

/-- The point of the dual at its origin. -/
def originPoint : (dualScheme A hA).left :=
  (dualOrigin A hA).left (IsLocalRing.closedPoint K)

/-- The Poincaré projection `A ×_K D ⟶ D`. -/
abbrev poincareProjection : ((baseChange (dualScheme A hA).hom).obj A).X.left ⟶
    (dualScheme A hA).left :=
  ((baseChange (dualScheme A hA).hom).obj A).X.hom

variable {hA} {V : (dualScheme A hA).left.Opens} (hV : IsAffineOpen V)

/-- The Poincaré family over the affine open `V`, as a scheme over `Spec Γ(D, V)`. -/
abbrev affineFamily : pullback (poincareProjection hA) hV.fromSpec ⟶ Spec Γ((dualScheme A hA).left, V) :=
  pullback.snd (poincareProjection hA) hV.fromSpec

/-- The Poincaré line bundle restricted to the family over `V`. -/
abbrev affinePoincare : LineBundle (pullback (poincareProjection hA) hV.fromSpec) :=
  (LineBundle.pullback (pullback.fst (poincareProjection hA) hV.fromSpec)).obj
    (poincareLineBundle A hA)

/-- The maximal ideal of `Γ(D, V)` at the origin. -/
abbrev originIdeal (hx : originPoint hA ∈ V) : Ideal Γ((dualScheme A hA).left, V) :=
  (hV.primeIdealOf ⟨originPoint hA, hx⟩).asIdeal

section Setup

variable (hA) in
/-- The origin of the dual is a closed immersion, being a section of the separated structure
morphism. -/
theorem isClosedImmersion_dualOrigin : IsClosedImmersion (dualOrigin A hA).left := by
  have : IsSeparated (dualScheme A hA).hom := fieldDualSchemeSeparated K A hA
  have h : (dualOrigin A hA).left ≫ (dualScheme A hA).hom = 𝟙 _ := Over.w (dualOrigin A hA)
  have : IsClosedImmersion ((dualOrigin A hA).left ≫ (dualScheme A hA).hom) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ (dualScheme A hA).hom

variable (hA) in
theorem range_dualOrigin : Set.range (dualOrigin A hA).left = {originPoint hA} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) z (IsLocalRing.closedPoint K)]
    rfl
  · rintro rfl
    exact ⟨_, rfl⟩

variable (hA) in
/-- The origin of the dual is a closed point. -/
theorem isClosed_originPoint : IsClosed ({originPoint hA} : Set (dualScheme A hA).left) := by
  rw [← range_dualOrigin hA]
  exact (isClosedImmersion_dualOrigin hA).isClosedEmbedding.isClosed_range

include hV in
/-- Sections of the dual over an affine open form a noetherian ring. -/
theorem isNoetherianRing_sections [LocallyOfFiniteType (dualScheme A hA).hom] :
    IsNoetherianRing Γ((dualScheme A hA).left, V) := by
  have : IsLocallyNoetherian (dualScheme A hA).left :=
    LocallyOfFiniteType.isLocallyNoetherian (dualScheme A hA).hom
  exact IsLocallyNoetherian.component_noetherian ⟨V, hV⟩

/-- The structure ring map `K ⟶ Γ(D, V)`. -/
def structureHom : CommRingCat.of K ⟶ Γ((dualScheme A hA).left, V) :=
  Spec.preimage (hV.fromSpec ≫ (dualScheme A hA).hom)

/-- The origin, as a point of `Spec Γ(D, V)`. -/
def originLift (hx : originPoint hA ∈ V) :
    Spec (CommRingCat.of K) ⟶ Spec Γ((dualScheme A hA).left, V) :=
  IsOpenImmersion.lift hV.fromSpec (dualOrigin A hA).left (by
    rw [range_dualOrigin hA, hV.range_fromSpec, Set.singleton_subset_iff]
    exact hx)

lemma originLift_fac (hx : originPoint hA ∈ V) :
    originLift hV hx ≫ hV.fromSpec = (dualOrigin A hA).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- Evaluation at the origin, `Γ(D, V) ⟶ K`. -/
def originEval (hx : originPoint hA ∈ V) : Γ((dualScheme A hA).left, V) ⟶ CommRingCat.of K :=
  Spec.preimage (originLift hV hx)

lemma structureHom_comp_originEval (hx : originPoint hA ∈ V) :
    structureHom hV ≫ originEval hV hx = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, structureHom, originEval, Spec.map_preimage, Spec.map_preimage,
    ← Category.assoc, originLift_fac, Spec.map_id]
  exact Over.w (dualOrigin A hA)

lemma originLift_closedPoint (hx : originPoint hA ∈ V) :
    originLift hV hx (IsLocalRing.closedPoint K) = hV.primeIdealOf ⟨originPoint hA, hx⟩ := by
  apply hV.fromSpec.isOpenEmbedding.injective
  rw [hV.fromSpec_primeIdealOf]
  change (originLift hV hx ≫ hV.fromSpec) (IsLocalRing.closedPoint K) = originPoint hA
  rw [originLift_fac]
  rfl

lemma ker_originEval (hx : originPoint hA ∈ V) :
    RingHom.ker (originEval hV hx).hom = originIdeal hV hx := by
  have h := congrArg PrimeSpectrum.asIdeal (originLift_closedPoint hV hx)
  rw [← Spec.map_preimage (originLift hV hx)] at h
  rw [originIdeal, ← h]
  change RingHom.ker _ = Ideal.comap (originEval hV hx).hom (IsLocalRing.maximalIdeal K)
  rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker]

/-- A ring map out of `Γ(D, V)` killing the origin ideal factors through evaluation at the
origin. -/
lemma originEval_comp_eq (hx : originPoint hA ∈ V) {T : CommRingCat.{u}}
    (φ : Γ((dualScheme A hA).left, V) ⟶ T) (hφ : ∀ b ∈ originIdeal hV hx, φ b = 0) :
    originEval hV hx ≫ structureHom hV ≫ φ = φ := by
  ext b
  have hb : b - (structureHom hV) ((originEval hV hx) b) ∈ originIdeal hV hx := by
    rw [← ker_originEval, RingHom.mem_ker, map_sub]
    change (originEval hV hx) b - (structureHom hV ≫ originEval hV hx) ((originEval hV hx) b) = 0
    rw [structureHom_comp_originEval]
    exact sub_self _
  have h := hφ _ hb
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

lemma spec_map_comp_fromSpec_eq (hx : originPoint hA ∈ V) {T : CommRingCat.{u}}
    (φ : Γ((dualScheme A hA).left, V) ⟶ T) (hφ : ∀ b ∈ originIdeal hV hx, φ b = 0) :
    Spec.map φ ≫ hV.fromSpec = Spec.map (structureHom hV ≫ φ) ≫ (dualOrigin A hA).left := by
  rw [← originLift_fac hV hx, originLift.eq_def]
  rw [← Spec.map_preimage (IsOpenImmersion.lift _ _ _), ← Category.assoc, ← Spec.map_comp]
  change Spec.map φ ≫ hV.fromSpec =
    Spec.map (originEval hV hx ≫ structureHom hV ≫ φ) ≫ hV.fromSpec
  rw [originEval_comp_eq hV hx φ hφ]

end Setup

section OriginTrivial

open Langlands.Scheme.Modules

variable {S : Scheme.{u}} (B : AbelianScheme S) (hB : HasDualScheme B)

set_option backward.isDefEq.respectTransparency.types false in
/-- If a morphism `q : X ⟶ A ×_S D` lies over a `T`-point of the dual that factors through the
origin, then `q^* P` is isomorphic to the structure sheaf of `X`. -/
theorem nonempty_pullback_poincare_iso_unit {T : Over S} {X : Scheme.{u}}
    (q : X ⟶ ((baseChange (dualScheme B hB).hom).obj B).X.left) (f : X ⟶ T.left)
    (h : q ≫ ((baseChange (dualScheme B hB).hom).obj B).X.hom =
      f ≫ ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin B hB).left) :
    Nonempty ((Scheme.Modules.pullback q).obj (poincareLineBundle B hB).obj ≅
      SheafOfModules.unit X.ringCatSheaf) := by
  let t := (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin B hB
  have hc := congrArg Subtype.val (dualPointClass_origin picardZeroPullback B hB T)
  obtain ⟨r⟩ := Quotient.exact hc
  have hw : t.left ≫ (dualScheme B hB).hom = T.hom := Over.w t
  let q₀ : X ⟶ pullback B.X.hom (dualScheme B hB).hom := q
  have h₀ : q₀ ≫ pullback.snd B.X.hom (dualScheme B hB).hom = f ≫ t.left := h
  let q' : X ⟶ (relativeSpace B.X.hom).obj T :=
    pullback.lift f (q₀ ≫ pullback.fst B.X.hom (dualScheme B hB).hom) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, h₀, Category.assoc, hw])
  have hq : q₀ ≫ (relativeSpaceSymmetry B.X.hom (dualScheme B hB)).inv =
      q' ≫ (relativeSpace B.X.hom).map t := by
    apply pullback.hom_ext
    · have hnat : (relativeSpace B.X.hom).map t ≫ pullback.fst (dualScheme B hB).hom B.X.hom =
          pullback.fst T.hom B.X.hom ≫ t.left := (relativeProjection B.X.hom).naturality t
      rw [Category.assoc, relativeSpaceSymmetry, pullbackSymmetry_inv_comp_fst, Category.assoc,
        hnat, h₀, ← Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, relativeSpaceSymmetry, pullbackSymmetry_inv_comp_snd, Category.assoc,
        relativeSpace_map_snd, pullback.lift_snd]
  let L₀ := (RigidifiedLineBundle.forget _).obj (poincareFamily B hB)
  exact ⟨(Scheme.Modules.pullbackComp q₀ _).app L₀.obj ≪≫
    (Scheme.Modules.pullbackCongr hq).app L₀.obj ≪≫
    ((Scheme.Modules.pullbackComp q' _).app L₀.obj).symm ≪≫
    (Scheme.Modules.pullback q').mapIso
      ((LineBundle.forget _).mapIso ((RigidifiedLineBundle.forget _).mapIso r)) ≪≫
    pullbackUnitIso q'⟩

end OriginTrivial

section Fibre

/-- Cohomology of a quasi-coherent module on a smooth proper scheme of relative dimension `g`
over a field vanishes above degree `g`. -/
theorem isZero_relativeCohomology_of_lt {T : Type u} [Field T] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of T)) (g : ℕ) [SmoothOfRelativeDimension g f] [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : g < n) :
    IsZero ((relativeCohomology f n).obj M) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian X := ⟨⟩
  have : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from f]; infer_instance⟩
  exact Langlands.AlgebraicGeometry.Modules.noetherianSeparatedQuasicoherentVanishing _ X f g
    (Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim T X f g inferInstance
      inferInstance) M inferInstance n hn

/-- Restricting scalars of a ring along a bijective ring map from a field gives a
one-dimensional vector space. -/
theorem finrank_restrictScalars_self {T S : Type u} [Field T] [CommRing S] (φ : T →+* S)
    (hφ : Function.Bijective φ) :
    Module.finrank T ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) = 1 := by
  let e : T →ₗ[T] (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) :=
    { toFun := fun t => (φ t : S)
      map_add' := fun a b => map_add φ a b
      map_smul' := fun a b => by
        change φ (a * b) = φ a * φ b
        exact map_mul φ a b }
  rw [← (LinearEquiv.ofBijective e hφ).finrank_eq, Module.finrank_self]

/-- On a smooth proper geometrically connected scheme over a field `T`, the global functions
form a one-dimensional `T`-vector space. -/
theorem finrank_relativeGlobalSections_unit {T : Type u} [Field T] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of T)) [Smooth f] [IsProper f] [GeometricallyConnected f] :
    Module.finrank T ((relativeGlobalSections f).obj (SheafOfModules.unit X.ringCatSheaf)) = 1 := by
  have : GeometricallyIntegral f :=
    Langlands.AbelianScheme.smoothGeometricIntegrality T X f inferInstance inferInstance
  have hb := bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected f
  have hs : Function.Bijective (structureRingHom f).hom := by
    rw [structureRingHom, CommRingCat.hom_comp]
    exact hb.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv)
  exact (((relativeGlobalSectionsIso f).app _).toLinearEquiv.finrank_eq).symm.trans
    (finrank_restrictScalars_self _ hs)

variable (g : ℕ) (hg : A.HasRelativeDimension g)

set_option backward.isDefEq.respectTransparency.types false in
include hg in
theorem smoothOfRelativeDimension_affineFamily :
    SmoothOfRelativeDimension g (affineFamily hV) :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension g) _ _
    (hasRelativeDimension_baseChange A g hg _)

set_option backward.isDefEq.respectTransparency.types false in
include hg in
/-- The homology of the base change of a perfect model to a field vanishes outside `[0, g]`. -/
theorem isZero_homology_baseChange_field (Kc : CochainComplex (ModuleCat.{u} Γ((dualScheme A hA).left, V)) ℤ)
    {T : Type u} [Field T] (φ : Γ((dualScheme A hA).left, V) ⟶ CommRingCat.of T)
    (e : DerivedCategory.Q.obj ((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc) ≅
        DerivedCategory.Plus.ι.obj
          ((derivedComplex (relativeGlobalSections
            (pullback.snd (affineFamily hV) (Spec.map φ)))).obj
              ((Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map φ))).obj
                (affinePoincare hV).obj)))
    (i : ℤ) (hi : i < 0 ∨ (g : ℤ) < i) :
    IsZero (((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc).homology i) := by
  rcases hi with hi | hi
  · refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ i).app _).symm
    exact IsZero.of_iso (isZero_homology_of_neg _ _ hi)
      ((DerivedCategory.homologyFunctor _ i).mapIso e)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, by omega⟩
    have : SmoothOfRelativeDimension g (affineFamily hV) :=
      smoothOfRelativeDimension_affineFamily hV g hg
    have : SmoothOfRelativeDimension g (pullback.snd (affineFamily hV) (Spec.map φ)) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension g) _ _ inferInstance
    have : IsProper (pullback.snd (affineFamily hV) (Spec.map φ)) :=
      MorphismProperty.pullback_snd (P := @IsProper) _ _
        (MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance)
    have : ((Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map φ))).obj
        (affinePoincare hV).obj).IsQuasicoherent :=
      (affinePoincare hV).property.isQuasicoherent_pullback _
    exact IsZero.of_iso (isZero_relativeCohomology_of_lt _ g _ n (by exact_mod_cast hi))
      (homologyIsoOfIsoDerivedComplex _ e n)

set_option backward.isDefEq.respectTransparency.types false in
include hg in
/-- The degree-zero homology of the base change of a perfect model to a field `T`, along a
ring map killing the origin ideal, is one-dimensional. -/
theorem finrank_homology_zero_baseChange_field (hx : originPoint hA ∈ V)
    (Kc : CochainComplex (ModuleCat.{u} Γ((dualScheme A hA).left, V)) ℤ)
    {T : Type u} [Field T] (φ : Γ((dualScheme A hA).left, V) ⟶ CommRingCat.of T)
    (hφ : ∀ b ∈ originIdeal hV hx, φ b = 0)
    (e : DerivedCategory.Q.obj ((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc) ≅
        DerivedCategory.Plus.ι.obj
          ((derivedComplex (relativeGlobalSections
            (pullback.snd (affineFamily hV) (Spec.map φ)))).obj
              ((Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map φ))).obj
                (affinePoincare hV).obj))) :
    Module.finrank T (((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc).homology 0) = 1 := by
  have : SmoothOfRelativeDimension g (affineFamily hV) :=
    smoothOfRelativeDimension_affineFamily hV g hg
  have : SmoothOfRelativeDimension g (pullback.snd (affineFamily hV) (Spec.map φ)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension g) _ _ inferInstance
  have : Smooth (pullback.snd (affineFamily hV) (Spec.map φ)) :=
    SmoothOfRelativeDimension.smooth g _
  have : IsProper (pullback.snd (affineFamily hV) (Spec.map φ)) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _
      (MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance)
  let q := pullback.fst (affineFamily hV) (Spec.map φ) ≫
    pullback.fst (poincareProjection hA) hV.fromSpec
  let Tk : Over (Spec (CommRingCat.of K)) := Over.mk (Spec.map (structureHom hV ≫ φ))
  have hsq : q ≫ ((baseChange (dualScheme A hA).hom).obj A).X.hom =
      pullback.snd (affineFamily hV) (Spec.map φ) ≫
        ((Over.homMk Tk.hom : Tk ⟶ Over.mk (𝟙 _)) ≫ dualOrigin A hA).left := by
    change (pullback.fst (affineFamily hV) (Spec.map φ) ≫
        pullback.fst (poincareProjection hA) hV.fromSpec) ≫ poincareProjection hA = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, spec_map_comp_fromSpec_eq hV hx φ hφ]
    rfl
  obtain ⟨u⟩ := nonempty_pullback_poincare_iso_unit A hA (T := Tk) q _ hsq
  have i2 : (Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map φ))).obj
      (affinePoincare hV).obj ≅ SheafOfModules.unit _ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫ u
  exact (homologyIsoOfIsoDerivedComplex _ e 0 ≪≫
    (relativeCohomologyZeroIso _).app _ ≪≫
      (relativeGlobalSections _).mapIso i2).toLinearEquiv.finrank_eq.trans
    (finrank_relativeGlobalSections_unit _)

end Fibre

section Tangent

/-- Global sections relative to `g ≫ Spec.map h` are those relative to `g`, with scalars
restricted along `h`. -/
def relativeGlobalSectionsCompSpecMapIso {X : Scheme.{u}} {R S : CommRingCat.{u}}
    (g : X ⟶ Spec S) (h : R ⟶ S) (M : X.Modules) :
    (relativeGlobalSections (g ≫ Spec.map h)).obj M ≅
      (ModuleCat.restrictScalars h.hom).obj ((relativeGlobalSections g).obj M) :=
  ((relativeGlobalSectionsIso (g ≫ Spec.map h)).app M).symm ≪≫
    ModuleCat.restrictScalarsComp'App h.hom (structureRingHom g).hom
      (structureRingHom (g ≫ Spec.map h)).hom (by
        rw [← CommRingCat.hom_comp]
        congr 1
        rw [structureRingHom, structureRingHom, Scheme.Hom.comp_appTop, ← Category.assoc,
          ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]) ((globalSections X).obj M) ≪≫
    (ModuleCat.restrictScalars h.hom).mapIso ((relativeGlobalSectionsIso g).app M)

/-- A ring, viewed through a ring isomorphism onto another ring, is free of rank one. -/
def restrictScalarsSelfIso {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S) ≅ ModuleCat.of R R :=
  let l : R ≃ₗ[R] (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S) :=
    { toFun := fun r => (e r : S)
      invFun := fun s => e.symm s
      map_add' := fun a b => map_add e a b
      map_smul' := fun a b => by
        change e (a * b) = e a * e b
        exact map_mul e a b
      left_inv := fun r => e.symm_apply_apply r
      right_inv := fun s => e.apply_symm_apply s }
  l.toModuleIso.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The tangent condition at the origin: for `m² ≤ J ⋖ m` in the local ring `R` of `D` at the
origin, the degree-zero homology of the perfect model over `R ⧸ J` is not free of rank one. -/
theorem isEmpty_homology_zero_quotient [IsAlgClosed K]
    (hTAN : AlgClosedFieldPoincareTangentSectionsStatement.{u})
    (hx : originPoint hA ∈ V)
    (Kc : CochainComplex (ModuleCat.{u} Γ((dualScheme A hA).left, V)) ℤ)
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra Γ((dualScheme A hA).left, V) R]
    [IsLocalization.AtPrime R (originIdeal hV hx)]
    (J : Ideal R) (hsq : maximalIdeal R ^ 2 ≤ J) (hcov : J ⋖ maximalIdeal R)
    (e : DerivedCategory.Q.obj ((Cohomology.ModuleComplex.baseChange (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (algebraMap Γ((dualScheme A hA).left, V) R))).hom).obj Kc) ≅
      DerivedCategory.Plus.ι.obj
        ((derivedComplex (relativeGlobalSections
          (pullback.snd (affineFamily hV) (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (algebraMap Γ((dualScheme A hA).left, V) R))))))).obj
            ((Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (algebraMap Γ((dualScheme A hA).left, V) R)))))).obj
              (affinePoincare hV).obj))) :
    IsEmpty ((((Cohomology.ModuleComplex.baseChange (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (algebraMap Γ((dualScheme A hA).left, V) R))).hom).obj Kc).homology 0) ≅
      ModuleCat.of (R ⧸ J) (R ⧸ J)) := by
  refine ⟨fun iso => ?_⟩
  have : (originIdeal hV hx).IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨originPoint hA, hx⟩ (isClosed_originPoint hA)
  let : Algebra K R := ((algebraMap Γ((dualScheme A hA).left, V) R).comp (structureHom hV).hom).toAlgebra
  have hev : (originEval hV hx).hom.comp (structureHom hV).hom = RingHom.id K := by
    rw [← CommRingCat.hom_comp, structureHom_comp_originEval]
    rfl
  have hres := bijective_algebraMap_residueField (S := R) (structureHom hV).hom
    (originEval hV hx).hom hev (originIdeal hV hx) (ker_originEval hV hx) rfl
  obtain ⟨ψ⟩ := nonempty_dualNumber_algEquiv hres J hsq hcov
  let φS : Γ((dualScheme A hA).left, V) ⟶ CommRingCat.of (R ⧸ J) := (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (algebraMap Γ((dualScheme A hA).left, V) R)))
  let eS : CommRingCat.of (DualNumber K) ≅ CommRingCat.of (R ⧸ J) :=
    ψ.toRingEquiv.toCommRingCatIso
  let t : Spec (CommRingCat.of (DualNumber K)) ⟶ (dualScheme A hA).left :=
    Spec.map eS.inv ≫ Spec.map φS ≫ hV.fromSpec
  have hcomp : structureHom hV ≫ φS ≫ eS.inv =
      CommRingCat.ofHom (algebraMap K (DualNumber K)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun k => ?_)
    change ψ.symm (Ideal.Quotient.mk J (algebraMap Γ((dualScheme A hA).left, V) R ((structureHom hV) k))) =
      algebraMap K (DualNumber K) k
    rw [← ψ.symm.commutes k]
    rfl
  have hT1 : t ≫ (dualScheme A hA).hom = dualNumberProjection K := by
    have h : hV.fromSpec ≫ (dualScheme A hA).hom = Spec.map (structureHom hV) :=
      (Spec.map_preimage _).symm
    change (Spec.map eS.inv ≫ Spec.map φS ≫ hV.fromSpec) ≫ (dualScheme A hA).hom = _
    rw [Category.assoc, Category.assoc, h, ← Spec.map_comp, ← Spec.map_comp, Category.assoc,
      hcomp]
    rfl
  have hfst : ∀ b ∈ originIdeal hV hx,
      (φS ≫ eS.inv ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) b = 0 := by
    intro b hb
    have ha : algebraMap Γ((dualScheme A hA).left, V) R b ∈ maximalIdeal R :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff R _ b).mpr hb
    have hJ : algebraMap Γ((dualScheme A hA).left, V) R b * algebraMap Γ((dualScheme A hA).left, V) R b ∈ J :=
      hsq (by rw [pow_two]; exact Ideal.mul_mem_mul ha ha)
    have hz : ψ.symm (Ideal.Quotient.mk J (algebraMap Γ((dualScheme A hA).left, V) R b)) *
        ψ.symm (Ideal.Quotient.mk J (algebraMap Γ((dualScheme A hA).left, V) R b)) = 0 := by
      rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hJ, map_zero]
    have h := congrArg TrivSqZeroExt.fst hz
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_zero] at h
    exact mul_self_eq_zero.mp h
  have hT2 : dualNumberAugmentation K ≫ t = (dualOrigin A hA).left := by
    have h := spec_map_comp_fromSpec_eq hV hx
      (φS ≫ eS.inv ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hfst
    have h1 : structureHom hV ≫ φS ≫ eS.inv ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom = 𝟙 _ := by
      rw [show structureHom hV ≫ φS ≫ eS.inv ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
          (structureHom hV ≫ φS ≫ eS.inv) ≫
            CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom by
        simp only [Category.assoc], hcomp]
      refine CommRingCat.hom_ext (RingHom.ext fun k => ?_)
      rfl
    rw [h1, Spec.map_id, Category.id_comp] at h
    rw [← h]
    simp only [t, dualNumberAugmentation, Spec.map_comp, Category.assoc]
  have hT3 : t ≠ dualNumberProjection K ≫ (dualOrigin A hA).left := by
    intro heq
    have ho : (dualOrigin A hA).left = Spec.map (originEval hV hx) ≫ hV.fromSpec := by
      rw [originEval, Spec.map_preimage, originLift_fac]
    have h2 : Spec.map eS.inv ≫ Spec.map φS =
        dualNumberProjection K ≫ Spec.map (originEval hV hx) := by
      apply (cancel_mono hV.fromSpec).mp
      rw [Category.assoc, Category.assoc, ← ho]
      exact heq
    rw [dualNumberProjection, ← Spec.map_comp, ← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    apply hcov.lt.not_ge
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (originIdeal hV hx) R,
      Ideal.map_le_iff_le_comap]
    intro b hb
    have hb0 : (originEval hV hx) b = 0 := by
      rw [← RingHom.mem_ker, ker_originEval]
      exact hb
    have h4 : ψ.symm (Ideal.Quotient.mk J (algebraMap _ R b)) =
        algebraMap K (DualNumber K) ((originEval hV hx) b) :=
      congrArg (fun φ => (CommRingCat.Hom.hom φ) b) h3
    rw [hb0, map_zero] at h4
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    exact ψ.symm.injective (h4.trans (map_zero _).symm)
  let gS := pullback.snd (affineFamily hV) (Spec.map φS)
  let q := pullback.fst (affineFamily hV) (Spec.map φS) ≫
    pullback.fst (poincareProjection hA) hV.fromSpec
  let eSpec : Spec (CommRingCat.of (R ⧸ J)) ≅ Spec (CommRingCat.of (DualNumber K)) :=
    { hom := Spec.map eS.hom
      inv := Spec.map eS.inv
      hom_inv_id := by rw [← Spec.map_comp, eS.inv_hom_id, Spec.map_id]
      inv_hom_id := by rw [← Spec.map_comp, eS.hom_inv_id, Spec.map_id] }
  have hpb : IsPullback q (gS ≫ Spec.map eS.hom) (poincareProjection hA) t := by
    have h12 := (IsPullback.of_hasPullback (affineFamily hV) (Spec.map φS)).paste_horiz
      (IsPullback.of_hasPullback (poincareProjection hA) hV.fromSpec)
    refine h12.of_iso (Iso.refl _) (Iso.refl _) eSpec (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [q]
    · simp [eSpec, gS]
    · simp
    · change (Spec.map φS ≫ hV.fromSpec) ≫ 𝟙 _ =
        Spec.map eS.hom ≫ Spec.map eS.inv ≫ Spec.map φS ≫ hV.fromSpec
      rw [← Category.assoc (Spec.map eS.hom), ← Spec.map_comp, eS.inv_hom_id, Spec.map_id,
        Category.id_comp, Category.comp_id]
  have isoS : (relativeGlobalSections gS).obj
      ((Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map φS))).obj
        (affinePoincare hV).obj) ≅ ModuleCat.of (R ⧸ J) (R ⧸ J) :=
    ((relativeCohomologyZeroIso gS).app _).symm ≪≫
      (homologyIsoOfIsoDerivedComplex _ e 0).symm ≪≫ iso
  have hiso : (relativeGlobalSections (gS ≫ Spec.map eS.hom)).obj
      ((Scheme.Modules.pullback q).obj (poincareLineBundle A hA).obj) ≅
        ModuleCat.of (DualNumber K) (DualNumber K) :=
    (relativeGlobalSections _).mapIso ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      relativeGlobalSectionsCompSpecMapIso gS eS.hom _ ≪≫
      (ModuleCat.restrictScalars eS.hom.hom).mapIso isoS ≪≫
      restrictScalarsSelfIso ψ.toRingEquiv
  exact (hTAN K A hA t ⟨⟨hT1, hT2⟩, hT3⟩ _ q (gS ≫ Spec.map eS.hom) hpb).false hiso

end Tangent

/-- The local computation at the origin: a perfect model over `Γ(D, V)` of the cohomology of the
Poincaré bundle, whose cohomology is supported at the origin, has cohomology only in degree `g`,
where it is the residue field of the origin. -/
theorem homology_of_perfectModel [IsAlgClosed K]
    (hAL : Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement.{u})
    (hTAN : AlgClosedFieldPoincareTangentSectionsStatement.{u})
    (g : ℕ) (hg : A.HasRelativeDimension g)
    (hsm : SmoothOfRelativeDimension g (dualScheme A hA).hom)
    (hx : originPoint hA ∈ V)
    (Kc : CochainComplex (ModuleCat.{u} Γ((dualScheme A hA).left, V)) ℤ) (hKc : IsStrictlyPerfect Kc)
    (hbc : ∀ (T : CommRingCat.{u}) (φ : Γ((dualScheme A hA).left, V) ⟶ T),
      Nonempty (DerivedCategory.Q.obj ((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc) ≅
        DerivedCategory.Plus.ι.obj
          ((derivedComplex (relativeGlobalSections
            (pullback.snd (affineFamily hV) (Spec.map φ)))).obj
              ((Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map φ))).obj
                (affinePoincare hV).obj))))
    (hsupp : ∀ f ∈ originIdeal hV hx, ∀ n : ℤ,
      IsZero (((Cohomology.ModuleComplex.baseChange (algebraMap Γ((dualScheme A hA).left, V) (Localization.Away f))).obj Kc).homology n)) :
    (∀ n : ℤ, n ≠ g → IsZero (Kc.homology n)) ∧
      Nonempty (Kc.homology (g : ℤ) ≅ ModuleCat.of Γ((dualScheme A hA).left, V) (Γ((dualScheme A hA).left, V) ⧸ originIdeal hV hx)) := by
  have : SmoothOfRelativeDimension g (dualScheme A hA).hom := hsm
  have : Smooth (dualScheme A hA).hom := SmoothOfRelativeDimension.smooth g _
  have : IsNoetherianRing Γ((dualScheme A hA).left, V) := isNoetherianRing_sections hV
  have hmax : (originIdeal hV hx).IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨originPoint hA, hx⟩ (isClosed_originPoint hA)
  let : Algebra Γ((dualScheme A hA).left, V)
      ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) :=
    (dualScheme A hA).left.presheaf.algebra_section_stalk ⟨originPoint hA, hx⟩
  have : IsLocalization.AtPrime ((dualScheme A hA).left.presheaf.stalk (originPoint hA))
      (originIdeal hV hx) := hV.isLocalization_stalk ⟨originPoint hA, hx⟩
  have : IsRegularLocalRing ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := (dualScheme A hA).hom) _
  have hdim : ringKrullDim ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) = g :=
    Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension K _ _ g hsm _
      (isClosed_originPoint hA)
  have hKloc : IsStrictlyPerfect ((Cohomology.ModuleComplex.baseChange (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).obj Kc) :=
    isStrictlyPerfect_baseChange _ hKc
  have h1 : ∀ i : ℤ, (i < 0 ∨ (g : ℤ) < i) →
      IsZero (((Cohomology.ModuleComplex.baseChange (algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA))))).obj
        ((Cohomology.ModuleComplex.baseChange (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).obj Kc)).homology i) := by
    intro i hi
    refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      ((baseChangeCompIso (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))
        (algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA))))).app Kc).symm)
    obtain ⟨e⟩ := hbc (CommRingCat.of (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA))))
      (CommRingCat.ofHom ((algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).comp
        (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))))
    exact isZero_homology_baseChange_field hV g hg Kc _ e i hi
  have h2 : Module.finrank (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))
      (((Cohomology.ModuleComplex.baseChange (algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA))))).obj
        ((Cohomology.ModuleComplex.baseChange (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).obj Kc)).homology 0) = 1 := by
    have hφ : ∀ b ∈ originIdeal hV hx,
        (CommRingCat.ofHom ((algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).comp
          (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA))))) b = 0 := by
      intro b hb
      change (algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))) (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) b) = 0
      rw [ResidueField.algebraMap_eq, residue_eq_zero_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (originIdeal hV hx) b).mpr hb
    obtain ⟨e⟩ := hbc (CommRingCat.of (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA))))
      (CommRingCat.ofHom ((algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).comp
        (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))))
    exact ((HomologicalComplex.homologyFunctor _ _ 0).mapIso
      ((baseChangeCompIso (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))
        (algebraMap ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) (ResidueField ((dualScheme A hA).left.presheaf.stalk (originPoint hA))))).app Kc).symm).toLinearEquiv.finrank_eq.trans
      (finrank_homology_zero_baseChange_field hV g hg hx Kc _ hφ e)
  have h3 : ∀ i : ℤ, ∃ N : ℕ, maximalIdeal ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) ^ N ≤ Module.annihilator ((dualScheme A hA).left.presheaf.stalk (originPoint hA))
      (((Cohomology.ModuleComplex.baseChange (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).obj Kc).homology i) :=
    exists_pow_le_annihilator_homology_localization (originIdeal hV hx) hKc hsupp
  have h4 : ∀ J : Ideal ((dualScheme A hA).left.presheaf.stalk (originPoint hA)), maximalIdeal ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) ^ 2 ≤ J → J ⋖ maximalIdeal ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) →
      IsEmpty (((Cohomology.ModuleComplex.baseChange (Ideal.Quotient.mk J)).obj
        ((Cohomology.ModuleComplex.baseChange (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))).obj Kc)).homology 0 ≅
          ModuleCat.of (((dualScheme A hA).left.presheaf.stalk (originPoint hA)) ⧸ J) (((dualScheme A hA).left.presheaf.stalk (originPoint hA)) ⧸ J)) := by
    intro J hsq hcov
    obtain ⟨e⟩ := hbc (CommRingCat.of (((dualScheme A hA).left.presheaf.stalk (originPoint hA)) ⧸ J))
      (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA)))))
    have hE := isEmpty_homology_zero_quotient hV hTAN hx Kc J hsq hcov e
    exact ⟨fun iso => hE.false (((HomologicalComplex.homologyFunctor _ _ 0).mapIso
      ((baseChangeCompIso (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA))) (Ideal.Quotient.mk J)).app Kc)) ≪≫ iso)⟩
  obtain ⟨hvan, ⟨hiso⟩⟩ := hAL ((dualScheme A hA).left.presheaf.stalk (originPoint hA)) g hdim _ hKloc h1 h2 h3 h4
  have hflat : (algebraMap Γ((dualScheme A hA).left, V) ((dualScheme A hA).left.presheaf.stalk (originPoint hA))).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (originIdeal hV hx).primeCompl)
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨N, hN⟩ := exists_pow_le_annihilator_homology (originIdeal hV hx) hKc hsupp n
    obtain ⟨e⟩ := nonempty_baseChange_homology_iso_of_flat _ hflat Kc n
    exact isZero_of_pow_le_annihilator (R := ((dualScheme A hA).left.presheaf.stalk (originPoint hA))) (originIdeal hV hx) _ hN
      (IsZero.of_iso (hvan n hn) e.symm)
  · obtain ⟨N, hN⟩ := exists_pow_le_annihilator_homology (originIdeal hV hx) hKc hsupp g
    obtain ⟨e⟩ := nonempty_baseChange_homology_iso_of_flat _ hflat Kc g
    exact nonempty_iso_quotient_of_pow_le_annihilator (R := ((dualScheme A hA).left.presheaf.stalk (originPoint hA))) (originIdeal hV hx) _ hN
      (e.symm ≪≫ hiso)

end Langlands.AbelianScheme.PoincareDirectImage
