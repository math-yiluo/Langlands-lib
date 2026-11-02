import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupTransportCovering
import Langlands.Representation.LocallyConstant.CompactAction
import Langlands.Topology.LocallyConstant.QuotientDescent
import Mathlib.CategoryTheory.Sites.Preserves

/-! # Full locally constant modules on the finite rational transport site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits Opposite Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]

namespace OpenSubgroupTransport

/-- The original labelled point map on the actual rational locus subspaces. -/
def Hom.locusMap {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    C(X.domain.obj.locus, Y.domain.obj.locus) where
  toFun x := ⟨ρ.toMonoidHom f.label • x.val, f.mapsTo x.val x.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (BanachSpectrum.comapContinuous
      (ρ.toMonoidHom f.label).inv.toBoundedRingHom).continuous.comp
        continuous_subtype_val

@[simp] theorem Hom.locusMap_val {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y)
    (x : X.domain.obj.locus) :
    (f.locusMap x).val = ρ.toMonoidHom f.label • x.val := rfl

@[simp] theorem Hom.locusMap_id (X : ρ.OpenSubgroupTransport)
    (x : X.domain.obj.locus) : (𝟙 X : X ⟶ X).locusMap x = x := by
  apply Subtype.ext
  simp

@[simp] theorem Hom.locusMap_comp {X Y Z : ρ.OpenSubgroupTransport}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.domain.obj.locus) :
    (f ≫ g).locusMap x = g.locusMap (f.locusMap x) := by
  apply Subtype.ext
  simp [mul_smul]

local instance locusCompactSpace (X : ρ.OpenSubgroupTransport) :
    CompactSpace X.domain.obj.locus :=
  isCompact_iff_compactSpace.mp (rationalRepresentation K P X.domain.obj).1.isCompact

/-- A finite point-image cover gives a quotient of the original compact
locus subspaces, including the empty cover. -/
theorem familyCovers_isQuotientMap {I : Type u} [Finite I]
    {Y : ρ.OpenSubgroupTransport} (D : I → ρ.OpenSubgroupTransport)
    (f : ∀ i, D i ⟶ Y) (hcover : FamilyCovers D f) :
    IsQuotientMap (fun x : (i : I) × (D i).domain.obj.locus => (f x.1).locusMap x.2) := by
  apply IsQuotientMap.of_surjective_continuous
  · intro x
    obtain ⟨i, y, hy, heq⟩ := hcover x.val x.property
    exact ⟨⟨i, ⟨y, hy⟩⟩, Subtype.ext heq⟩
  · exact continuous_sigma (fun i => (f i).locusMap.continuous)

/-- The original finite labelled covers detect local constancy. -/
theorem isLocallyConstant_iff_of_familyCovers {I : Type u} [Finite I]
    {Y : ρ.OpenSubgroupTransport} (D : I → ρ.OpenSubgroupTransport)
    (f : ∀ i, D i ⟶ Y) (hcover : FamilyCovers D f)
    {C : Type w} (q : Y.domain.obj.locus → C) :
    IsLocallyConstant q ↔ ∀ i, IsLocallyConstant (q ∘ (f i).locusMap) := by
  constructor
  · intro h i
    exact h.comp_continuous (f i).locusMap.continuous
  · intro h
    apply (Langlands.LocallyConstantQuotient.isLocallyConstant_iff _
      (familyCovers_isQuotientMap D f hcover) q).mpr
    intro s
    exact isOpen_sigma_iff.mpr (fun i => h i s)

/-- Pullback on the full function module combines the original labelled
geometric point map with the inverse coefficient operator. -/
def locallyConstantPullback (M : Rep.{w} R G)
    {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    LocallyConstant Y.domain.obj.locus M →ₗ[R] LocallyConstant X.domain.obj.locus M :=
  (LocallyConstant.mapₗ R (M.ρ f.label⁻¹)).comp
    (LocallyConstant.comapₗ R f.locusMap)

@[simp] theorem locallyConstantPullback_apply (M : Rep.{w} R G)
    {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y)
    (s : LocallyConstant Y.domain.obj.locus M) (x : X.domain.obj.locus) :
    locallyConstantPullback M f s x = M.ρ f.label⁻¹ (s (f.locusMap x)) := rfl

/-- All locally constant coefficient functions and every original labelled
arrow, without a smooth-submodule replacement. -/
def locallyConstantPresheaf (M : Rep.{w} R G) :
    (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ ModuleCat.{max u w} R where
  obj X := ModuleCat.of R (LocallyConstant X.unop.domain.obj.locus M)
  map f := ModuleCat.ofHom (locallyConstantPullback M f.unop)
  map_id X := by
    ext s x
    change M.ρ (𝟙 X.unop : X.unop ⟶ X.unop).label⁻¹
      (s ((𝟙 X.unop : X.unop ⟶ X.unop).locusMap x)) = s x
    simp
  map_comp f g := by
    ext s x
    change M.ρ (g.unop ≫ f.unop).label⁻¹
        (s ((g.unop ≫ f.unop).locusMap x)) =
      M.ρ g.unop.label⁻¹ (M.ρ f.unop.label⁻¹
        (s (f.unop.locusMap (g.unop.locusMap x))))
    simp [map_mul, mul_inv_rev]


/-- The underlying full function presheaf, displayed explicitly as sets. -/
abbrev locallyConstantTypePresheaf (M : Rep.{w} R G) :
    (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ Type (max u w) where
  obj X := LocallyConstant X.unop.domain.obj.locus M
  map f := TypeCat.ofHom (locallyConstantPullback M f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro s
    ext x
    change M.ρ (𝟙 X.unop : X.unop ⟶ X.unop).label⁻¹
      (s ((𝟙 X.unop : X.unop ⟶ X.unop).locusMap x)) = s x
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    ext x
    change M.ρ (g.unop ≫ f.unop).label⁻¹
        (s ((g.unop ≫ f.unop).locusMap x)) =
      M.ρ g.unop.label⁻¹ (M.ρ f.unop.label⁻¹
        (s (f.unop.locusMap (g.unop.locusMap x))))
    simp [map_mul, mul_inv_rev]

/-- Forgetting the constructed module structure keeps every function and map. -/
def locallyConstantForgetIso (M : Rep.{w} R G) :
    locallyConstantPresheaf (ρ := ρ) M ⋙ forget (ModuleCat.{max u w} R) ≅
      locallyConstantTypePresheaf (ρ := ρ) M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable (M : Rep.{w} R G) {Y : ρ.OpenSubgroupTransport} {S : Sieve Y}
  (p : Presieve.FamilyOfElements
    (locallyConstantTypePresheaf M) S.arrows)
  (hp : p.Compatible)

include hp in
/-- Matching on the original translated intersection identifies coefficient
values transported to a common target point. -/
theorem locallyConstantCompatible_apply {X Z : ρ.OpenSubgroupTransport}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : S f) (hg : S g)
    (x : X.domain.obj.locus) (z : Z.domain.obj.locus)
    (heq : f.locusMap x = g.locusMap z) :
    M.ρ f.label ((p f hf : LocallyConstant X.domain.obj.locus M) x) = M.ρ g.label ((p g hg : LocallyConstant Z.domain.obj.locus M) z) := by
  have hz : ρ.toMonoidHom (f.label⁻¹ * g.label) • z.val = x.val := by
    have h := congrArg Subtype.val heq
    change ρ.toMonoidHom f.label • x.val = ρ.toMonoidHom g.label • z.val at h
    simp only [map_mul, map_inv, mul_smul, ← h, inv_smul_smul]
  let q : (refinement f g).domain.obj.locus := ⟨x.val, by
    change x.val ∈ (X.domain.obj.inter
      (ρ.toMonoidHom (f.label⁻¹ * g.label) • Z.domain.obj)).locus
    rw [RationalData.locus_inter, locus_smul]
    exact ⟨x.property, z.val, z.property, hz⟩⟩
  have hleft : (refinementLeft f g).locusMap q = x := by
    apply Subtype.ext
    change ρ.toMonoidHom 1 • x.val = x.val
    simp
  have hright : (refinementRight f g).locusMap q = z := by
    apply Subtype.ext
    change ρ.toMonoidHom (g.label⁻¹ * f.label) • x.val = z.val
    have h := congrArg Subtype.val heq
    change ρ.toMonoidHom f.label • x.val = ρ.toMonoidHom g.label • z.val at h
    simp only [map_mul, map_inv, mul_smul, h, inv_smul_smul]
  have h := congrArg
    (fun s : LocallyConstant (refinement f g).domain.obj.locus M => s q)
    (hp (refinementLeft f g) (refinementRight f g) hf hg (refinement_comm f g))
  change M.ρ (refinementLeft f g).label⁻¹
      ((p f hf : LocallyConstant X.domain.obj.locus M) ((refinementLeft f g).locusMap q)) =
    M.ρ (refinementRight f g).label⁻¹
      ((p g hg : LocallyConstant Z.domain.obj.locus M) ((refinementRight f g).locusMap q)) at h
  rw [hleft, hright] at h
  change M.ρ (1 : G)⁻¹ ((p f hf : LocallyConstant X.domain.obj.locus M) x) =
    M.ρ (g.label⁻¹ * f.label)⁻¹ ((p g hg : LocallyConstant Z.domain.obj.locus M) z) at h
  have h' := congrArg (M.ρ f.label) h
  simpa [mul_inv_rev, map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc] using h'

include hp in
/-- Point coverage supplies the uniquely determined value, without choosing a
default coefficient or assuming a nonempty coefficient type. -/
theorem exists_locallyConstantSieveValue (hS : IsFiniteCovering S)
    (y : Y.domain.obj.locus) :
    ∃ c : M, ∀ (X : ρ.OpenSubgroupTransport) (f : X ⟶ Y) (hf : S f)
      (x : X.domain.obj.locus), f.locusMap x = y → c = M.ρ f.label ((p f hf : LocallyConstant X.domain.obj.locus M) x) := by
  obtain ⟨I, _, D, f, hf, hcover⟩ := hS
  obtain ⟨i, x, hx, hxy⟩ := hcover y.val y.property
  refine ⟨M.ρ (f i).label ((p (f i) (hf i) : LocallyConstant (D i).domain.obj.locus M) ⟨x, hx⟩), ?_⟩
  intro X g hg z hzy
  exact locallyConstantCompatible_apply M p hp (f i) g (hf i) hg ⟨x, hx⟩ z
    ((Subtype.ext hxy).trans hzy.symm)

/-- The compatible coefficient value at every original target point. -/
def locallyConstantSieveGlueFun (hS : IsFiniteCovering S) : Y.domain.obj.locus → M :=
  fun y => (exists_locallyConstantSieveValue M p hp hS y).choose

theorem locallyConstantSieveGlueFun_apply (hS : IsFiniteCovering S)
    {X : ρ.OpenSubgroupTransport} (f : X ⟶ Y) (hf : S f)
    (x : X.domain.obj.locus) :
    locallyConstantSieveGlueFun M p hp hS (f.locusMap x) =
      M.ρ f.label ((p f hf : LocallyConstant X.domain.obj.locus M) x) :=
  (exists_locallyConstantSieveValue M p hp hS (f.locusMap x)).choose_spec X f hf x rfl

/-- The finite quotient criterion proves that the actual glued function is
locally constant in the original target subspace topology. -/
def locallyConstantSieveGlue (hS : IsFiniteCovering S) :
    LocallyConstant Y.domain.obj.locus M where
  toFun := locallyConstantSieveGlueFun M p hp hS
  isLocallyConstant := by
    obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
    let : Finite I := hI
    apply (isLocallyConstant_iff_of_familyCovers D f hcover _).mpr
    intro i
    have he : (locallyConstantSieveGlueFun M p hp
        ⟨I, hI, D, f, hf, hcover⟩ ∘ (f i).locusMap) =
        fun x => M.ρ (f i).label ((p (f i) (hf i) : LocallyConstant (D i).domain.obj.locus M) x) := by
      funext x
      exact locallyConstantSieveGlueFun_apply M p hp _ (f i) (hf i) x
    rw [he]
    exact (p (f i) (hf i) : LocallyConstant (D i).domain.obj.locus M).isLocallyConstant.comp _

@[simp]
theorem locallyConstantSieveGlue_apply (hS : IsFiniteCovering S)
    {X : ρ.OpenSubgroupTransport} (f : X ⟶ Y) (hf : S f)
    (x : X.domain.obj.locus) :
    locallyConstantSieveGlue M p hp hS (f.locusMap x) =
      M.ρ f.label ((p f hf : LocallyConstant X.domain.obj.locus M) x) :=
  locallyConstantSieveGlueFun_apply M p hp hS f hf x

/-- The constructed section has all the original inverse-label restrictions. -/
theorem locallyConstantSieveGlue_isAmalgamation (hS : IsFiniteCovering S) :
    p.IsAmalgamation (locallyConstantSieveGlue M p hp hS) := by
  intro X f hf
  apply LocallyConstant.ext
  intro x
  change M.ρ f.label⁻¹
    (locallyConstantSieveGlue M p hp hS (f.locusMap x)) = (p f hf : LocallyConstant X.domain.obj.locus M) x
  rw [locallyConstantSieveGlue_apply M p hp hS f hf x]
  simp [← Module.End.mul_apply, ← map_mul]

/-- Original point coverage proves uniqueness among all locally constant
sections of the full module. -/
theorem locallyConstantSieveGlue_unique (hS : IsFiniteCovering S)
    (q : LocallyConstant Y.domain.obj.locus M) (hq : p.IsAmalgamation q) :
    q = locallyConstantSieveGlue M p hp hS := by
  ext y
  obtain ⟨I, _, D, f, hf, hcover⟩ := hS
  obtain ⟨i, x, hx, hxy⟩ := hcover y.val y.property
  have he := congrArg (fun s : LocallyConstant (D i).domain.obj.locus M => s ⟨x, hx⟩)
    (hq (f i) (hf i))
  change M.ρ (f i).label⁻¹ (q ((f i).locusMap ⟨x, hx⟩)) =
    (p (f i) (hf i) : LocallyConstant (D i).domain.obj.locus M) ⟨x, hx⟩ at he
  have hpnt : (f i).locusMap ⟨x, hx⟩ = y := Subtype.ext hxy
  have he' := congrArg (M.ρ (f i).label) he
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at he'
  rw [hpnt] at he'
  exact he'.trans (hpnt ▸ locallyConstantSieveGlue_apply M p hp
    ⟨I, ‹Finite I›, D, f, hf, hcover⟩ (f i) (hf i) ⟨x, hx⟩).symm

/-- Every matching family on every original finite covering sieve has a unique
amalgamation in the entire locally constant function set. -/
theorem locallyConstantTypePresheaf_isSheaf (M : Rep.{w} R G) :
    Presheaf.IsSheaf (finiteTopology ρ)
      (locallyConstantTypePresheaf (ρ := ρ) M) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro Y S hS p hp
  exact ⟨locallyConstantSieveGlue M p hp hS,
    locallyConstantSieveGlue_isAmalgamation M p hp hS,
    fun q hq => locallyConstantSieveGlue_unique M p hp hS q hq⟩


/-- Forgetting module structure retains the sheaf of all coefficient functions. -/
theorem locallyConstantForget_isSheaf (M : Rep.{w} R G) :
    Presheaf.IsSheaf (finiteTopology ρ)
      (locallyConstantPresheaf (ρ := ρ) M ⋙ forget (ModuleCat.{max u w} R)) :=
  (Presheaf.isSheaf_of_iso_iff (locallyConstantForgetIso M)).mpr
    (locallyConstantTypePresheaf_isSheaf M)

/-- The actual matching limits are reflected to modules, even when the group
and site universes are larger than the coefficient carrier universe. -/
theorem locallyConstantPresheaf_isSheaf (M : Rep.{w} R G) :
    Presheaf.IsSheaf (finiteTopology ρ) (locallyConstantPresheaf (ρ := ρ) M) := by
  let : ReflectsLimitsOfSize.{v, max u v} (forget (ModuleCat.{max u w} R)) := by
    refine { reflectsLimitsOfShape := ?_ }
    intro J _
    refine { reflectsLimit := ?_ }
    intro F
    refine { reflects := ?_ }
    intro c hc
    let : HasLimit (F ⋙ forget (ModuleCat.{max u w} R)) := ⟨_, hc⟩
    let : Small.{max u w} (F ⋙ forget (ModuleCat.{max u w} R)).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    let : HasLimit F := ModuleCat.hasLimit F
    let : PreservesLimit F (forget (ModuleCat.{max u w} R)) :=
      preservesLimit_of_preserves_limit_cone (ModuleCat.HasLimits.limitConeIsLimit F)
        (Types.Small.limitConeIsLimit _)
    let : ReflectsLimit F (forget (ModuleCat.{max u w} R)) :=
      reflectsLimit_of_reflectsIsomorphisms F _
    exact ⟨isLimitOfReflects _ hc⟩
  exact Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{max u w} R))
    (locallyConstantForget_isSheaf M)

/-- The full module sheaf on the original varying-open-subgroup transport site. -/
def locallyConstantSheaf (M : Rep.{w} R G) :
    Sheaf (finiteTopology ρ) (ModuleCat.{max u w} R) :=
  ⟨locallyConstantPresheaf M, locallyConstantPresheaf_isSheaf M⟩

/-- A coefficient intertwiner acts on every value of every original section. -/
def locallyConstantCoefficientMap {M N : Rep.{w} R G} (a : M ⟶ N) :
    locallyConstantPresheaf (ρ := ρ) M ⟶ locallyConstantPresheaf (ρ := ρ) N where
  app _ := ModuleCat.ofHom (LocallyConstant.mapₗ R a.hom.toLinearMap)
  naturality X Y f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change LocallyConstant.mapₗ R a.hom.toLinearMap
        (locallyConstantPullback M f.unop s) =
      locallyConstantPullback N f.unop (LocallyConstant.mapₗ R a.hom.toLinearMap s)
    apply LocallyConstant.ext
    intro x
    exact Rep.hom_comm_apply a f.unop.label⁻¹
      (LocallyConstant.toFun s (f.unop.locusMap x))

@[simp]
theorem locallyConstantCoefficientMap_apply {M N : Rep.{w} R G} (a : M ⟶ N)
    (X : ρ.OpenSubgroupTransport) (s : LocallyConstant X.domain.obj.locus M)
    (x : X.domain.obj.locus) :
    LocallyConstant.toFun
      ((locallyConstantCoefficientMap (ρ := ρ) a).app (op X) s) x = a.hom (s x) := rfl

/-- Full locally constant transport sheaves depend functorially on arbitrary
ambient algebraic representations and their actual intertwiners. -/
def locallyConstantSheafFunctor :
    Rep.{w} R G ⥤ Sheaf (finiteTopology ρ) (ModuleCat.{max u w} R) where
  obj M := locallyConstantSheaf M
  map a := ⟨locallyConstantCoefficientMap a⟩
  map_id M := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro x
    rfl

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
