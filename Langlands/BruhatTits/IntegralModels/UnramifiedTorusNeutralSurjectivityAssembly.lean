import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.BruhatTits.IntegralModels.RelativeComponentConstruction
import Langlands.GroupScheme.Torus.QuotientRationalSurjectivityStatement
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionStatement
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.CentralIsogeny.TorusLift
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.DimensionLEOneTorusCocycleVanishingProof
import Langlands.FieldTheory.HenselianDiscreteDimensionLEOneProof
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.IntegralModel.ConnectedGeneration
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.AdicCongruenceTopology
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothOpenMapProof
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Reduction of neutral lifting for exact sequences of tori (KP B.8.6) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.IntegralModels

/-- The four explicit prerequisites imply the unchanged neutral-lifting
statement for exact sequences of tori over the maximal unramified field. -/
def UnramifiedTorusNeutralSurjectivityAssemblyStatement : Prop :=
  ConnectedGenerationStatement.{u} →
  TorusQuotientRationalSurjectivityStatement.{u} →
  UnramifiedTorusNeutralFiniteGenerationStatement.{u} →
  TorusSurjectionIsogenySectionStatement.{u} →
  UnramifiedTorusNeutralSurjectivityStatement.{u}

namespace NeutralSurjectivity

/-- A subgroup of a finitely generated commutative group whose elements are
all killed by one positive exponent is finite. -/
theorem finite_subgroup_of_pow_eq_one {Q : Type*} [CommGroup Q] [Group.FG Q]
    (H : Subgroup Q) {n : ℕ} (hn : 0 < n) (hH : ∀ x ∈ H, x ^ n = 1) : Finite H := by
  have : Module.Finite ℤ (Additive Q) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hfg : (AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup H)).FG :=
    IsNoetherian.noetherian _
  rw [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at hfg
  have : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr ((Subgroup.fg_iff_add_fg H).mpr hfg)
  refine CommGroup.finite_of_fg_isMulTorsion H ?_
  intro x
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (by simpa using hH x x.2)⟩

/-- If finitely many elements and `J` generate a commutative group `G`, and
every `n`-th power of the image of a homomorphism `e` lies in `J`, then the
preimage of `J` under `e` has finite index. -/
theorem finiteIndex_comap_of_closure_sup {G A : Type*} [CommGroup G] [Group A]
    (e : A →* G) (J : Subgroup G) {s : Set G} (hs : s.Finite)
    (htop : Subgroup.closure s ⊔ J = ⊤) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ a, e a ^ n ∈ J) : (J.comap e).FiniteIndex := by
  let π : G →* G ⧸ J := QuotientGroup.mk' J
  have hQ : Group.FG (G ⧸ J) := by
    rw [Group.fg_iff]
    refine ⟨π '' s, ?_, hs.image _⟩
    have h := congrArg (Subgroup.map π) htop
    rwa [Subgroup.map_sup, MonoidHom.map_closure, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective J)] at h
  let g : A →* G ⧸ J := π.comp e
  have hker : g.ker = J.comap e := by
    ext a
    simp only [g, π, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  have : Finite g.range := finite_subgroup_of_pow_eq_one g.range hn (by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    simp only [g, π, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (by rw [map_pow]; exact hpow a))
  rw [← hker]
  exact Subgroup.finiteIndex_ker g

/-- The finite-index criterion transported along a surjective homomorphism:
if finitely many elements and `P` generate `G₀`, `f : G₀ → G` is surjective and
every `n`-th power of the image of `e` lies in `f(P)`, then the preimage of
`f(P)` under `e` has finite index. -/
theorem finiteIndex_comap_map_of_closure_sup {G₀ G A : Type*} [Group G₀] [CommGroup G]
    [Group A] (f : G₀ →* G) (hf : Function.Surjective f) (e : A →* G) (P : Subgroup G₀)
    {s : Set G₀} (hs : s.Finite) (htop : Subgroup.closure s ⊔ P = ⊤) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ a, e a ^ n ∈ P.map f) : ((P.map f).comap e).FiniteIndex := by
  refine finiteIndex_comap_of_closure_sup e (P.map f) (hs.image f) ?_ hn hpow
  have h := congrArg (Subgroup.map f) htop
  rwa [Subgroup.map_sup, MonoidHom.map_closure, Subgroup.map_top_of_surjective f hf] at h

/-- A surjective homomorphism of affine tori over a field whose kernel is a
torus is smooth: it is an fppf quotient by its smooth kernel. -/
theorem smooth_of_torus_kernel {k : Type u} [Field k]
    {B C : GroupScheme (Spec (CommRingCat.of k))} [IsAffine B.X.left] [IsAffine C.X.left]
    (hB : IsTorus B) (hC : IsTorus C) (q : B ⟶ C) (hq : Surjective q.hom.hom.left)
    (hker : IsTorus (kernel q)) : Smooth q.hom.hom.left := by
  have : Smooth B.X.hom := hB.smooth
  have : Smooth C.X.hom := hC.smooth
  have : Flat q.hom.hom.left := hB.flat_of_surjective_hom hC q hq
  have hqc : QuasiCompact (q.hom.hom.left ≫ C.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ C.X.hom
  have hlft : LocallyOfFiniteType (q.hom.hom.left ≫ C.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFiniteType q.hom.hom.left := locallyOfFiniteType_of_comp _ C.X.hom
  have : IsLocallyNoetherian C.X.left := LocallyOfFiniteType.isLocallyNoetherian C.X.hom
  have : LocallyOfFinitePresentation q.hom.hom.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hqf : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q :=
    ⟨inferInstance, hq, inferInstance, rfl⟩
  exact hqf.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hker.smooth

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- For a model homomorphism `ψ` over `f`, the image of `ψ` on integral
sections is the preimage of the image under `f` of the source integral points. -/
theorem range_map_eq_comap {G H : GroupScheme (Spec (CommRingCat.of K))} {f : G ⟶ H}
    {M : IntegralModel R K G} {N : IntegralModel R K H} (ψ : M.Hom N f) :
    (rationalPoints.map ψ.hom).range =
      (M.integralPoints.map (rationalPoints.map f)).comap N.integralPointMap := by
  ext c
  constructor
  · rintro ⟨b, rfl⟩
    change N.integralPointMap (rationalPoints.map ψ.hom b) ∈
      M.integralPoints.map (rationalPoints.map f)
    rw [ψ.integralPointMap_naturality b]
    exact Subgroup.mem_map_of_mem _ ⟨b, rfl⟩
  · intro hc
    obtain ⟨g, ⟨b, rfl⟩, hg⟩ := hc
    refine ⟨b, N.integralPointMap_injective ?_⟩
    rw [ψ.integralPointMap_naturality b]
    exact hg

/-- If `s ≫ q = [n]` and `s` extends to a model homomorphism `σ`, then the
`n`-th power of every integral point of the target model of `q` lies in the
image under `q` of the integral points of the source model. -/
theorem pow_mem_map_of_section {B C : CommGroupScheme (Spec (CommRingCat.of K))}
    {q : B.toGrp ⟶ C.toGrp} {s : C.toGrp ⟶ B.toGrp} {n : ℕ}
    (hs : s ≫ q = multiplication C.toGrp (n : ℤ))
    {MB : IntegralModel R K B.toGrp} {MC : IntegralModel R K C.toGrp} (σ : MC.Hom MB s)
    (a : MC.integralSections) :
    MC.integralPointMap a ^ n ∈ MB.integralPoints.map (rationalPoints.map q) := by
  have hsq : s.hom.hom ≫ q.hom.hom = (multiplication C.toGrp (n : ℤ)).hom.hom := by
    rw [← Grp.comp_hom_hom, hs]
  refine ⟨rationalPoints.map s (MC.integralPointMap a),
    σ.map_mem_integralPoints ⟨a, rfl⟩, ?_⟩
  change (MC.integralPointMap a ≫ s.hom.hom) ≫ q.hom.hom = MC.integralPointMap a ^ n
  rw [Category.assoc, hsq, points_multiplication, zpow_natCast]

/-- Over the maximal unramified extension, the image under a smooth
homomorphism of affine groups of the integral points of a model contains the
generic image of a positive congruence kernel of any target model. -/
theorem exists_sectionCongruenceKernel_le_comap (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B C : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffine B.X.left] [IsAffine C.X.left] (q : B ⟶ C) [Smooth q.hom.hom.left]
    (MB : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) B)
    (MC : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) C) :
    ∃ m : ℕ+, ConnectedGeneration.sectionCongruenceKernel MC.group m ≤
      (MB.integralPoints.map (rationalPoints.map q)).comap MC.integralPointMap := by
  let : TopologicalSpace (inertiaFixedField F) := fixedFieldTopology F
  let : TopologicalSpace (rationalPoints B) :=
    rationalPointTopology (inertiaFixedField F) B.X
  let : TopologicalSpace (rationalPoints C) :=
    rationalPointTopology (inertiaFixedField F) C.X
  have hPB : IsOpen (MB.integralPoints : Set (rationalPoints B)) :=
    IntegralModel.isOpen_integralPoints_unramified F MB
  have hJ : IsOpen ((MB.integralPoints.map (rationalPoints.map q) :
      Subgroup (rationalPoints C)) : Set (rationalPoints C)) := by
    have h := isOpenMap_rationalPoint_of_smooth F henselianSmoothRationalPointOpenMap
      B.X C.X q.hom.hom _ hPB
    rw [Subgroup.coe_map]
    exact h
  obtain ⟨m, hm⟩ := IntegralModel.congruenceSubgroupAt_cofinal_unramified F MC _
    (hJ.mem_nhds (Subgroup.one_mem _))
  exact ⟨m, fun x hx => hm ⟨x, hx, rfl⟩⟩

end NeutralSurjectivity

set_option maxHeartbeats 400000 in
open NeutralSurjectivity in
/-- KP Corollary B.8.6 over the maximal unramified extension, from rational
surjectivity of torus quotients, finite generation modulo neutral integral
points, isogeny sections of torus surjections and KP Lemma A.4.26. -/
theorem unramifiedTorusNeutralSurjectivityAssembly :
    UnramifiedTorusNeutralSurjectivityAssemblyStatement.{u} := by
  intro hgen hrat hfg hsec F _ _ _ _ B C _ _ hB hC q hq hker DB DC hDB hDC
  obtain ⟨hdvr, hhens, hsep⟩ := fixedFieldIntegers_strictHenselian F
  have hres : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
    let := (residueToFixedField F).toAlgebra
    let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
      fixedFieldResidueIsAlgClosure F
    exact IsAlgClosure.isAlgClosed 𝓀[F]
  have : GeometricallyConnected DB.neutral.group.X.hom := DB.neutral_geometricallyConnected
  have : GeometricallyConnected DC.neutral.group.X.hom := DC.neutral_geometricallyConnected
  have hDBn : DB.neutral.integralPoints ≤
      characterValuationKernel (fixedFieldValuation F) B.toGrp := by
    rw [← DB.neutralPoints_eq, ← hDB]
    exact DB.neutralPoints_le_full
  have hDCn : DC.neutral.integralPoints ≤
      characterValuationKernel (fixedFieldValuation F) C.toGrp := by
    rw [← DC.neutralPoints_eq, ← hDC]
    exact DC.neutralPoints_le_full
  -- The map `q` and an isogeny section `s` extend to the neutral models.
  obtain ⟨φ⟩ := IntegralModel.smoothHomExtension (fixedFieldIntegers F) (inertiaFixedField F)
    B.toGrp C.toGrp q DB.neutral DC.full DB.neutral_smooth (fun g hg => by
      rw [hDC]
      exact map_characterValuationKernel_le (fixedFieldValuation F) q
        (Subgroup.mem_map_of_mem _ (hDBn hg)))
  let ψ := DC.toNeutral φ
  obtain ⟨n, hn, s, hs⟩ := hsec (inertiaFixedField F) B C hB hC q hq
  obtain ⟨φs⟩ := IntegralModel.smoothHomExtension (fixedFieldIntegers F) (inertiaFixedField F)
    C.toGrp B.toGrp s DC.neutral DB.full DC.neutral_smooth (fun g hg => by
      rw [hDB]
      exact map_characterValuationKernel_le (fixedFieldValuation F) s
        (Subgroup.mem_map_of_mem _ (hDCn hg)))
  have hI := range_map_eq_comap ψ
  have hgen_eq : ConnectedGeneration.generatedImages (fun _ : Fin 1 => ψ.hom) =
      (rationalPoints.map ψ.hom).range :=
    iSup_const
  -- The image of `ψ` has finite index.
  have hcoc : HasTrivialTorusCocycles (inertiaFixedField F) :=
    dimensionLEOneTorusCocycleVanishing _
      (Langlands.FieldTheory.henselianDiscreteDimensionLEOne _
        (MaximalUnramified.valuation F) (MaximalUnramified.valuation_surjective F)
        (MaximalUnramified.valuationSubring_isHenselian F)
        (MaximalUnramified.residueField_isAlgClosed F))
  have hsurj := hrat (inertiaFixedField F) hcoc B.toGrp C.toGrp hB hC q hq hker
  obtain ⟨S, hSfin, hStop⟩ := hfg F B.toGrp hB DB hDB
  have hfin := finiteIndex_comap_map_of_closure_sup (rationalPoints.map q) hsurj
    DC.neutral.integralPointMap DB.neutral.integralPoints hSfin hStop hn
    (pow_mem_map_of_section hs (DB.toNeutral φs))
  -- A congruence kernel lies in the image of `ψ`.
  have : Smooth q.hom.hom.left := smooth_of_torus_kernel hB hC q hq hker
  obtain ⟨m, hm⟩ := exists_sectionCongruenceKernel_le_comap F q DB.neutral DC.neutral
  -- KP Lemma A.4.26 for the neutral model of `C`.
  have hall := hgen (fixedFieldIntegers F) DC.neutral.group DC.neutral_smooth 1
    (fun _ => DB.neutral.group) (fun _ => DB.neutral_smooth) (fun _ => inferInstance)
    (fun _ => ψ.hom) (by rw [hgen_eq, hI]; exact hfin) ⟨m, by rw [hgen_eq, hI]; exact hm⟩
    DC.neutral.group (𝟙 _) (isRelativeIdentityComponent_id_of_geometricallyConnected _)
  rintro _ ⟨c, rfl⟩
  have hc : c ∈ (rationalPoints.map ψ.hom).range := by
    rw [← hgen_eq, hall]
    exact ⟨c, Category.comp_id c⟩
  rw [hI] at hc
  exact hc

end Langlands.BruhatTits.IntegralModels
