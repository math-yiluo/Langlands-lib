import Langlands.AlgebraicGeometry.Picard.DualNumberDeformationH1
import Langlands.AlgebraicGeometry.Picard.DualNumberScaling

/-! # Actual epsilon scaling of first-order line-bundle deformations

Pulling back along the actual scaling endomorphism `scale f c` of the dual-number thickening
sends the bundle glued from the unit cocycle `1 + ε z` to the bundle glued from `1 + ε (c z)`.
On deformation classes it therefore corresponds, under `deformationH1AddEquiv`, to
multiplication by `c` on actual derived `H¹`.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

namespace CocycleGluing

variable {X : Scheme.{u}} {ι : Type u} {T T' : ι → X.Opens}

/-- On a smaller family `T' i ≤ T i`, the restricted local generators of `glued g` are frames. -/
lemma isFrameOn_genSec_of_le (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (hle : ∀ i, T' i ≤ T i) (i : ι) :
    Scheme.Modules.IsFrameOn (genSec g hg i (hle i)) (T' i) := by
  intro W hWU _
  rw [map_genSec g hg i hWU (hle i)]
  exact smul_genSec_bijective g hg i _

/-- The restricted local generators have the restricted transition functions. -/
lemma isTransition_genSec_of_le (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (hle : ∀ i, T' i ≤ T i) (g' : ∀ i j : ι, (Γ(X, T' i ⊓ T' j))ˣ)
    (hres : ∀ i j, X.presheaf.map (homOfLE (inf_le_inf (hle i) (hle j))).op
      (g i j : Γ(X, T i ⊓ T j)) = g' i j) :
    IsTransition (M := glued g) (fun i ↦ genSec g hg i (hle i)) g' := by
  intro i j
  rw [map_genSec g hg j _ (hle j), map_genSec g hg i _ (hle i),
    genSec_eq_smul_genSec hg (inf_le_left.trans (hle i)) (inf_le_right.trans (hle j))]
  exact congrArg (fun r ↦ r • genSec g hg i (inf_le_left.trans (hle i))) (hres i j)

/-- Gluing on a smaller covering family `T' i ≤ T i` with the restricted cocycle gives the same
sheaf: the isomorphism is `frameIso` for the restricted local generators of `glued g`. -/
noncomputable def shrinkIso (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (hle : ∀ i, T' i ≤ T i) (hT' : (⨆ i, T' i) = ⊤) (g' : ∀ i j : ι, (Γ(X, T' i ⊓ T' j))ˣ)
    (hres : ∀ i j, X.presheaf.map (homOfLE (inf_le_inf (hle i) (hle j))).op
      (g i j : Γ(X, T i ⊓ T j)) = g' i j) :
    glued g ≅ glued g' :=
  frameIso (isFrameOn_genSec_of_le g hg hle) (isTransition_genSec_of_le g hg hle g' hres) hT'

/-- `shrinkIso` sends the local generator of `glued g` over `V ≤ T' i` to that of `glued g'`. -/
lemma shrinkIso_hom_app_genSec (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (hle : ∀ i, T' i ≤ T i) (hT' : (⨆ i, T' i) = ⊤) (g' : ∀ i j : ι, (Γ(X, T' i ⊓ T' j))ˣ)
    (hres : ∀ i j, X.presheaf.map (homOfLE (inf_le_inf (hle i) (hle j))).op
      (g i j : Γ(X, T i ⊓ T j)) = g' i j) (hg' : IsCocycle g') (i : ι) {V : X.Opens}
    (hV : V ≤ T' i) :
    (shrinkIso g hg hle hT' g' hres).hom.app V (genSec g hg i (hV.trans (hle i))) =
      genSec g' hg' i hV := by
  rw [← map_genSec g hg i hV (hle i)]
  exact frameIso_hom_app_frame _ _ hT' hg' i hV

end CocycleGluing

namespace DualNumberThickening

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Actual epsilon scaling preserves every inverse-image open of the thickening. -/
lemma scale_preimage_projection (c : k) (U : X.Opens) :
    scale f c ⁻¹ᵁ (projection f ⁻¹ᵁ U) = projection f ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, scale_projection]

section Bundle

variable {ι : Type u} (T : ι → X.Opens)

/-- On the original inverse-image overlaps, the actual pullback along `scale f c` of the unit
cochain `1 + ε z` is the unit cochain `1 + ε w` of the scaled coefficients `w = c z`. -/
lemma res_pullbackCocycle_scale_unitCochain (c : k) (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hwz : ∀ i j, w i j = baseSectionMap f (T i ⊓ T j) c * z i j) (i j : ι) :
    (thickening f).presheaf.map (homOfLE (inf_le_inf
        (scale_preimage_projection f c (T i)).ge (scale_preimage_projection f c (T j)).ge)).op
      (CocycleGluing.pullbackCocycle (scale f c) (unitCochain f T z) i j :
        Γ(thickening f, scale f c ⁻¹ᵁ thickenedOpens f T i ⊓
          scale f c ⁻¹ᵁ thickenedOpens f T j)) =
      (unitCochain f T w i j : Γ(thickening f, thickenedOpens f T i ⊓ thickenedOpens f T j)) := by
  refine (CocycleGluing.res_pullbackCocycle (scale f c) (unitCochain f T z) _).trans ?_
  change scaleSectionMap f c (T i ⊓ T j) (coefficientUnit f (T i ⊓ T j) (z i j) :
      Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j))) =
    (coefficientUnit f (T i ⊓ T j) (w i j) : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j)))
  rw [hwz i j]
  exact congrArg Units.val (scaleSectionMap_coefficientUnit f c (T i ⊓ T j) (z i j))

variable (hT : (⨆ i, T i) = ⊤)

/-- The actual pullback along epsilon scaling `scale f c` of the bundle glued from `1 + ε z` is
the bundle glued from `1 + ε w`, for `w = c z`: the pullback isomorphism of glued bundles
followed by `shrinkIso` from the cover `scale f c ⁻¹ᵁ (projection f ⁻¹ᵁ T i)` to the equal
cover `projection f ⁻¹ᵁ T i`. -/
def scaleCocycleBundleIso (c : k) (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z)
    (hwz : ∀ i j, w i j = baseSectionMap f (T i ⊓ T j) c * z i j) :
    (Scheme.Modules.pullback (scale f c)).obj (CocycleGluing.glued (unitCochain f T z)) ≅
      CocycleGluing.glued (unitCochain f T w) :=
  CocycleGluing.pullbackIso (scale f c) (unitCochain f T z)
      ((projection f).iSup_preimage_eq_top hT) ((isCocycle_unitCochain_iff f T z).mpr hz) ≪≫
    CocycleGluing.shrinkIso _ (((isCocycle_unitCochain_iff f T z).mpr hz).pullback (scale f c))
      (fun i ↦ (scale_preimage_projection f c (T i)).ge)
      ((projection f).iSup_preimage_eq_top hT) (unitCochain f T w)
      (res_pullbackCocycle_scale_unitCochain f T c z w hwz)

/-- Generator formula: the pulled-back local generator of the bundle of `z` over
`V ≤ projection f ⁻¹ᵁ T i` goes to the local generator of the bundle of `w`. -/
lemma scaleCocycleBundleIso_hom_app_genSec (c : k) (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z)
    (hw : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T w)
    (hwz : ∀ i j, w i j = baseSectionMap f (T i ⊓ T j) c * z i j) (i : ι)
    {V : (thickening f).Opens} (hV : V ≤ thickenedOpens f T i) :
    (scaleCocycleBundleIso f T hT c z w hz hwz).hom.app (scale f c ⁻¹ᵁ V)
        (Scheme.Modules.pullbackLocalSection (scale f c)
          (CocycleGluing.genSec (unitCochain f T z) ((isCocycle_unitCochain_iff f T z).mpr hz)
            i hV)) =
      CocycleGluing.genSec (unitCochain f T w) ((isCocycle_unitCochain_iff f T w).mpr hw) i
        (((scale f c).preimage_mono hV).trans (scale_preimage_projection f c (T i)).le) := by
  rw [scaleCocycleBundleIso, Iso.trans_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, CocycleGluing.pullbackIso_hom_app_genSec]
  exact CocycleGluing.shrinkIso_hom_app_genSec _ _ _ _ _ _ _ i _

end Bundle

section Classes

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Actual pullback along epsilon scaling preserves triviality of the zero-section pullback,
since `closedPoint f ≫ scale f c = closedPoint f`. -/
lemma pullbackHom_scale_mem (c : k) (q : DeformationClasses preservation f) :
    LineBundle.pullbackHom preservation (scale f c) q.1 ∈ DeformationClasses preservation f := by
  refine MonoidHom.mem_ker.mpr ?_
  rw [LineBundle.pullbackHom_comp_eq preservation (closedPoint f) (scale f c)
    (closedPoint_scale f c)]
  exact MonoidHom.mem_ker.mp q.2

/-- Actual epsilon scaling `ε ↦ c ε` on first-order deformation classes: actual line-bundle
pullback along `scale f c`, restricted to `DeformationClasses`. -/
def scaleClass (c : k) : DeformationClasses preservation f →* DeformationClasses preservation f :=
  ((LineBundle.pullbackHom preservation (scale f c)).comp
    (DeformationClasses preservation f).subtype).codRestrict _
    (pullbackHom_scale_mem f preservation c)

/-- The underlying class of `scaleClass c q` is the actual pullback of `q` along `scale f c`. -/
lemma coe_scaleClass (c : k) (q : DeformationClasses preservation f) :
    (scaleClass f preservation c q : LineBundle.IsoClasses preservation (thickening f)) =
      LineBundle.pullbackHom preservation (scale f c) q :=
  rfl

variable (𝒰 : X.OrderedAffineCover)

/-- Epsilon scaling sends the class of the bundle of `z` to the class of the bundle of `c • z`.
The field acts on additive cocycles through the base-field section map, so `(c • z) a b` is
definitionally `baseSectionMap f _ c * z a b`. -/
lemma scaleClass_cocycleDeformationClass (c : k)
    (z : CechResolution.allPairsCocycles (OModulePresheaf.ofModules f (structureSheaf X)) 𝒰) :
    scaleClass f preservation c (cocycleDeformationClass preservation f 𝒰 z) =
      cocycleDeformationClass preservation f 𝒰 (c • z) := by
  apply Subtype.ext
  exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _
    (scaleCocycleBundleIso f 𝒰.U 𝒰.iSup_eq_top c z.1 (c • z).1 z.2 (fun _ _ ↦ rfl)))

variable [IsSeparated f]

attribute [local instance] structureSheaf_isQuasicoherent

/-- Under the comparison with actual derived `H¹`, actual epsilon scaling by `c` is
multiplication by `c`. -/
theorem deformationH1AddEquiv_scaleClass (c : k) (q : DeformationClasses preservation f) :
    deformationH1AddEquiv preservation f 𝒰 (Additive.ofMul (scaleClass f preservation c q)) =
      c • deformationH1AddEquiv preservation f 𝒰 (Additive.ofMul q) := by
  obtain ⟨z, hz⟩ := CechResolution.allPairsH1Map_surjective f 𝒰 (structureSheaf X)
    (deformationH1AddEquiv preservation f 𝒰 (Additive.ofMul q))
  have hq : cocycleDeformationClass preservation f 𝒰 z = q := by
    have h := (deformationH1AddEquiv_cocycleDeformationClass preservation f 𝒰 z).trans hz
    exact Additive.ofMul.injective ((deformationH1AddEquiv preservation f 𝒰).injective h)
  rw [← hq, scaleClass_cocycleDeformationClass, deformationH1AddEquiv_cocycleDeformationClass,
    deformationH1AddEquiv_cocycleDeformationClass, map_smul]

end Classes

end DualNumberThickening

end Langlands.AlgebraicGeometry.Picard
