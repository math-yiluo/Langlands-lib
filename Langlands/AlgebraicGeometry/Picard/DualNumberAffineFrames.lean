import Langlands.AlgebraicGeometry.Picard.AffineNilpotentLineBundle
import Langlands.AlgebraicGeometry.Picard.DualNumberActualUnits
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit

/-! # Affine-local frames for actual line-bundle deformations -/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.SchemeModule Langlands.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

lemma closedPoint_preimage_projection (U : X.Opens) :
    closedPoint f ⁻¹ᵁ projection f ⁻¹ᵁ U = U := by
  rw [← Scheme.Hom.comp_preimage, closedPoint_projection, Scheme.Hom.id_preimage]

/-- The actual zero section on an open of the original scheme. -/
def closedPointOpen (U : X.Opens) : U.toScheme ⟶ (projection f ⁻¹ᵁ U).toScheme :=
  (closedPoint f).resLE _ U (by rw [closedPoint_preimage_projection])

@[reassoc (attr := simp)]
lemma closedPointOpen_comp_ι (U : X.Opens) :
    closedPointOpen f U ≫ (projection f ⁻¹ᵁ U).ι = U.ι ≫ closedPoint f :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma closedPointOpen_projection (U : X.Opens) :
    closedPointOpen f U ≫ (projection f ∣_ U) = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    closedPointOpen_comp_ι, Category.assoc, closedPoint_projection,
    Category.comp_id, Category.id_comp]

instance closedPointOpen_surjective (U : X.Opens) : Surjective (closedPointOpen f U) := by
  constructor
  intro y
  refine ⟨(projection f ∣_ U) y, ?_⟩
  apply Subtype.ext
  rw [show (closedPointOpen f U ((projection f ∣_ U) y)).val =
    closedPoint f (((projection f ∣_ U) y).val) from Scheme.Hom.coe_resLE_apply _ _ _]
  rw [morphismRestrict_base_coe]
  exact closedPoint_projection_apply f y.val

lemma closedPointOpen_appTop_surjective (U : X.Opens) :
    Function.Surjective (closedPointOpen f U).appTop := by
  intro a
  refine ⟨(projection f ∣_ U).appTop a, ?_⟩
  exact congrArg (fun r ↦ r.hom a)
    (congrArg (fun r : U.toScheme ⟶ U.toScheme ↦ r.appTop)
      (closedPointOpen_projection f U))

/-- Restrict an actual zero-section trivialization to the corresponding open schemes. -/
def zeroSectionOpenTrivialization (U : X.Opens) (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    (Scheme.Modules.pullback (closedPointOpen f U)).obj
        ((Scheme.Modules.pullback (projection f ⁻¹ᵁ U).ι).obj L.obj) ≅ structureModule U.toScheme :=
  (Scheme.Modules.pullbackComp (closedPointOpen f U) (projection f ⁻¹ᵁ U).ι).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr (closedPointOpen_comp_ι f U)).app L.obj ≪≫
      ((Scheme.Modules.pullbackComp U.ι (closedPoint f)).app L.obj).symm ≪≫
        (Scheme.Modules.pullback U.ι).mapIso e ≪≫ pullbackUnitIso U.ι

/-- Every such actual line bundle is trivial over the inverse image of each affine open. -/
def affineOpenTrivialization (U : X.Opens) (hU : IsAffineOpen U)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    (Scheme.Modules.pullback (projection f ⁻¹ᵁ U).ι).obj L.obj ≅
      structureModule (projection f ⁻¹ᵁ U).toScheme := by
  let : IsAffine U.toScheme := hU
  let : IsAffine (projection f ⁻¹ᵁ U).toScheme := hU.preimage (projection f)
  exact affinePullbackTrivialization (closedPointOpen f U)
    (closedPointOpen_appTop_surjective f U)
    ((LineBundle.pullback (projection f ⁻¹ᵁ U).ι).obj L)
    (zeroSectionOpenTrivialization f U L e)

/-- A genuine local frame exists on the inverse image of each affine open. -/
lemma exists_affineOpen_frame (U : X.Opens) (hU : IsAffineOpen U)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    ∃ s : Γ(L.obj, projection f ⁻¹ᵁ U),
      Scheme.Modules.IsFrameOn s (projection f ⁻¹ᵁ U) :=
  Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit (projection f ⁻¹ᵁ U)
    (affineOpenTrivialization f U hU L e)

/-- Actual zero-section reduction of a local section. -/
def reduceSection (U : X.Opens) (M : (thickening f).Modules)
    (s : Γ(M, projection f ⁻¹ᵁ U)) :
    Γ((Scheme.Modules.pullback (closedPoint f)).obj M, U) :=
  ((Scheme.Modules.pullback (closedPoint f)).obj M).presheaf.map
    (homOfLE (show U ≤ closedPoint f ⁻¹ᵁ projection f ⁻¹ᵁ U by
      rw [closedPoint_preimage_projection])).op
        (Scheme.Modules.pullbackLocalSection (closedPoint f) s)

lemma reduceSection_smul (U : X.Opens) (M : (thickening f).Modules)
    (a : Γ(thickening f, projection f ⁻¹ᵁ U)) (s : Γ(M, projection f ⁻¹ᵁ U)) :
    reduceSection f U M (a • s) = reductionMap f U a • reduceSection f U M s := by
  unfold reduceSection reductionMap
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.map_smul]
  rfl

/-- Scalar value of a reduced section in a specified zero-section trivialization. -/
def reducedCoefficient (U : X.Opens) (M : (thickening f).Modules)
    (e : (Scheme.Modules.pullback (closedPoint f)).obj M ≅ structureModule X)
    (s : Γ(M, projection f ⁻¹ᵁ U)) : Γ(X, U) :=
  e.hom.app U (reduceSection f U M s)

lemma reducedCoefficient_smul (U : X.Opens) (M : (thickening f).Modules)
    (e : (Scheme.Modules.pullback (closedPoint f)).obj M ≅ structureModule X)
    (a : Γ(thickening f, projection f ⁻¹ᵁ U)) (s : Γ(M, projection f ⁻¹ᵁ U)) :
    reducedCoefficient f U M e (a • s) =
      reductionMap f U a * reducedCoefficient f U M e s := by
  unfold reducedCoefficient
  rw [reduceSection_smul]
  exact Scheme.Modules.Hom.app_smul e.hom _ _

lemma isFrameOn_smul_unit {Y : Scheme.{u}} {M : Y.Modules} {U V : Y.Opens}
    (s : Γ(M, U)) (hs : Scheme.Modules.IsFrameOn s V) (a : Γ(Y, U)ˣ) :
    Scheme.Modules.IsFrameOn ((a : Γ(Y, U)) • s) V := by
  intro W hWU hWV
  let aW := Units.map (Y.presheaf.map (homOfLE hWU).op).hom.toMonoidHom a
  have he :
      (fun b : Γ(Y, W) ↦ b • M.presheaf.map (homOfLE hWU).op ((a : Γ(Y, U)) • s)) =
      (fun b : Γ(Y, W) ↦ b • M.presheaf.map (homOfLE hWU).op s) ∘
        (fun b : Γ(Y, W) ↦ b * (aW : Γ(Y, W))) := by
    funext b
    rw [Scheme.Modules.map_smul, smul_smul]
    rfl
  rw [he]
  exact (hs.bijective hWU hWV).comp (Units.mulRight aW).bijective

/-- A local frame has an invertible coefficient in every zero-section trivialization. -/
lemma reducedCoefficient_isUnit (U : X.Opens) (M : (thickening f).Modules)
    (e : (Scheme.Modules.pullback (closedPoint f)).obj M ≅ structureModule X)
    (s : Γ(M, projection f ⁻¹ᵁ U))
    (hs : Scheme.Modules.IsFrameOn s (projection f ⁻¹ᵁ U)) :
    IsUnit (reducedCoefficient f U M e s) := by
  have hle : U ≤ closedPoint f ⁻¹ᵁ projection f ⁻¹ᵁ U := by
    rw [closedPoint_preimage_projection]
  have hr := (hs.pullbackLocalSection (closedPoint f)).map (homOfLE hle)
  have hr' := (hr.mono hle).map_iso e
  obtain ⟨a, ha⟩ := (hr'.bijective le_rfl le_rfl).surjective (1 : Γ(X, U))
  change a • ((structureModule X).presheaf.map (homOfLE le_rfl).op
    (reducedCoefficient f U M e s)) = (1 : Γ(X, U)) at ha
  simp only [homOfLE_refl, op_id] at ha
  rw [(structureModule X).presheaf.map_id (op U)] at ha
  change a * reducedCoefficient f U M e s = 1 at ha
  exact isUnit_iff_exists_inv.mpr ⟨a, (mul_comm _ _).trans ha⟩

/-- Normalize an actual local frame so its zero-section coefficient is one. -/
lemma exists_normalized_frame_of_frame (U : X.Opens) (M : (thickening f).Modules)
    (e : (Scheme.Modules.pullback (closedPoint f)).obj M ≅ structureModule X)
    (s : Γ(M, projection f ⁻¹ᵁ U))
    (hs : Scheme.Modules.IsFrameOn s (projection f ⁻¹ᵁ U)) :
    ∃ t : Γ(M, projection f ⁻¹ᵁ U),
      Scheme.Modules.IsFrameOn t (projection f ⁻¹ᵁ U) ∧
        reducedCoefficient f U M e t = 1 := by
  have hb := reducedCoefficient_isUnit f U M e s hs
  let b : Γ(X, U)ˣ := hb.unit
  let a := Units.map ((projection f).app U).hom.toMonoidHom b⁻¹
  refine ⟨(a : Γ(thickening f, projection f ⁻¹ᵁ U)) • s,
    isFrameOn_smul_unit s hs a, ?_⟩
  rw [reducedCoefficient_smul]
  change reductionMap f U ((projection f).app U ((b⁻¹ : Γ(X, U)ˣ) : Γ(X, U))) *
    reducedCoefficient f U M e s = 1
  rw [reductionMap_projection_apply, ← hb.unit_spec]
  exact Units.inv_mul b

/-- Every affine open admits a frame normalized against the specified actual reduction. -/
lemma exists_affineOpen_normalized_frame (U : X.Opens) (hU : IsAffineOpen U)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    ∃ s : Γ(L.obj, projection f ⁻¹ᵁ U),
      Scheme.Modules.IsFrameOn s (projection f ⁻¹ᵁ U) ∧
        reducedCoefficient f U L.obj e s = 1 := by
  obtain ⟨s, hs⟩ := exists_affineOpen_frame f U hU L e
  exact exists_normalized_frame_of_frame f U L.obj e s hs

lemma reduceSection_naturality {U V : X.Opens} (h : V ≤ U)
    (M : (thickening f).Modules) (s : Γ(M, projection f ⁻¹ᵁ U)) :
    reduceSection f V M (M.presheaf.map
      ((Opens.map (projection f).base).map (homOfLE h)).op s) =
    ((Scheme.Modules.pullback (closedPoint f)).obj M).presheaf.map (homOfLE h).op
      (reduceSection f U M s) := by
  unfold reduceSection
  rw [← Scheme.Modules.map_pullbackLocalSection]
  simp only [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma reducedCoefficient_naturality {U V : X.Opens} (h : V ≤ U)
    (M : (thickening f).Modules)
    (e : (Scheme.Modules.pullback (closedPoint f)).obj M ≅ structureModule X)
    (s : Γ(M, projection f ⁻¹ᵁ U)) :
    reducedCoefficient f V M e (M.presheaf.map
      ((Opens.map (projection f).base).map (homOfLE h)).op s) =
      X.presheaf.map (homOfLE h).op (reducedCoefficient f U M e s) := by
  unfold reducedCoefficient
  rw [reduceSection_naturality]
  exact congrArg (fun r ↦ r.hom (reduceSection f U M s))
    (e.hom.mapPresheaf.naturality (homOfLE h).op)

/-- A chosen actual affine-local frame normalized by its zero-section coefficient. -/
def affineNormalizedFrame (U : X.Opens) (hU : IsAffineOpen U)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    Γ(L.obj, projection f ⁻¹ᵁ U) :=
  (exists_affineOpen_normalized_frame f U hU L e).choose

lemma affineNormalizedFrame_isFrame (U : X.Opens) (hU : IsAffineOpen U)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    Scheme.Modules.IsFrameOn (affineNormalizedFrame f U hU L e) (projection f ⁻¹ᵁ U) :=
  (exists_affineOpen_normalized_frame f U hU L e).choose_spec.1

@[simp]
lemma reducedCoefficient_affineNormalizedFrame (U : X.Opens) (hU : IsAffineOpen U)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X) :
    reducedCoefficient f U L.obj e (affineNormalizedFrame f U hU L e) = 1 :=
  (exists_affineOpen_normalized_frame f U hU L e).choose_spec.2

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
