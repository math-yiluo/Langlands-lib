import Langlands.GroupScheme.IdentityJetCoordinateBaseChange
import Langlands.GroupScheme.IdentityJetHomSections
import Langlands.GroupScheme.IdentityJetAffineGenerators
import Langlands.GroupScheme.IdentityJetAlgebraCoordinates
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation

/-! # Actual jet tensor coordinates under subgroup-family evaluation -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.GroupScheme.IdentityJet
open AffineCoordinates Corepresented TorusSubgroupModuli

private theorem baseChange_affine {S T : Scheme.{u}} (K : GroupScheme S)
    [IsAffineHom K.X.hom] (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj K).X.hom := by
  change IsAffineHom (Limits.pullback.snd K.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
attribute [local instance] baseChange_affine

private theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

/-- Actual coefficient pullback along a relative parameter map. -/
def familyCoefficientHom {R : CommRingCat.{u}} {M T : Over (Spec R)} (a : T ⟶ M)
    (U : M.left.Opens) (V : T.left.Opens) (hVU : V ≤ a.left ⁻¹ᵁ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom T.hom V
    Γ(M.left, U) →ₐ[R] Γ(T.left, V) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom T.hom V
  refine { toRingHom := (a.left.appLE U V hVU).hom, commutes' := ?_ }
  intro r
  have hh := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE a.left M.hom ⊤ U V (by simp) hVU)
      ((Scheme.ΓSpecIso R).inv r)
  change a.left.appLE U V hVU
    (M.hom.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso R).inv r)) =
      T.hom.appLE ⊤ V (by simp) ((Scheme.ΓSpecIso R).inv r)
  exact hh.trans (ConcreteCategory.congr_hom
    (appLE_congr_hom (Over.w a) ⊤ V _ _) ((Scheme.ΓSpecIso R).inv r))

/-- The actual ambient coordinate map of an evaluated family is the original
one pulled along its actual group projection. -/
theorem familyAmbientProjection {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left] {M T : Over (Spec R)}
    {K : GroupScheme M.left} (h : K ⟶ (GroupScheme.baseChange M.hom).obj G) (a : T ⟶ M) :
    ambientProjection G T.hom (familyHom h a) =
      Limits.pullback.fst K.X.hom a.left ≫ ambientProjection G M.hom h := by
  unfold ambientProjection
  rw [← Category.assoc, familyHom_original, Category.assoc, Category.assoc]

private theorem scalar_pullback {S T X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ T) (a : T ⟶ S) (f : Y ⟶ X)
    (hf : f ≫ p = q ≫ a) (U : S.Opens) (V : T.Opens)
    (hVU : V ≤ a ⁻¹ᵁ U) (hUV : q ⁻¹ᵁ V ≤ f ⁻¹ᵁ (p ⁻¹ᵁ U)) (r : Γ(S, U)) :
    f.appLE (p ⁻¹ᵁ U) (q ⁻¹ᵁ V) hUV (p.app U r) =
      q.app V (a.appLE U V hVU r) := by
  have hh := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE f p U (p ⁻¹ᵁ U) (q ⁻¹ᵁ V) le_rfl hUV) r
  rw [Scheme.Hom.appLE_eq_app] at hh
  have hk := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE q a U V (q ⁻¹ᵁ V) hVU le_rfl) r
  rw [Scheme.Hom.appLE_eq_app] at hk
  exact hh.trans ((ConcreteCategory.congr_hom
    (appLE_congr_hom hf U (q ⁻¹ᵁ V) _ _) r).trans hk.symm)

attribute [local instance] jetSectionAlgebra

/-- Actual jet pullback respects the actual base coefficient action. -/
theorem baseChangeSectionsRingMap_smul {S T : Scheme.{u}}
    (K : GroupScheme S) [IsAffineHom K.X.hom] (a : T ⟶ S)
    (n : ℕ) (U : S.Opens) (V : T.Opens) (hVU : V ≤ a ⁻¹ᵁ U)
    (r : Γ(S, U)) (x : Γ(scheme K n, projection K n ⁻¹ᵁ U)) :
    baseChangeSectionsRingMap K a n U V hVU (r • x) =
      (a.appLE U V hVU r) • baseChangeSectionsRingMap K a n U V hVU x := by
  change baseChangeSectionsRingMap K a n U V hVU ((projection K n).app U r * x) = _
  rw [map_mul]
  apply congrArg (· * baseChangeSectionsRingMap K a n U V hVU x)
  exact scalar_pullback (projection K n) (projection ((GroupScheme.baseChange a).obj K) n)
    a (baseChangeMap K a n) (baseChange_isPullback K a n).w U V hVU
    (baseChangeMap_preimage K a n hVU) r

private theorem tensorCoordinates_tmul_jet {R : CommRingCat.{u}} {S : Scheme.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left] (b : S ⟶ Spec R)
    (K : GroupScheme S) [IsAffineHom K.X.hom] (j : K ⟶ (GroupScheme.baseChange b).obj G)
    (n : ℕ) (U : S.affineOpens) (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    ambientTensorCoordinates G b j n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • jetCoordinateMap K (ambientProjection G b j) n U c := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  rw [ambientTensorCoordinates_tmul, ambientQuotientCoordinates,
    quotientCoordinates_mk, jetCoordinateMap_restrict]

private theorem jetCoordinateMap_congr {S : Scheme.{u}} (K : GroupScheme S)
    {B : CommRingCat.{u}} {j k : K.X.left ⟶ Spec B} (hjk : j = k)
    (n : ℕ) (U : S.Opens) (c : B) :
    jetCoordinateMap K j n U c = jetCoordinateMap K k n U c := by
  subst k
  rfl

private theorem homSections_jetCoordinateMap {S : Scheme.{u}} {K L : GroupScheme S}
    [IsAffineHom K.X.hom] [IsAffineHom L.X.hom] (f : L ⟶ K)
    {B : CommRingCat.{u}} (j : K.X.left ⟶ Spec B) (n : ℕ) (U : S.affineOpens) (c : B) :
    homSections f n U (jetCoordinateMap K j n U c) =
      jetCoordinateMap L (f.hom.hom.left ≫ j) n U c := by
  rw [jetCoordinateMap_eq, jetCoordinateMap_eq]
  exact homSections_quotientMap f n U (coordinateMap K j U c) |>.trans
    (congrArg ((quotientMap L n).app U) (homGroupSections_coordinateMap f j U c))

private theorem ambientProjection_comp {R : CommRingCat.{u}} {S : Scheme.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left] (b : S ⟶ Spec R)
    {K L : GroupScheme S} (h : K ⟶ (GroupScheme.baseChange b).obj G) (f : L ⟶ K) :
    f.hom.hom.left ≫ ambientProjection G b h = ambientProjection G b (f ≫ h) := by
  simp only [ambientProjection, Grp.comp_hom_hom, Over.comp_left, Category.assoc]

/-- Actual ambient tensor restriction commutes with actual subgroup-family evaluation. -/
theorem ambientTensorCoordinates_family_baseChange {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left] {M T : Over (Spec R)}
    {K : GroupScheme M.left} [IsAffineHom K.X.hom]
    (h : K ⟶ (GroupScheme.baseChange M.hom).obj G) (a : T ⟶ M)
    (n : ℕ) (U : M.left.affineOpens) (V : T.left.affineOpens)
    (hVU : (V : T.left.Opens) ≤ a.left ⁻¹ᵁ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom T.hom V
    ∀ z : Γ(M.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)),
      baseChangeSectionsRingMap K a.left n U V hVU
          (ambientTensorCoordinates G M.hom h n U z) =
        ambientTensorCoordinates G T.hom (familyHom h a) n V
          ((familyCoefficientHom a U V hVU).toLinearMap.rTensor _ z) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom M.hom U
  let := Scheme.TwoAffineOpenCover.algebraOfHom T.hom V
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r c =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [LinearMap.rTensor_tmul, tensorCoordinates_tmul_jet,
      tensorCoordinates_tmul_jet, baseChangeSectionsRingMap_smul, jetCoordinateMap_baseChange]
    apply congrArg (fun x => (a.left.appLE U V hVU r) • x)
    exact jetCoordinateMap_congr ((GroupScheme.baseChange a.left).obj K)
      (familyAmbientProjection G h a).symm n V c
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Actual ambient tensor restriction is compatible with actual source homomorphisms. -/
theorem homSections_ambientTensorCoordinates {R : CommRingCat.{u}} {S : Scheme.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left] (b : S ⟶ Spec R)
    {K L : GroupScheme S} [IsAffineHom K.X.hom] [IsAffineHom L.X.hom]
    (h : K ⟶ (GroupScheme.baseChange b).obj G) (f : L ⟶ K)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    ∀ z : Γ(S, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)),
      homSections f n U (ambientTensorCoordinates G b h n U z) =
        ambientTensorCoordinates G b (f ≫ h) n U z := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r c =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [tensorCoordinates_tmul_jet, (homSections f n U).map_smul,
      tensorCoordinates_tmul_jet]
    apply congrArg (r • ·)
    exact (homSections_jetCoordinateMap f (ambientProjection G b h) n U c).trans
      (jetCoordinateMap_congr L (ambientProjection_comp G b h f) n U c)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Langlands.GroupScheme.IdentityJet
