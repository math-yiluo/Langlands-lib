import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.GroupScheme.AffineWeilTorusAdjunction
import Langlands.GroupScheme.SplitComponent.AffineTargetBridge
import Langlands.Global.RealSplitTorusIdentityComponent

/-! # The Getz–Hahn split centre: the greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G` -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section AffineCentre

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- For an affine group scheme, a point over `Spec A` lies in the centre exactly when its image
over every `A`-algebra commutes with every point there. -/
theorem mem_center_algSpec_iff {A : CommAlgCat.{u} R} (g : G.affinePoints A) :
    g ∈ (center G).carrier ((algSpec R).obj (op A)) ↔
      ∀ (D : CommAlgCat.{u} R) (φ : A ⟶ D) (y : G.affinePoints D),
        Commute (G.affinePointMap φ g) y := by
  constructor
  · intro hg D φ y
    exact hg _ ((algSpec R).map φ.op) y
  · intro h T' a y
    let M := AffineCoordinates.functor G
    let c := AffineCoordinates.corepresentation G
    let e := (AffineCoordinates.groupSchemeIso G).symm
    let Φ : (T' ⟶ G.X) ≃* M.obj ((algΓ R).obj T').unop :=
      (isoPointsEquiv e T').trans (Corepresented.pointsEquiv M c T')
    let D : CommAlgCat.{u} R := ((algΓ R).obj T').unop
    let ψ : A ⟶ D := (Corepresented.affineSectionsIso A).inv ≫ ((algΓ R).map a).unop
    have key : Φ (a ≫ g) = SplitComponent.coordinatePointsEquiv G D (G.affinePointMap ψ g) := by
      rw [SplitComponent.coordinatePointsEquiv_naturality]
      change Corepresented.pointsEquiv M c T' ((a ≫ g) ≫ e.hom.hom.hom) = _
      rw [Category.assoc, Corepresented.pointsEquiv_naturality,
        Corepresented.pointsEquiv_eq_affinePointsEquiv]
      change _ = M.map ψ (Corepresented.affinePointsEquiv M c A (g ≫ e.hom.hom.hom))
      rw [Functor.map_comp]
      rfl
    apply Corepresented.commute_of_mulEquiv Φ
    rw [key, ← (SplitComponent.coordinatePointsEquiv G D).apply_symm_apply (Φ y)]
    exact (h D ψ _).map (SplitComponent.coordinatePointsEquiv G D)

end AffineCentre

end Langlands.GroupScheme

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme Langlands.GroupScheme.SplitComponent

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A homomorphism `j : S → Res_{F/ℚ} G` takes values in `Res_{F/ℚ} Z_G`: for every
`ℚ`-algebra `C` and every point `s ∈ S(C)`, the point `j(s)` of `(Res_{F/ℚ} G)(C) = G(F ⊗ C)`
lies in the centre `Z_G` of `G` over `F ⊗ C`. -/
def IsRestrictionCentreValued {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G) : Prop :=
  ∀ (C : Type) [CommRing C] [Algebra ℚ C]
    (s : Langlands.GroupScheme.affinePoints S.toGrp (CommAlgCat.of (CommRingCat.of ℚ) C)),
    AffineWeil.pointsEquiv ℚ F G C (s ≫ j.hom.hom) ∈
      (center G).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of (CommRingCat.of F) (F ⊗[ℚ] C))))

/-- Getz–Hahn (2.20): `j : S → Res_{F/ℚ} G` is the greatest `ℚ`-split torus of
`Res_{F/ℚ} Z_G`. It is a split subtorus with values in `Res_{F/ℚ} Z_G`, and every split
subtorus with values in `Res_{F/ℚ} Z_G` factors through it. -/
def IsGreatestRestrictionCentreSplitTorus {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G) : Prop :=
  IsSplitSubtorus j ∧ IsRestrictionCentreValued F G j ∧
    ∀ (S' : CommGroupScheme (Spec (CommRingCat.of ℚ)))
      (j' : S'.toGrp ⟶ AffineWeil.groupScheme ℚ F G),
      IsSplitSubtorus j' → IsRestrictionCentreValued F G j' →
        ∃ f : S'.toGrp ⟶ S.toGrp, f ≫ j = j'

variable {F G}

/-- The algebra map `C → D`, `c ↦ φ (1 ⊗ c)`, for an `F`-algebra map `φ : F ⊗ C → D`. -/
def tensorRightHom {C : Type} [CommRing C] [Algebra ℚ C]
    {D : CommAlgCat.{0} (CommRingCat.of F)}
    (φ : CommAlgCat.of (CommRingCat.of F) (F ⊗[ℚ] C) ⟶ D) :
    CommAlgCat.of (CommRingCat.of ℚ) C ⟶ (AffineWeil.restrictScalars ℚ F).obj D :=
  letI : Algebra ℚ D := Algebra.compHom D (algebraMap ℚ F)
  CommAlgCat.ofHom
    { φ.hom.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℚ] F ⊗[ℚ] C).toRingHom with
      commutes' := fun r => (φ.hom.toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[ℚ] F ⊗[ℚ] C).toRingHom).map_rat_algebraMap r }

theorem tensorRightHom_apply {C : Type} [CommRing C] [Algebra ℚ C]
    {D : CommAlgCat.{0} (CommRingCat.of F)}
    (φ : CommAlgCat.of (CommRingCat.of F) (F ⊗[ℚ] C) ⟶ D) (c : C) :
    (tensorRightHom φ).hom c = φ.hom ((1 : F) ⊗ₜ[ℚ] c) := rfl

theorem tensorMap_tensorRightHom_multiplication {C : Type} [CommRing C] [Algebra ℚ C]
    {D : CommAlgCat.{0} (CommRingCat.of F)}
    (φ : CommAlgCat.of (CommRingCat.of F) (F ⊗[ℚ] C) ⟶ D) :
    (AffineWeil.tensorFunctor ℚ F).map (tensorRightHom φ) ≫ AffineWeil.multiplication ℚ D = φ := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change (AffineWeil.multiplication ℚ D).hom
    (((AffineWeil.tensorFunctor ℚ F).map (tensorRightHom φ)).hom x) = φ.hom x
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    rw [AffineWeil.multiplication_tensorMap_tmul, tensorRightHom_apply, ← φ.hom.commutes b,
      ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
    rfl
  | add x y hx hy =>
    erw [map_add, map_add, hx, hy, map_add]

/-- A central homomorphism into `Res_{F/ℚ} G` takes values in `Res_{F/ℚ} Z_G`. -/
theorem isRestrictionCentreValued_of_isCentral {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hj : IsCentral j) :
    IsRestrictionCentreValued F G j := by
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  intro C _ _ s
  rw [mem_center_algSpec_iff]
  intro D φ y
  obtain ⟨y', rfl⟩ := AffineWeil.exists_affinePointMap_multiplication_eq ℚ G D y
  obtain ⟨y'', rfl⟩ :=
    (AffineWeil.pointsEquiv ℚ F G ((AffineWeil.restrictScalars ℚ F).obj D)).surjective y'
  let ψ := tensorRightHom φ
  have hc' := (hj _ s _ ((algSpec (CommRingCat.of ℚ)).map ψ.op) y'').map
    (AffineWeil.pointsEquiv ℚ F G ((AffineWeil.restrictScalars ℚ F).obj D))
  let _ : Algebra ℚ D := Algebra.compHom D (algebraMap ℚ F)
  have hn := AffineWeil.pointsEquiv_naturality ℚ F G ψ.hom (s ≫ j.hom.hom)
  change AffineWeil.pointsEquiv ℚ F G _ ((algSpec (CommRingCat.of ℚ)).map ψ.op ≫ s ≫ j.hom.hom) = _
    at hn
  rw [hn] at hc'
  have hm := hc'.map (G.affinePointMap (AffineWeil.multiplication ℚ D))
  have key : G.affinePointMap φ (AffineWeil.pointsEquiv ℚ F G C (s ≫ j.hom.hom)) =
      G.affinePointMap (AffineWeil.multiplication ℚ D)
        (G.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor F ψ.hom))
          (AffineWeil.pointsEquiv ℚ F G C (s ≫ j.hom.hom))) := by
    conv_lhs => rw [← tensorMap_tensorRightHom_multiplication φ]
    erw [GroupScheme.affinePointMap_comp]
    rfl
  rw [key]
  exact hm

/-- A homomorphism from a split torus into `Res_{F/ℚ} G` with values in `Res_{F/ℚ} Z_G` is
central in `Res_{F/ℚ} G`. -/
theorem isCentral_of_isRestrictionCentreValued {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hS : IsSplitTorus S.toGrp)
    (hj : IsRestrictionCentreValued F G j) : IsCentral j := by
  obtain ⟨I0, hI0, ⟨eS⟩⟩ := hS
  let _ : Fintype I0 := Fintype.ofFinite I0
  let e0 := (torusIso (CommRingCat.of ℚ) I0).hom ≫ eS.inv
  have hc : IsCentral (e0 ≫ j) := by
    rw [← groupSchemeMap_natOfHom (latticeCorep (CommRingCat.of ℚ) (FreeAbelianGroup I0))
      (AffineWeil.corepresentableBy ℚ F G) (e0 ≫ j)]
    apply isCentral_groupSchemeMap
    intro C x y
    rw [natOfHom_app, Grp.comp_hom_hom, ← Category.assoc]
    exact commute_of_mem_center
      (hj C ((Corepresented.affinePointsEquiv _ _ C).symm x ≫ e0.hom.hom)) y
  have hj' : j = (eS.hom ≫ (torusIso (CommRingCat.of ℚ) I0).inv) ≫ e0 ≫ j := by
    simp only [e0, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [hj']
  exact hc.comp _

/-- For a split torus `S`, a homomorphism `S → Res_{F/ℚ} G` takes values in `Res_{F/ℚ} Z_G`
exactly when it is central in `Res_{F/ℚ} G`. -/
theorem isRestrictionCentreValued_iff_isCentral {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hS : IsSplitTorus S.toGrp) :
    IsRestrictionCentreValued F G j ↔ IsCentral j :=
  ⟨isCentral_of_isRestrictionCentreValued hS, isRestrictionCentreValued_of_isCentral⟩

/-- A closed subgroup can be cancelled on the right. -/
private theorem cancel_of_isClosedSubgroup {H K : GroupScheme (Spec (CommRingCat.of ℚ))}
    {i : H ⟶ AffineWeil.groupScheme ℚ F G} (hi : IsClosedSubgroup i) {f g : K ⟶ H}
    (h : f ≫ i = g ≫ i) : f = g := by
  have : IsClosedImmersion i.hom.hom.left := hi
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  have h' := congrArg (fun q : K ⟶ AffineWeil.groupScheme ℚ F G => q.hom.hom.left) h
  exact (cancel_mono i.hom.hom.left).mp h'

/-- The greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G` is exactly a split component of
`Res_{F/ℚ} G`. -/
theorem isGreatestRestrictionCentreSplitTorus_iff_isSplitComponent
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} :
    IsGreatestRestrictionCentreSplitTorus F G j ↔ IsSplitComponent j := by
  constructor
  · rintro ⟨hsub, hrcv, hgr⟩
    refine ⟨⟨hsub, isCentral_of_isRestrictionCentreValued hsub.1 hrcv⟩, ?_⟩
    intro A' i' hi' f hf
    obtain ⟨g, hg⟩ := hgr A' i' hi'.1 (isRestrictionCentreValued_of_isCentral hi'.2)
    refine ⟨⟨g, ?_, ?_⟩⟩
    · apply cancel_of_isClosedSubgroup hsub.2
      rw [Category.assoc, hg, hf, Category.id_comp]
    · apply cancel_of_isClosedSubgroup hi'.1.2
      rw [Category.assoc, hf, hg, Category.id_comp]
  · intro hj
    refine ⟨hj.1.1, isRestrictionCentreValued_of_isCentral hj.1.2, ?_⟩
    intro S' j' hsub' hrcv'
    exact hj.exists_comp_eq_of_isCentral (finiteType_coordinateAlgebra _) j' hsub'.1
      (isCentral_of_isRestrictionCentreValued hsub'.1 hrcv')

variable (F G) in
/-- The greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G` exists. -/
theorem exists_isGreatestRestrictionCentreSplitTorus :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
      (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G), IsGreatestRestrictionCentreSplitTorus F G j :=
  ⟨_, _, isGreatestRestrictionCentreSplitTorus_iff_isSplitComponent.mpr
    (isSplitComponent_canonicalRestrictionComponent F G)⟩

/-- Getz–Hahn (2.20): the positive real image of the greatest `ℚ`-split torus of
`Res_{F/ℚ} Z_G` is the canonical split-centre subgroup `A_G` of `G(𝔸_F)`. -/
theorem subgroup_eq_canonicalSubgroup_of_isGreatest
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
    (hj : IsGreatestRestrictionCentreSplitTorus F G j) :
    subgroup F G S j = canonicalSubgroup F G :=
  subgroup_eq_canonicalSubgroup
    (isGreatestRestrictionCentreSplitTorus_iff_isSplitComponent.mp hj)

section IdentityComponent

open PositiveRealTorus

local instance realAffinePointsTopology (H : GroupScheme (Spec (CommRingCat.of ℚ))) :
    TopologicalSpace (Lie.AffinePoints H ℝ) :=
  GroupScheme.affinePointsTopologicalSpace H (CommAlgCat.of ℚ ℝ)

/-- For a split torus `S`, the subgroup attached to `j : S → Res_{F/ℚ} G` is the image in
`G(𝔸_F)` of the identity component of the real points `S(ℝ)`, through
`S(ℝ) → (Res_{F/ℚ} G)(ℝ) = G(F ⊗ ℝ) = G(F_∞) ⊆ G(𝔸_F)`. -/
theorem coe_subgroup_eq_image_connectedComponent
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G) (hS : IsSplitTorus S.toGrp) :
    (subgroup F G S j : Set (AdelicGroupPoints F G)) =
      (fun a => AdelicGroupPoints.ofInfinite F G (AdelicWeilRestriction.realPointsEquiv F G
        (pointMap ℚ S.toGrp (AffineWeil.groupScheme ℚ F G) ℝ j a))) ''
        connectedComponent (1 : Lie.AffinePoints S.toGrp ℝ) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  let _ : Fintype I := Fintype.ofFinite I
  rw [connectedComponent_one_eq_orderedCoefficientPositiveSubgroup ℚ S I e ℝ]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- Getz–Hahn (2.20), literally: `A_G` is the image in `G(𝔸_F)` of the identity component of the
real points of the greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G`, and it is the canonical
split-centre subgroup. -/
theorem coe_canonicalSubgroup_eq_image_connectedComponent
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
    (hj : IsGreatestRestrictionCentreSplitTorus F G j) :
    (canonicalSubgroup F G : Set (AdelicGroupPoints F G)) =
      (fun a => AdelicGroupPoints.ofInfinite F G (AdelicWeilRestriction.realPointsEquiv F G
        (pointMap ℚ S.toGrp (AffineWeil.groupScheme ℚ F G) ℝ j a))) ''
        connectedComponent (1 : Lie.AffinePoints S.toGrp ℝ) := by
  rw [← subgroup_eq_canonicalSubgroup_of_isGreatest hj]
  exact coe_subgroup_eq_image_connectedComponent j hj.1.1

end IdentityComponent

end Langlands.Global.RestrictionSplitCentre
