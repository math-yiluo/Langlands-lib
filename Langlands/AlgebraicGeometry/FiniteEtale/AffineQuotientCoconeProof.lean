import Langlands.AlgebraicGeometry.FiniteEtale.QuotientCoconeStatements
import Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraProof
import Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraGeometricPointsProof

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-! ### Points of affine schemes -/

section Points

/-- Morphisms from the spectrum of a ring into an affine scheme are ring maps
out of its global sections. -/
def affinePointEquiv (Z : Scheme.{u}) [IsAffine Z] (K : CommRingCat.{u}) :
    (Spec K ⟶ Z) ≃ (Γ(Z, ⊤) ⟶ K) where
  toFun x := Spec.preimage (x ≫ Z.isoSpec.hom)
  invFun φ := Spec.map φ ≫ Z.isoSpec.inv
  left_inv x := by simp
  right_inv φ := by simp

@[simp]
theorem affinePointEquiv_symm_apply (Z : Scheme.{u}) [IsAffine Z] (K : CommRingCat.{u})
    (φ : Γ(Z, ⊤) ⟶ K) : (affinePointEquiv Z K).symm φ = Spec.map φ ≫ Z.isoSpec.inv := rfl

theorem SpecMap_affinePointEquiv (Z : Scheme.{u}) [IsAffine Z] (K : CommRingCat.{u})
    (x : Spec K ⟶ Z) : Spec.map (affinePointEquiv Z K x) = x ≫ Z.isoSpec.hom :=
  Spec.map_preimage _

/-- Postcomposition corresponds to precomposition with the map on global sections. -/
theorem affinePointEquiv_comp {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W] (K : CommRingCat.{u})
    (h : Z ⟶ W) (x : Spec K ⟶ Z) :
    affinePointEquiv W K (x ≫ h) = h.appTop ≫ affinePointEquiv Z K x := by
  apply Spec.map_injective
  rw [SpecMap_affinePointEquiv, Spec.map_comp, SpecMap_affinePointEquiv, Category.assoc,
    Category.assoc, Scheme.isoSpec_hom_naturality]

end Points

/-! ### The action on global sections -/

/-- Over an affine base, the source of a finite cover is affine. -/
instance isAffine_cover_left {S : Scheme.{u}} [IsAffine S] (Y : Cover S) : IsAffine Y.obj.left :=
  isAffine_of_isAffineHom Y.obj.hom

section Construction

variable {S : Scheme.{u}} {G : Type u} [Group G] (D : SingleObj G ⥤ Cover S)

/-- The scheme acted on by the diagram. -/
abbrev coverScheme : Scheme.{u} := (D.obj (SingleObj.star G)).obj.left

/-- The contravariant ring map of global sections induced by `g`. -/
def coverAction (g : G) : Γ(coverScheme D, ⊤) ⟶ Γ(coverScheme D, ⊤) :=
  (D.map (SingleObj.toEnd G g)).hom.left.appTop

theorem coverAction_one : coverAction D 1 = 𝟙 _ := by
  simp [coverAction]

theorem coverAction_mul (g h : G) :
    coverAction D (g * h) = coverAction D g ≫ coverAction D h := by
  simp [coverAction]

theorem appTop_comp_coverAction (g : G) :
    (D.obj (SingleObj.star G)).obj.hom.appTop ≫ coverAction D g =
      (D.obj (SingleObj.star G)).obj.hom.appTop := by
  rw [coverAction, ← Scheme.Hom.comp_appTop, Over.w]

theorem coverAction_inv_apply (g : G) (a : Γ(coverScheme D, ⊤)) :
    (coverAction D g).hom ((coverAction D g⁻¹).hom a) = a := by
  rw [← CommRingCat.comp_apply, ← coverAction_mul, inv_mul_cancel, coverAction_one]
  rfl

theorem coverAction_appTop_mul (g : G) (r : Γ(S, ⊤)) (a : Γ(coverScheme D, ⊤)) :
    (coverAction D g).hom ((D.obj (SingleObj.star G)).obj.hom.appTop.hom r * a) =
      (D.obj (SingleObj.star G)).obj.hom.appTop.hom r * (coverAction D g).hom a := by
  rw [map_mul]
  congr 1
  exact congrArg (fun φ => CommRingCat.Hom.hom φ r) (appTop_comp_coverAction D g)

/-- Global sections of the acted-on cover. -/
def coverRing : Type u := Γ(coverScheme D, ⊤)

instance : CommRing (coverRing D) := inferInstanceAs (CommRing Γ(coverScheme D, ⊤))

instance : Algebra Γ(S, ⊤) (coverRing D) :=
  (D.obj (SingleObj.star G)).obj.hom.appTop.hom.toAlgebra

theorem coverRing_algebraMap_apply (r : Γ(S, ⊤)) :
    algebraMap Γ(S, ⊤) (coverRing D) r = (D.obj (SingleObj.star G)).obj.hom.appTop.hom r := rfl

/-- The left action: `g` acts through the ring map induced by `g⁻¹`. -/
instance : MulSemiringAction G (coverRing D) where
  smul g a := (coverAction D g⁻¹).hom a
  one_smul a := by
    change (coverAction D 1⁻¹).hom a = a
    rw [inv_one, coverAction_one]
    rfl
  mul_smul g h a := by
    change (coverAction D (g * h)⁻¹).hom a = (coverAction D g⁻¹).hom ((coverAction D h⁻¹).hom a)
    rw [mul_inv_rev, coverAction_mul]
    rfl
  smul_zero g := map_zero (coverAction D g⁻¹).hom
  smul_add g := map_add (coverAction D g⁻¹).hom
  smul_one g := map_one (coverAction D g⁻¹).hom
  smul_mul g := map_mul (coverAction D g⁻¹).hom

theorem coverRing_smul_def (g : G) (a : coverRing D) :
    g • a = (coverAction D g⁻¹).hom a := rfl

instance : SMulCommClass G Γ(S, ⊤) (coverRing D) where
  smul_comm g r a := coverAction_appTop_mul D g⁻¹ r a

/-- The invariant subalgebra of global sections. -/
abbrev quotientRing : Subalgebra Γ(S, ⊤) (coverRing D) :=
  FixedPoints.subalgebra Γ(S, ⊤) (coverRing D) G

theorem mem_quotientRing_iff (a : coverRing D) :
    a ∈ quotientRing D ↔ ∀ g : G, (coverAction D g).hom a = a := by
  change (∀ g : G, g • a = a) ↔ _
  constructor
  · intro h g
    have hg := h g⁻¹
    rw [coverRing_smul_def, inv_inv] at hg
    exact hg
  · intro h g
    exact h g⁻¹

/-- The inclusion of invariants, as a morphism of commutative rings. -/
def quotientRingInclusion : CommRingCat.of (quotientRing D) ⟶ Γ(coverScheme D, ⊤) :=
  CommRingCat.ofHom (quotientRing D).val.toRingHom

theorem quotientRingInclusion_injective :
    Function.Injective (quotientRingInclusion D).hom := Subtype.val_injective

theorem quotientRingInclusion_comp_coverAction (g : G) :
    quotientRingInclusion D ≫ coverAction D g = quotientRingInclusion D := by
  ext c
  exact (mem_quotientRing_iff D c.1).mp c.2 g

/-- The quotient scheme: the spectrum of the invariant subalgebra. -/
abbrev quotientScheme : Scheme.{u} := Spec (CommRingCat.of (quotientRing D))

variable [IsAffine S]

/-- The quotient map: the spectrum of the inclusion of invariants. -/
def quotientMap : coverScheme D ⟶ quotientScheme D :=
  (coverScheme D).isoSpec.hom ≫ Spec.map (quotientRingInclusion D)

/-- The structure morphism of the quotient, through the spectrum of the base ring. -/
def quotientStructure : quotientScheme D ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D))) ≫ S.isoSpec.inv

theorem quotientMap_comp_quotientStructure :
    quotientMap D ≫ quotientStructure D = (D.obj (SingleObj.star G)).obj.hom := by
  have e : CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D)) ≫ quotientRingInclusion D =
      (D.obj (SingleObj.star G)).obj.hom.appTop := by
    ext r
    rfl
  rw [quotientMap, quotientStructure, Category.assoc, ← Category.assoc (Spec.map _),
    ← Spec.map_comp, e, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The quotient map is an epimorphism onto affine schemes. -/
theorem quotientMap_cancel {Y : Scheme.{u}} [IsAffine Y] {a b : quotientScheme D ⟶ Y}
    (h : quotientMap D ≫ a = quotientMap D ≫ b) : a = b := by
  rw [← cancel_mono Y.isoSpec.hom]
  rw [← Spec.map_preimage (a ≫ Y.isoSpec.hom), ← Spec.map_preimage (b ≫ Y.isoSpec.hom)]
  congr 1
  have h' : Spec.map (Spec.preimage (a ≫ Y.isoSpec.hom) ≫ quotientRingInclusion D) =
      Spec.map (Spec.preimage (b ≫ Y.isoSpec.hom) ≫ quotientRingInclusion D) := by
    rw [← cancel_epi (coverScheme D).isoSpec.hom, Spec.map_comp, Spec.map_comp,
      Spec.map_preimage, Spec.map_preimage]
    simpa [quotientMap] using congrArg (· ≫ Y.isoSpec.hom) h
  have h'' := Spec.map_injective h'
  ext c
  exact congrArg (fun φ => CommRingCat.Hom.hom φ c) h''

/-! ### The quotient cocone -/

/-- The equivariance of a cover morphism, read off on the quotient map. -/
theorem coverMap_comp_quotientMap (g : G) :
    (D.map (SingleObj.toEnd G g)).hom.left ≫ quotientMap D = quotientMap D := by
  have h := quotientRingInclusion_comp_coverAction D g
  rw [coverAction] at h
  rw [quotientMap, ← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc,
    ← Spec.map_comp, h]

/-- A ring map into global sections, viewed as a map into the type synonym. -/
def toCoverRing {T : CommRingCat.{u}} (φ : T ⟶ Γ(coverScheme D, ⊤)) : T →+* coverRing D :=
  φ.hom

variable {D} in
/-- Global sections of a `G`-invariant map land in the invariant subring. -/
def descRingHom {Z : Scheme.{u}} (ψ : coverScheme D ⟶ Z)
    (hψ : ∀ g : G, (D.map (SingleObj.toEnd G g)).hom.left ≫ ψ = ψ) :
    Γ(Z, ⊤) ⟶ CommRingCat.of (quotientRing D) :=
  CommRingCat.ofHom (RingHom.codRestrict (toCoverRing D ψ.appTop) (quotientRing D) fun z =>
    (mem_quotientRing_iff D _).mpr fun g => by
      have h := congrArg (fun f => f.appTop.hom z) (hψ g)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      exact h)

omit [IsAffine S] in
theorem descRingHom_comp_quotientRingInclusion {Z : Scheme.{u}} (ψ : coverScheme D ⟶ Z)
    (hψ : ∀ g : G, (D.map (SingleObj.toEnd G g)).hom.left ≫ ψ = ψ) :
    descRingHom ψ hψ ≫ quotientRingInclusion D = ψ.appTop := by
  ext z
  rfl

variable {D} in
/-- The factorization of a `G`-invariant map to an affine scheme through the quotient. -/
def descMap {Z : Scheme.{u}} [IsAffine Z] (ψ : coverScheme D ⟶ Z)
    (hψ : ∀ g : G, (D.map (SingleObj.toEnd G g)).hom.left ≫ ψ = ψ) : quotientScheme D ⟶ Z :=
  Spec.map (descRingHom ψ hψ) ≫ Z.isoSpec.inv

theorem quotientMap_comp_descMap {Z : Scheme.{u}} [IsAffine Z] (ψ : coverScheme D ⟶ Z)
    (hψ : ∀ g : G, (D.map (SingleObj.toEnd G g)).hom.left ≫ ψ = ψ) :
    quotientMap D ≫ descMap ψ hψ = ψ := by
  rw [quotientMap, descMap, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp,
    descRingHom_comp_quotientRingInclusion, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem descMap_comp_structure {Z : Scheme.{u}} [IsAffine Z] {f : Z ⟶ S}
    (ψ : coverScheme D ⟶ Z) (hψ : ∀ g : G, (D.map (SingleObj.toEnd G g)).hom.left ≫ ψ = ψ)
    (h : ψ ≫ f = (D.obj (SingleObj.star G)).obj.hom) :
    descMap ψ hψ ≫ f = quotientStructure D := by
  apply quotientMap_cancel D
  rw [reassoc_of% quotientMap_comp_descMap, quotientMap_comp_quotientStructure, h]

omit [IsAffine S] in
/-- The leg of a cocone over `D` is invariant under the group. -/
theorem cocone_leg_invariant (s : Cocone D) (g : G) :
    (D.map (SingleObj.toEnd G g)).hom.left ≫ (s.ι.app (SingleObj.star G)).hom.left =
      (s.ι.app (SingleObj.star G)).hom.left :=
  congrArg (fun f => f.hom.left) (s.w (SingleObj.toEnd G g))

section FiniteEtale

variable [IsLocallyNoetherian S]

instance isNoetherianRing_globalSections : IsNoetherianRing Γ(S, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩

instance : Module.Finite Γ(S, ⊤) (coverRing D) :=
  Scheme.Hom.finite_appTop (D.obj (SingleObj.star G)).obj.hom

instance : Algebra.Etale Γ(S, ⊤) (coverRing D) :=
  HasRingHomProperty.appTop @Etale (D.obj (SingleObj.star G)).obj.hom inferInstance

variable [Finite G]

theorem quotientRing_finite_etale :
    Module.Finite Γ(S, ⊤) (quotientRing D) ∧ Algebra.Etale Γ(S, ⊤) (quotientRing D) :=
  invariantAlgebraFiniteEtale Γ(S, ⊤) (coverRing D) G

instance : IsFinite (quotientStructure D) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D)))) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
    exact (quotientRing_finite_etale D).1
  rw [quotientStructure]
  infer_instance

instance : Etale (quotientStructure D) := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom,
      RingHom.etale_algebraMap]
    exact (quotientRing_finite_etale D).2
  rw [quotientStructure]
  infer_instance

/-- The quotient as a finite étale cover. -/
def quotientCover : Cover S := cover (quotientStructure D)

/-- The leg of the quotient cocone. -/
def quotientCoconeMap : D.obj (SingleObj.star G) ⟶ quotientCover D :=
  ObjectProperty.homMk (Over.homMk (quotientMap D) (quotientMap_comp_quotientStructure D))

/-- The quotient cocone. -/
def quotientCocone : Cocone D where
  pt := quotientCover D
  ι :=
    { app := fun _ => quotientCoconeMap D
      naturality := fun _ _ g => by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        change (D.map g).hom.left ≫ quotientMap D = quotientMap D ≫ 𝟙 _
        rw [Category.comp_id]
        exact coverMap_comp_quotientMap D g }

/-- The quotient cocone is a colimit in finite étale covers. -/
def quotientCoconeIsColimit : IsColimit (quotientCocone D) where
  desc s := ObjectProperty.homMk (Over.homMk
    (descMap (s.ι.app (SingleObj.star G)).hom.left (cocone_leg_invariant D s))
    (descMap_comp_structure D _ _ (Over.w (s.ι.app (SingleObj.star G)).hom)))
  fac s _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact quotientMap_comp_descMap D _ _
  uniq s m hm := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply quotientMap_cancel D
    exact (congrArg (fun f => f.hom.left) (hm (SingleObj.star G))).trans
      (quotientMap_comp_descMap D _ _).symm

/-! ### Geometric points -/

section GeometricPoints

variable {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

/-- The ring map of a geometric point of the acted-on cover. -/
def fiberRingHom (x : Fiber s (D.obj (SingleObj.star G))) :
    Γ(coverScheme D, ⊤) ⟶ CommRingCat.of Ω :=
  affinePointEquiv (coverScheme D) (.of Ω) x.left

omit [IsLocallyNoetherian S] [Finite G] in
theorem fiberRingHom_injective : Function.Injective (fiberRingHom D s) := by
  intro x y h
  apply Over.OverMorphism.ext
  exact (affinePointEquiv _ _).injective h

omit [IsLocallyNoetherian S] [Finite G] in
theorem appTop_comp_fiberRingHom (x : Fiber s (D.obj (SingleObj.star G))) :
    (D.obj (SingleObj.star G)).obj.hom.appTop ≫ fiberRingHom D s x =
      affinePointEquiv S (.of Ω) s := by
  rw [fiberRingHom, ← affinePointEquiv_comp, Over.w x]
  rfl

omit [IsLocallyNoetherian S] [Finite G] in
theorem fiberRingHom_map (g : G) (x : Fiber s (D.obj (SingleObj.star G))) :
    fiberRingHom D s ((pointFunctor s).map (D.map (SingleObj.toEnd G g)) x) =
      coverAction D g ≫ fiberRingHom D s x := by
  rw [pointFunctor_map, fiberRingHom, fiberRingHom, Over.comp_left, affinePointEquiv_comp]
  rfl

omit [IsLocallyNoetherian S] [Finite G] in
theorem exists_fiberRingHom (φ : Γ(coverScheme D, ⊤) ⟶ CommRingCat.of Ω)
    (hφ : (D.obj (SingleObj.star G)).obj.hom.appTop ≫ φ = affinePointEquiv S (.of Ω) s) :
    ∃ x, fiberRingHom D s x = φ := by
  refine ⟨Over.homMk ((affinePointEquiv _ _).symm φ) ?_, ?_⟩
  · apply (affinePointEquiv S (.of Ω)).injective
    rw [affinePointEquiv_comp, Equiv.apply_symm_apply, hφ]
    rfl
  · exact Equiv.apply_symm_apply _ _

/-- The ring map of a geometric point of the quotient. -/
def quotientFiberRingHom (t : Fiber s (quotientCover D)) :
    CommRingCat.of (quotientRing D) ⟶ CommRingCat.of Ω :=
  Spec.preimage t.left

theorem SpecMap_quotientFiberRingHom (t : Fiber s (quotientCover D)) :
    Spec.map (quotientFiberRingHom D s t) = t.left :=
  Spec.map_preimage _

theorem quotientFiberRingHom_injective : Function.Injective (quotientFiberRingHom D s) := by
  intro t t' h
  apply Over.OverMorphism.ext
  have h' := congrArg Spec.map h
  rwa [SpecMap_quotientFiberRingHom, SpecMap_quotientFiberRingHom] at h'

theorem quotientFiberRingHom_map (x : Fiber s (D.obj (SingleObj.star G))) :
    quotientFiberRingHom D s
        ((pointFunctor s).map ((quotientCocone D).ι.app (SingleObj.star G)) x) =
      quotientRingInclusion D ≫ fiberRingHom D s x := by
  apply Spec.map_injective
  rw [SpecMap_quotientFiberRingHom, Spec.map_comp, fiberRingHom, SpecMap_affinePointEquiv,
    Category.assoc]
  rfl

theorem algebraMap_comp_quotientFiberRingHom (t : Fiber s (quotientCover D)) :
    CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D)) ≫ quotientFiberRingHom D s t =
      affinePointEquiv S (.of Ω) s := by
  apply Spec.map_injective
  have hw : t.left ≫ quotientStructure D = s := Over.w t
  rw [Spec.map_comp, SpecMap_quotientFiberRingHom, SpecMap_affinePointEquiv]
  calc _ = (t.left ≫ quotientStructure D) ≫ S.isoSpec.hom := by
        rw [quotientStructure, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = s ≫ S.isoSpec.hom := by rw [hw]

variable [IsAlgClosed Ω]

/-- Every geometric point of the quotient lifts to the cover. -/
theorem quotientCocone_surjective :
    Function.Surjective
      ((pointFunctor s).map ((quotientCocone D).ι.app (SingleObj.star G))) := by
  intro t
  let _ : Algebra Γ(S, ⊤) Ω := (affinePointEquiv S (.of Ω) s).hom.toAlgebra
  obtain ⟨hsurj, -⟩ := invariantAlgebraGeometricPoints Γ(S, ⊤) (coverRing D) G Ω
  let f : quotientRing D →ₐ[Γ(S, ⊤)] Ω :=
    { toRingHom := (quotientFiberRingHom D s t).hom
      commutes' := fun r =>
        congrArg (fun φ => CommRingCat.Hom.hom φ r) (algebraMap_comp_quotientFiberRingHom D s t) }
  obtain ⟨x', hx'⟩ := hsurj f
  obtain ⟨x, hx⟩ := exists_fiberRingHom D s (CommRingCat.ofHom x'.toRingHom) (by
    ext r
    exact x'.commutes r)
  refine ⟨x, quotientFiberRingHom_injective D s ?_⟩
  rw [quotientFiberRingHom_map, hx]
  ext c
  exact DFunLike.congr_fun hx' c

/-- Two geometric points of the cover have the same image exactly when they lie
in one group orbit. -/
theorem quotientCocone_orbit (x y : Fiber s (D.obj (SingleObj.star G))) :
    (pointFunctor s).map ((quotientCocone D).ι.app (SingleObj.star G)) x =
        (pointFunctor s).map ((quotientCocone D).ι.app (SingleObj.star G)) y ↔
      ∃ g : G, y = (pointFunctor s).map (D.map (SingleObj.toEnd G g)) x := by
  let _ : Algebra Γ(S, ⊤) Ω := (affinePointEquiv S (.of Ω) s).hom.toAlgebra
  obtain ⟨-, horbit⟩ := invariantAlgebraGeometricPoints Γ(S, ⊤) (coverRing D) G Ω
  let F : Fiber s (D.obj (SingleObj.star G)) → (coverRing D →ₐ[Γ(S, ⊤)] Ω) := fun z =>
    { toRingHom := (fiberRingHom D s z).hom
      commutes' := fun r =>
        congrArg (fun φ => CommRingCat.Hom.hom φ r) (appTop_comp_fiberRingHom D s z) }
  constructor
  · intro h
    have h' := congrArg (quotientFiberRingHom D s) h
    rw [quotientFiberRingHom_map, quotientFiberRingHom_map] at h'
    have hcomp : (F x).comp (quotientRing D).val = (F y).comp (quotientRing D).val := by
      ext c
      exact congrArg (fun φ => CommRingCat.Hom.hom φ c) h'
    obtain ⟨g, hg⟩ := (horbit (F x) (F y)).mp hcomp
    refine ⟨g⁻¹, fiberRingHom_injective D s ?_⟩
    rw [fiberRingHom_map]
    ext a
    exact DFunLike.congr_fun hg a
  · rintro ⟨g, rfl⟩
    apply quotientFiberRingHom_injective D s
    rw [quotientFiberRingHom_map, quotientFiberRingHom_map, fiberRingHom_map, ← Category.assoc,
      quotientRingInclusion_comp_coverAction]

end GeometricPoints

end FiniteEtale

end Construction

/-- Over an affine locally noetherian base, the spectrum of the invariant global
sections is a quotient cocone with the geometric orbit property. -/
theorem affineFiniteGroupQuotientCocones : AffineFiniteGroupQuotientCocones.{u} := by
  intro S _ _ G _ _ D
  exact ⟨quotientCocone D, ⟨quotientCoconeIsColimit D⟩, fun Ω _ _ s =>
    ⟨quotientCocone_surjective D s, quotientCocone_orbit D s⟩⟩

end Langlands.AlgebraicGeometry.FiniteEtale
