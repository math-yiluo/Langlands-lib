import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines
import Langlands.AlgebraicGeometry.LinearSystem.Morphism
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof

/-! # Morphisms to projective space glued from local homogeneous coordinates

Let `X` be a scheme over a commutative ring `K`, and let `V i` be opens of `X`. On each
`V i` let `c i 0, …, c i m` be functions. Suppose that on every overlap `V i ⊓ V k` the
second family is a unit multiple of the first, and that at every point some `c i σ` is
invertible. Then the local chart maps `[c i 0 : ⋯ : c i m]` glue to a morphism
`X ⟶ ProjectiveSpace K m`. Two field-valued points with the same image have proportional
coordinate vectors.
-/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.CoordinateAtlas

open Langlands.AlgebraicGeometry.LinearSystem

variable {K : Type u} [CommRing K] {X Z Z' : Scheme.{u}}

section pull

/-- Pull a function on `U` back to a global function along a morphism landing in `U`. -/
def pull (g : Z ⟶ X) {U : X.Opens} (hg : ∀ z, g z ∈ U) : Γ(X, U) →+* Γ(Z, ⊤) :=
  (g.appLE U ⊤ fun z _ ↦ hg z).hom

lemma comp_pull (h : Z' ⟶ Z) (g : Z ⟶ X) {U : X.Opens} (hg : ∀ z, g z ∈ U) :
    h.appTop.hom.comp (pull g hg) = pull (h ≫ g) fun z ↦ hg (h z) := by
  have e : h.appTop = h.appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE]
    simp
  rw [pull, pull, e, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

lemma pull_res (g : Z ⟶ X) {U U' : X.Opens} (hUU' : U' ≤ U) (hg : ∀ z, g z ∈ U')
    (f : Γ(X, U)) :
    pull g hg (X.presheaf.map (homOfLE hUU').op f) = pull g (fun z ↦ hUU' (hg z)) f := by
  rw [pull, pull, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma basicOpen_pull (g : Z ⟶ X) {U : X.Opens} (hg : ∀ z, g z ∈ U) (f : Γ(X, U)) :
    Z.basicOpen (pull g hg f) = g ⁻¹ᵁ X.basicOpen f := by
  rw [pull, Scheme.basicOpen_appLE, top_inf_eq]

lemma isUnit_pull_iff (g : Z ⟶ X) {U : X.Opens} (hg : ∀ z, g z ∈ U) (f : Γ(X, U)) :
    IsUnit (pull g hg f) ↔ ∀ z, g z ∈ X.basicOpen f := by
  constructor
  · intro hu z
    have h := Scheme.basicOpen_of_isUnit (X := Z) hu
    rw [basicOpen_pull] at h
    change z ∈ g ⁻¹ᵁ X.basicOpen f
    rw [h]
    trivial
  · intro h
    apply Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines.isUnit_of_basicOpen_eq_top
    rw [basicOpen_pull]
    exact eq_top_iff.mpr fun z _ ↦ h z

end pull

variable (p : X ⟶ Spec (CommRingCat.of K)) {m : ℕ} {ι : Type*} {V : ι → X.Opens}
  (c : ∀ i, Fin (m + 1) → Γ(X, V i))

/-- Local coordinate families forming an atlas: on overlaps one family is a unit multiple
of the other, and at every point some coordinate of some family is invertible. -/
structure IsAtlas : Prop where
  covers : ∀ x : X, ∃ i σ, x ∈ X.basicOpen (c i σ)
  compat : ∀ i k, ∃ u : (Γ(X, V i ⊓ V k))ˣ, ∀ σ,
    X.presheaf.map (homOfLE inf_le_right).op (c k σ) =
      (u : Γ(X, V i ⊓ V k)) * X.presheaf.map (homOfLE inf_le_left).op (c i σ)

section coord

/-- The ring map `X_σ ↦ c i σ` pulled back along a point landing in `V i`. -/
def coordRingHom (g : Z ⟶ X) (i : ι) (hg : ∀ z, g z ∈ V i) :
    ProjectiveCoordinateRing K m →+* Γ(Z, ⊤) :=
  MvPolynomial.eval₂Hom (Scheme.Modules.scalarsFromBase (g ≫ p)) fun σ ↦ pull g hg (c i σ)

@[simp]
lemma coordRingHom_X (g : Z ⟶ X) (i : ι) (hg : ∀ z, g z ∈ V i) (σ : Fin (m + 1)) :
    coordRingHom p c g i hg (MvPolynomial.X σ) = pull g hg (c i σ) :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[simp]
lemma coordRingHom_C (g : Z ⟶ X) (i : ι) (hg : ∀ z, g z ∈ V i) (k : K) :
    coordRingHom p c g i hg (MvPolynomial.C k) = Scheme.Modules.scalarsFromBase (g ≫ p) k :=
  MvPolynomial.eval₂Hom_C _ _ _

lemma comp_coordRingHom (h : Z' ⟶ Z) (g : Z ⟶ X) (i : ι) (hg : ∀ z, g z ∈ V i) :
    h.appTop.hom.comp (coordRingHom p c g i hg) = coordRingHom p c (h ≫ g) i fun z ↦ hg (h z) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    rw [RingHom.comp_apply, coordRingHom_C, coordRingHom_C, Category.assoc,
      scalarsFromBase_comp h (g ≫ p)]
    rfl
  · intro σ
    rw [RingHom.comp_apply, coordRingHom_X, coordRingHom_X, ← comp_pull h g hg,
      RingHom.comp_apply]

lemma coordRingHom_congr {g g' : Z ⟶ X} (h : g = g') (i : ι) (hg : ∀ z, g z ∈ V i) :
    coordRingHom p c g i hg = coordRingHom p c g' i (h ▸ hg) := by
  subst h
  rfl

variable {p c}

lemma mem_of_mem_basicOpen {g : Z ⟶ X} {i : ι} {σ : Fin (m + 1)}
    (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) : ∀ z, g z ∈ V i :=
  fun z ↦ X.basicOpen_le _ (hg z)

lemma isUnit_coordRingHom_X {g : Z ⟶ X} {i : ι} {σ : Fin (m + 1)}
    (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) :
    IsUnit (coordRingHom p c g i (mem_of_mem_basicOpen hg) (MvPolynomial.X σ)) := by
  rw [coordRingHom_X, isUnit_pull_iff]
  exact hg

/-- On an overlap, the second coordinate ring map is the first one rescaled by the unit
transition function according to degree. -/
lemma coordRingHom_scale (hc : IsAtlas c) {g : Z ⟶ X} {i k : ι} (hi : ∀ z, g z ∈ V i)
    (hk : ∀ z, g z ∈ V k) :
    ∃ a : Γ(Z, ⊤), IsUnit a ∧ ∀ (n : ℕ) (f : ProjectiveCoordinateRing K m),
      f ∈ projectiveSpaceGrading K m n →
        coordRingHom p c g k hk f = a ^ n * coordRingHom p c g i hi f := by
  obtain ⟨u, hu⟩ := hc.compat i k
  have hik : ∀ z, g z ∈ V i ⊓ V k := fun z ↦ ⟨hi z, hk z⟩
  refine ⟨pull g hik u, u.isUnit.map _, fun n f hf ↦ ?_⟩
  have hx : (fun σ ↦ pull g hk (c k σ)) = fun σ ↦ pull g hik u * pull g hi (c i σ) := by
    funext σ
    rw [← pull_res g inf_le_right hik, hu σ, map_mul, pull_res g inf_le_left hik]
  rw [coordRingHom, coordRingHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, hx]
  exact eval₂_mul_of_isHomogeneous _ _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hf)

lemma isUnit_pull_iff_of_atlas (hc : IsAtlas c) {g : Z ⟶ X} {i k : ι} (hi : ∀ z, g z ∈ V i)
    (hk : ∀ z, g z ∈ V k) (σ : Fin (m + 1)) :
    IsUnit (pull g hi (c i σ)) ↔ IsUnit (pull g hk (c k σ)) := by
  obtain ⟨u, hu⟩ := hc.compat i k
  have hik : ∀ z, g z ∈ V i ⊓ V k := fun z ↦ ⟨hi z, hk z⟩
  rw [← pull_res g inf_le_right hik, hu σ, map_mul, pull_res g inf_le_left hik]
  have ha : IsUnit (pull g hik (u : Γ(X, V i ⊓ V k))) := u.isUnit.map _
  exact ⟨fun h ↦ ha.mul h, fun h ↦ isUnit_of_mul_isUnit_right h⟩

end coord

section pointMap

/-- The morphism `Z ⟶ ℙᵐ` through the chart `D₊(X_σ)` given by the pulled-back coordinates
of chart `i`, for a `Z`-point landing in the basic open of `c i σ`. -/
def pointMap (g : Z ⟶ X) (i : ι) (σ : Fin (m + 1)) (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) :
    Z ⟶ ProjectiveSpace K m :=
  chartMap (projectiveSpaceGrading K m) (coordRingHom p c g i (mem_of_mem_basicOpen hg))
    (projectiveSpace_X_mem K m σ) one_pos (isUnit_coordRingHom_X hg)

lemma pointMap_congr {g g' : Z ⟶ X} (h : g = g') (i : ι) (σ : Fin (m + 1))
    (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) :
    pointMap p c g i σ hg = pointMap p c g' i σ (h ▸ hg) := by
  subst h
  rfl

/-- Point maps are natural in the source. -/
lemma comp_pointMap (h : Z' ⟶ Z) {g : Z ⟶ X} {i : ι} {σ : Fin (m + 1)}
    (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) :
    h ≫ pointMap p c g i σ hg = pointMap p c (h ≫ g) i σ fun z ↦ hg (h z) := by
  rw [pointMap, pointMap, comp_chartMap]
  exact chartMap_ringHom_congr _ (comp_coordRingHom p c h g i _) _ _ _

/-- The point map depends neither on the chart nor on the chosen invertible coordinate. -/
lemma pointMap_eq (hc : IsAtlas c) {g : Z ⟶ X} {i k : ι} {σ τ : Fin (m + 1)}
    (hσ : ∀ z, g z ∈ X.basicOpen (c i σ)) (hτ : ∀ z, g z ∈ X.basicOpen (c k τ)) :
    pointMap p c g i σ hσ = pointMap p c g k τ hτ := by
  have hi := mem_of_mem_basicOpen hσ
  have hk := mem_of_mem_basicOpen hτ
  obtain ⟨a, -, ha⟩ := coordRingHom_scale (p := p) hc hi hk
  have hu : IsUnit (coordRingHom p c g i hi (MvPolynomial.X τ)) := by
    rw [coordRingHom_X, isUnit_pull_iff_of_atlas hc hi hk τ, ← coordRingHom_X p c g k hk]
    exact isUnit_coordRingHom_X hτ
  rw [pointMap, pointMap, chartMap_eq _ _ (projectiveSpace_X_mem K m σ) one_pos
    (projectiveSpace_X_mem K m τ) one_pos _ hu]
  exact (chartMap_eq_of_scale _ (coordRingHom p c g i hi) (coordRingHom p c g k hk)
    (projectiveSpace_X_mem K m τ) one_pos hu (isUnit_coordRingHom_X hτ) a ha).symm

/-- Point maps lie over `Spec K`. -/
lemma pointMap_toSpec {g : Z ⟶ X} {i : ι} {σ : Fin (m + 1)}
    (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) :
    pointMap p c g i σ hg ≫ projectiveSpaceToSpec K m = g ≫ p := by
  change chartMap (projectiveSpaceGrading K m) _ _ _ _ ≫
    Proj.toSpecZero (projectiveSpaceGrading K m) ≫
      Spec.map (CommRingCat.ofHom (projectiveSpaceConstants K m)) = g ≫ p
  rw [← Category.assoc, chartMap_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  conv_rhs => rw [← toSpecΓ_SpecMap_scalarsFromBase (g ≫ p)]
  congr 3
  ext k
  rw [RingHom.comp_apply, RingHom.comp_apply]
  erw [awayLift_fromZeroRingHom]
  exact coordRingHom_C p c g i _ k

/-- The preimage of a coordinate chart under a point map. -/
lemma pointMap_preimage {g : Z ⟶ X} {i : ι} {σ : Fin (m + 1)}
    (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) (τ : Fin (m + 1)) :
    pointMap p c g i σ hg ⁻¹ᵁ projectiveSpaceCoordinateOpen K m τ =
      Z.basicOpen (pull g (mem_of_mem_basicOpen hg) (c i τ)) := by
  rw [← coordRingHom_X p c g i (mem_of_mem_basicOpen hg) τ]
  exact chartMap_preimage_basicOpen _ _ _ one_pos (projectiveSpace_X_mem K m τ) one_pos _

end pointMap

section glue

variable {p c}

lemma isOpenCover (hc : IsAtlas c) :
    TopologicalSpace.IsOpenCover fun a : ι × Fin (m + 1) ↦ X.basicOpen (c a.1 a.2) :=
  eq_top_iff.mpr fun x _ ↦ by
    obtain ⟨i, σ, h⟩ := hc.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, σ), h⟩

variable (p) (hc : IsAtlas c)

/-- The morphism to projective space glued from the local coordinate families. -/
def atlasMap : X ⟶ ProjectiveSpace K m :=
  (X.openCoverOfIsOpenCover _ (isOpenCover hc)).glueMorphisms
    (fun a ↦ pointMap p c (X.basicOpen (c a.1 a.2)).ι a.1 a.2 (ι_mem _)) fun a b ↦ by
      rw [comp_pointMap, comp_pointMap]
      exact (pointMap_congr p c Limits.pullback.condition _ _ _).trans (pointMap_eq p c hc _ _)

lemma ι_atlasMap (a : ι × Fin (m + 1)) :
    (X.basicOpen (c a.1 a.2)).ι ≫ atlasMap p hc =
      pointMap p c (X.basicOpen (c a.1 a.2)).ι a.1 a.2 (ι_mem _) :=
  (X.openCoverOfIsOpenCover _ (isOpenCover hc)).ι_glueMorphisms _ _ a

/-- Along a point landing in the basic open of `c i σ`, the glued map is the point map. -/
lemma comp_atlasMap (g : Z ⟶ X) (i : ι) (σ : Fin (m + 1))
    (hg : ∀ z, g z ∈ X.basicOpen (c i σ)) :
    g ≫ atlasMap p hc = pointMap p c g i σ hg := by
  apply Scheme.hom_ext_of_forall
  intro z
  obtain ⟨k, τ, hk⟩ := hc.covers (g z)
  refine ⟨g ⁻¹ᵁ X.basicOpen (c k τ), hk, ?_⟩
  rw [← morphismRestrict_ι_assoc, ι_atlasMap p hc (k, τ), comp_pointMap, comp_pointMap,
    pointMap_congr p c (morphismRestrict_ι g _)]
  exact pointMap_eq p c hc _ _

lemma atlasMap_toSpec : atlasMap p hc ≫ projectiveSpaceToSpec K m = p := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨k, τ, hk⟩ := hc.covers x
  refine ⟨_, hk, ?_⟩
  rw [← Category.assoc, comp_atlasMap p hc _ k τ (ι_mem _), pointMap_toSpec]

end glue

section points

variable {p c}

lemma exists_isUnit_pull (hc : IsAtlas c) {F : Type u} [Field F]
    (t : Spec (CommRingCat.of F) ⟶ X) {i : ι} (ht : ∀ z, t z ∈ V i) :
    ∃ σ, IsUnit (pull t ht (c i σ)) := by
  obtain ⟨k, τ, hk⟩ := hc.covers (t (IsLocalRing.closedPoint F))
  have hk' : ∀ z, t z ∈ X.basicOpen (c k τ) := fun z ↦ by
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint F)]
  exact ⟨τ, (isUnit_pull_iff_of_atlas hc ht (mem_of_mem_basicOpen hk') τ).mpr
    ((isUnit_pull_iff _ _ _).mpr hk')⟩

/-- Two field-valued points with the same image in projective space have proportional
coordinate vectors, whichever charts contain them. -/
theorem exists_unit_of_comp_eq (hc : IsAtlas c) {F : Type u} [Field F]
    {t t' : Spec (CommRingCat.of F) ⟶ X} {i k : ι} (ht : ∀ z, t z ∈ V i)
    (ht' : ∀ z, t' z ∈ V k) (H : t ≫ atlasMap p hc = t' ≫ atlasMap p hc) :
    ∃ a : Γ(Spec (CommRingCat.of F), ⊤), IsUnit a ∧
      ∀ σ, pull t' ht' (c k σ) = a * pull t ht (c i σ) := by
  set pt := IsLocalRing.closedPoint F
  obtain ⟨σ₀, hσ₀⟩ := exists_isUnit_pull hc t ht
  have hσ₀' : ∀ z, t z ∈ X.basicOpen (c i σ₀) := (isUnit_pull_iff t ht _).mp hσ₀
  have hy : ((t ≫ atlasMap p hc) pt) ∈ (⊤ : (ProjectiveSpace K m).Opens) := trivial
  rw [← iSup_projectiveSpaceCoordinateOpen K m] at hy
  obtain ⟨τ, hτ⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  -- the coordinate `τ` is invertible at both points
  have hunit : ∀ (s : Spec (CommRingCat.of F) ⟶ X) (l : ι) (hs : ∀ z, s z ∈ V l),
      s ≫ atlasMap p hc = t ≫ atlasMap p hc → IsUnit (pull s hs (c l τ)) := by
    intro s l hs hs'
    obtain ⟨ρ, hρ⟩ := exists_isUnit_pull hc s hs
    have hρ' := (isUnit_pull_iff s hs _).mp hρ
    have hpre := pointMap_preimage p c hρ' τ
    rw [← comp_atlasMap p hc s l ρ hρ', hs'] at hpre
    have hmem : pt ∈ (Spec (CommRingCat.of F)).basicOpen (pull s (mem_of_mem_basicOpen hρ')
        (c l τ)) := by
      rw [← hpre]
      exact hτ
    apply Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines.isUnit_of_basicOpen_eq_top
    exact eq_top_iff.mpr fun z _ ↦ by rwa [Subsingleton.elim z pt]
  have hu := hunit t i ht rfl
  have hu' := hunit t' k ht' H.symm
  have hτt : ∀ z, t z ∈ X.basicOpen (c i τ) := (isUnit_pull_iff t ht _).mp hu
  have hτt' : ∀ z, t' z ∈ X.basicOpen (c k τ) := (isUnit_pull_iff t' ht' _).mp hu'
  have H' := H
  rw [comp_atlasMap p hc t i τ hτt, comp_atlasMap p hc t' k τ hτt', pointMap, pointMap] at H'
  have hA := awayLift_eq_of_chartMap_eq _ _ _ _ one_pos _ _ H'
  refine ⟨pull t' ht' (c k τ) * ((hu.unit⁻¹ : (Γ(Spec (CommRingCat.of F), ⊤))ˣ) :
    Γ(Spec (CommRingCat.of F), ⊤)), hu'.mul (Units.isUnit _), fun σ ↦ ?_⟩
  have hmem : (MvPolynomial.X σ : ProjectiveCoordinateRing K m) ∈
      projectiveSpaceGrading K m (1 • 1) := by
    simpa using projectiveSpace_X_mem K m σ
  have key := congrArg (fun φ ↦ φ (HomogeneousLocalization.Away.mk
    (projectiveSpaceGrading K m) (projectiveSpace_X_mem K m τ) 1 (MvPolynomial.X σ) hmem)) hA
  set r := awayLift (projectiveSpaceGrading K m) (coordRingHom p c t i _) _
    (isUnit_coordRingHom_X hτt) (HomogeneousLocalization.Away.mk
      (projectiveSpaceGrading K m) (projectiveSpace_X_mem K m τ) 1 (MvPolynomial.X σ) hmem)
  have h1 := (awayLift_mk_eq_iff (projectiveSpaceGrading K m)
    (coordRingHom p c t i (mem_of_mem_basicOpen hτt)) (isUnit_coordRingHom_X hτt)
    (projectiveSpace_X_mem K m τ) 1 (MvPolynomial.X σ) hmem r).mp rfl
  have h2 := (awayLift_mk_eq_iff (projectiveSpaceGrading K m)
    (coordRingHom p c t' k (mem_of_mem_basicOpen hτt')) (isUnit_coordRingHom_X hτt')
    (projectiveSpace_X_mem K m τ) 1 (MvPolynomial.X σ) hmem r).mp key.symm
  simp only [coordRingHom_X, pow_one] at h1 h2
  rw [h2, h1]
  calc r * pull t' ht' (c k τ)
      = r * pull t' ht' (c k τ) * (((hu.unit⁻¹ : (Γ(Spec (CommRingCat.of F), ⊤))ˣ) :
          Γ(Spec (CommRingCat.of F), ⊤)) * pull t ht (c i τ)) := by
        rw [IsUnit.val_inv_mul, mul_one]
    _ = _ := by ring

end points

end Langlands.AlgebraicGeometry.CoordinateAtlas
