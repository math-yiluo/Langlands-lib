import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismStatement
import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismCompatibilityProof

/-! # Analytifications of morphisms of schemes: existence, uniqueness and composition -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification.MorphismComparison

open Set Topology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Composition

variable {A B C : Type v} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] (P : FinitePolynomialPresentation K A)
  (Q : FinitePolynomialPresentation K B) (R : FinitePolynomialPresentation K C)

/-- Maps of analytifications compose like the algebra maps inducing them. -/
theorem baseMap_baseMap (f₁ : A →ₐ[K] B) (f₂ : B →ₐ[K] C) (f₃ : A →ₐ[K] C)
    (h : ∀ a, f₂ (f₁ a) = f₃ a) (z : Space K R) :
    baseMap K P Q f₁ (baseMap K Q R f₂ z) = baseMap K P R f₃ z := by
  apply SeminormComparison.pointSeminorm_injective K P
  ext a
  rw [pointSeminorm_baseMap, pointSeminorm_baseMap, pointSeminorm_baseMap, h]

/-- An algebra map fixing every element induces the identity of the analytification. -/
theorem baseMap_eq_self (φ : A →ₐ[K] A) (hφ : ∀ a, φ a = a) (z : Space K P) :
    baseMap K P P φ z = z := by
  apply SeminormComparison.pointSeminorm_injective K P
  ext a
  rw [pointSeminorm_baseMap, hφ]

end Composition

section Localization

variable {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)

/-- A `K`-algebra map which is a localization away from one element induces an open
embedding of analytifications. -/
theorem isOpenEmbedding_baseMap_of_localization (φ : A →ₐ[K] B) (a : A)
    (h : letI := φ.toRingHom.toAlgebra; IsLocalization.Away a B) :
    IsOpenEmbedding (baseMap K P Q φ) := by
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algHom φ
  let : IsLocalization.Away a B := h
  have heq : IsScalarTower.toAlgHom K A B = φ := by
    ext b
    rfl
  rw [← heq]
  exact ImmersionComparison.isOpenEmbedding_baseMap_away K P Q a

end Localization

end Langlands.Analytic.AffineAnalytification.MorphismComparison

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology Set
open Langlands.Analytic.AffineSchemeAnalytification

namespace MorphismExistence

section Algebraic

variable {K : Type u} [CommRing K] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of K)} {f' : Y ⟶ Spec (CommRingCat.of K)}

/-- Restriction of sections along two successive inclusions of affine opens is
restriction along the composite inclusion. -/
theorem restriction_restriction {U V W : X.affineOpens} (hVU : (V : X.Opens) ≤ U)
    (hWV : (W : X.Opens) ≤ V) (a : CoordinateRing (structureMap f U)) :
    restriction f hWV (restriction f hVU a) = restriction f (hWV.trans hVU) a := by
  change (X.homOfLE hWV).appTop ((X.homOfLE hVU).appTop a) =
    (X.homOfLE (hWV.trans hVU)).appTop a
  rw [← X.homOfLE_homOfLE hWV hVU, Scheme.Hom.comp_appTop]
  exact (CommRingCat.comp_apply _ _ _).symm

/-- Restriction along the identity inclusion is the identity. -/
theorem restriction_self (U : X.affineOpens) (a : CoordinateRing (structureMap f U)) :
    restriction f (le_refl (U : X.Opens)) a = a := by
  change (X.homOfLE (le_refl (U : X.Opens))).appTop a = a
  rw [Scheme.homOfLE_rfl, Scheme.Hom.id_appTop]
  rfl

/-- Restricting the induced coordinate map to a smaller affine open of the source. -/
theorem restriction_openCoordinateMap (g : X ⟶ Y) (hg : g ≫ f' = f) {U U' : X.affineOpens}
    {V : Y.affineOpens} (hU : (U' : X.Opens) ≤ U) (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (a : CoordinateRing (structureMap f' V)) :
    restriction f hU (openCoordinateMap g hg h a) = openCoordinateMap g hg (hU.trans h) a := by
  change (X.homOfLE hU).appTop ((g.resLE (V : Y.Opens) (U : X.Opens) h).appTop a) =
    (g.resLE (V : Y.Opens) (U' : X.Opens) (hU.trans h)).appTop a
  rw [← Scheme.Hom.map_resLE g h hU, Scheme.Hom.comp_appTop]
  exact (CommRingCat.comp_apply _ _ _).symm

/-- Composing the induced coordinate map with restriction from a larger affine open of
the target. -/
theorem openCoordinateMap_restriction (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens}
    {V V' : Y.affineOpens} (hV : (V : Y.Opens) ≤ V') (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (h' : (U : X.Opens) ≤ g ⁻¹ᵁ (V' : Y.Opens)) (a : CoordinateRing (structureMap f' V')) :
    openCoordinateMap g hg h (restriction f' hV a) = openCoordinateMap g hg h' a := by
  change (g.resLE (V : Y.Opens) (U : X.Opens) h).appTop ((Y.homOfLE hV).appTop a) =
    (g.resLE (V' : Y.Opens) (U : X.Opens) h').appTop a
  rw [← Scheme.Hom.resLE_map g h hV, Scheme.Hom.comp_appTop]
  exact (CommRingCat.comp_apply _ _ _).symm

end Algebraic

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (f' : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType f']

/-- The restriction maps of affine analytifications compose. -/
theorem localMap_localMap {U V W : X.affineOpens} (hVU : (V : X.Opens) ≤ U)
    (hWV : (W : X.Opens) ≤ V) (y : LocalSpace K f W) :
    localMap K f hVU (localMap K f hWV y) = localMap K f (hWV.trans hVU) y :=
  AffineAnalytification.MorphismComparison.baseMap_baseMap K _ _ _ _ _ _
    (fun a => restriction_restriction hVU hWV a) y

/-- The restriction map along the identity inclusion is the identity. -/
theorem localMap_self (U : X.affineOpens) (y : LocalSpace K f U) :
    localMap K f (le_refl (U : X.Opens)) y = y :=
  AffineAnalytification.MorphismComparison.baseMap_eq_self K _ _
    (fun a => restriction_self U a) y

/-- The local map induced by `g` on a smaller affine open of the source. -/
theorem morphismLocalMap_localMap (g : X ⟶ Y) (hg : g ≫ f' = f) {U U' : X.affineOpens}
    {V : Y.affineOpens} (hU : (U' : X.Opens) ≤ U) (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (y : LocalSpace K f U') :
    morphismLocalMap K f f' g hg h (localMap K f hU y) =
      morphismLocalMap K f f' g hg (hU.trans h) y :=
  AffineAnalytification.MorphismComparison.baseMap_baseMap K _ _ _ _ _ _
    (fun a => restriction_openCoordinateMap g hg hU h a) y

/-- The local map induced by `g` followed by restriction to a larger affine open of the
target. -/
theorem localMap_morphismLocalMap (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens}
    {V V' : Y.affineOpens} (hV : (V : Y.Opens) ≤ V') (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (h' : (U : X.Opens) ≤ g ⁻¹ᵁ (V' : Y.Opens)) (y : LocalSpace K f U) :
    localMap K f' hV (morphismLocalMap K f f' g hg h y) = morphismLocalMap K f f' g hg h' y :=
  AffineAnalytification.MorphismComparison.baseMap_baseMap K _ _ _ _ _ _
    (fun a => openCoordinateMap_restriction g hg hV h h' a) y

/-- The local maps induced by morphisms compose. -/
theorem morphismLocalMap_comp {Z : Scheme.{u}} (f'' : Z ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f''] (g : X ⟶ Y) (hg : g ≫ f' = f) (g' : Y ⟶ Z)
    (hg' : g' ≫ f'' = f') {U : X.affineOpens} {V : Y.affineOpens} {W : Z.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) (h' : (V : Y.Opens) ≤ g' ⁻¹ᵁ (W : Z.Opens))
    (h'' : (U : X.Opens) ≤ (g ≫ g') ⁻¹ᵁ (W : Z.Opens)) (y : LocalSpace K f U) :
    morphismLocalMap K f' f'' g' hg' h' (morphismLocalMap K f f' g hg h y) =
      morphismLocalMap K f f'' (g ≫ g') (by rw [Category.assoc, hg', hg]) h'' y :=
  AffineAnalytification.MorphismComparison.baseMap_baseMap K _ _ _ _ _ _
    (fun a => (DFunLike.congr_fun (openCoordinateMap_comp g hg g' hg' h h' h'') a).symm) y

/-- Restriction from a principal affine open is an open embedding of analytifications. -/
theorem isOpenEmbedding_localMap_basicOpen (U : X.affineOpens) (a : Γ(X, U.val)) :
    IsOpenEmbedding (localMap K f (X.affineBasicOpen_le a)) :=
  AffineAnalytification.MorphismComparison.isOpenEmbedding_baseMap_of_localization K
    (chartPresentation K f U) (chartPresentation K f (X.affineBasicOpen a))
    (restriction f (X.affineBasicOpen_le a)) (CenterRange.basicOpenGenerator f U a)
    (CenterRange.isLocalization_restriction_basicOpen f U a)

/-- The image of the restriction map along an inclusion `V ⊆ U` of affine opens is the
set of points of `Uᵃⁿ` whose center lies in `V`. -/
theorem range_localMap {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    range (localMap K f hVU) = localCenter K f U ⁻¹' ((V : X.Opens) : Set X) :=
  CenterRange.range_localMap K f (OpenGluing.basicOpenRangeData K f)
    (fun hVU hWV y => localMap_localMap K f hVU hWV y) hVU

/-- The restriction map along every inclusion of affine opens is injective. -/
theorem localMap_injective {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    Function.Injective (localMap K f hVU) := by
  intro w w' hww'
  have hc : localCenter K f V w' = localCenter K f V w := by
    rw [← localCenter_localMap K f hVU w', ← hww', localCenter_localMap]
  have hxV : localCenter K f V w ∈ (V : X.Opens) := center_ι_mem K f V w
  obtain ⟨a, haV, hxa⟩ := U.property.exists_basicOpen_le
    (V := (V : X.Opens)) ⟨localCenter K f V w, hxV⟩ (hVU hxV)
  have hD : ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ V := haV
  have hw : w ∈ range (localMap K f hD) := by
    rw [range_localMap]
    exact hxa
  have hw' : w' ∈ range (localMap K f hD) := by
    rw [range_localMap]
    change localCenter K f V w' ∈ X.basicOpen a
    rw [hc]
    exact hxa
  obtain ⟨d, rfl⟩ := hw
  obtain ⟨d', rfl⟩ := hw'
  rw [localMap_localMap, localMap_localMap] at hww'
  rw [(isOpenEmbedding_localMap_basicOpen K f U a).injective hww']

variable {f} in
/-- A point of the analytification of an affine open `U` of `X` comes, along the
restriction map, from the analytification of a principal affine open of `U` which `g`
maps into an affine open of `Y`. -/
theorem exists_basicOpen_datum (g : X ⟶ Y) (U : X.affineOpens) (y : LocalSpace K f U) :
    ∃ (a : Γ(X, U.val)) (V : Y.affineOpens)
      (_ : ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
      (w : LocalSpace K f (X.affineBasicOpen a)), localMap K f (X.affineBasicOpen_le a) w = y := by
  have hx : localCenter K f U y ∈ (U : X.Opens) := center_ι_mem K f U y
  obtain ⟨V, hV, hgxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := g (localCenter K f U y)) (U := ⊤) trivial
  obtain ⟨a, haV, hxa⟩ := U.property.exists_basicOpen_le
    (V := g ⁻¹ᵁ V) ⟨localCenter K f U y, hgxV⟩ hx
  have hy : y ∈ range (localMap K f (X.affineBasicOpen_le a)) := by
    rw [OpenGluing.range_localMap_basicOpen]
    exact hxa
  obtain ⟨w, hw⟩ := hy
  exact ⟨a, ⟨V, hV⟩, haV, w, hw⟩

/-- A local datum for the value at a point `y` of `Uᵃⁿ` of the analytification of
`g : X ⟶ Y`: an affine open `D ⊆ U` mapped by `g` into an affine open `V` of `Y`, and a
point `w` of `Dᵃⁿ` restricting to `y`. -/
structure LocalDatum (g : X ⟶ Y) (U : X.affineOpens) (y : LocalSpace K f U) where
  /-- The affine open of the source. -/
  D : X.affineOpens
  /-- The affine open of the target. -/
  V : Y.affineOpens
  hDU : (D : X.Opens) ≤ U
  hDV : (D : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)
  /-- The point of `Dᵃⁿ`. -/
  w : LocalSpace K f D
  hw : localMap K f hDU w = y

variable {K f f'}

/-- The value of a local datum: the image of `w` under the local map `Dᵃⁿ → Vᵃⁿ`
induced by `g`, in the glued analytification of `Y`. -/
def LocalDatum.value (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens}
    {y : LocalSpace K f U} (d : LocalDatum K f g U y) : Space K f' :=
  ι K f' d.V (morphismLocalMap K f f' g hg d.hDV d.w)

/-- The value of a local datum depends only on the point. -/
theorem LocalDatum.value_eq (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens}
    {y : LocalSpace K f U} (d₁ d₂ : LocalDatum K f g U y) :
    d₁.value g hg = d₂.value g hg := by
  have hx₁ : localCenter K f U y ∈ (d₁.D : X.Opens) := by
    have hm : localCenter K f d₁.D d₁.w ∈ (d₁.D : X.Opens) := center_ι_mem K f d₁.D d₁.w
    rwa [← localCenter_localMap K f d₁.hDU, d₁.hw] at hm
  have hx₂ : localCenter K f U y ∈ (d₂.D : X.Opens) := by
    have hm : localCenter K f d₂.D d₂.w ∈ (d₂.D : X.Opens) := center_ι_mem K f d₂.D d₂.w
    rwa [← localCenter_localMap K f d₂.hDU, d₂.hw] at hm
  have hgx : g (localCenter K f U y) ∈ (d₁.V : Y.Opens) ⊓ (d₂.V : Y.Opens) :=
    ⟨d₁.hDV hx₁, d₂.hDV hx₂⟩
  obtain ⟨V₃, hV₃, hgxV₃, hV₃le⟩ := exists_isAffineOpen_mem_and_subset hgx
  obtain ⟨a, haW, hxa⟩ := U.property.exists_basicOpen_le
    (V := (d₁.D : X.Opens) ⊓ (d₂.D : X.Opens) ⊓ g ⁻¹ᵁ V₃)
    ⟨localCenter K f U y, ⟨⟨hx₁, hx₂⟩, hgxV₃⟩⟩ (center_ι_mem K f U y)
  let V' : Y.affineOpens := ⟨V₃, hV₃⟩
  have h₁ : ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ d₁.D :=
    haW.trans (inf_le_left.trans inf_le_left)
  have h₂ : ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ d₂.D :=
    haW.trans (inf_le_left.trans inf_le_right)
  have h₃ : ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ g ⁻¹ᵁ (V' : Y.Opens) :=
    haW.trans inf_le_right
  have hV₁ : (V' : Y.Opens) ≤ d₁.V := fun z hz => (hV₃le hz).1
  have hV₂ : (V' : Y.Opens) ≤ d₂.V := fun z hz => (hV₃le hz).2
  obtain ⟨w₃, hw₃⟩ : y ∈ range (localMap K f (X.affineBasicOpen_le a)) := by
    rw [OpenGluing.range_localMap_basicOpen]
    exact hxa
  have e₁ : localMap K f h₁ w₃ = d₁.w :=
    localMap_injective K f d₁.hDU (by rw [localMap_localMap, d₁.hw]; exact hw₃)
  have e₂ : localMap K f h₂ w₃ = d₂.w :=
    localMap_injective K f d₂.hDU (by rw [localMap_localMap, d₂.hw]; exact hw₃)
  have k₁ : d₁.value g hg = ι K f' V' (morphismLocalMap K f f' g hg h₃ w₃) := by
    rw [LocalDatum.value, ← e₁, morphismLocalMap_localMap, ← ι_localMap K f' hV₁,
      localMap_morphismLocalMap K f f' g hg hV₁ h₃ (h₁.trans d₁.hDV)]
  have k₂ : d₂.value g hg = ι K f' V' (morphismLocalMap K f f' g hg h₃ w₃) := by
    rw [LocalDatum.value, ← e₂, morphismLocalMap_localMap, ← ι_localMap K f' hV₂,
      localMap_morphismLocalMap K f f' g hg hV₂ h₃ (h₂.trans d₂.hDV)]
  rw [k₁, k₂]

variable (K f)

/-- Every point of an affine analytification admits a local datum. -/
theorem nonempty_localDatum (g : X ⟶ Y) (U : X.affineOpens) (y : LocalSpace K f U) :
    Nonempty (LocalDatum K f g U y) := by
  obtain ⟨a, V, h, w, hw⟩ := exists_basicOpen_datum K g U y
  exact ⟨⟨X.affineBasicOpen a, V, X.affineBasicOpen_le a, h, w, hw⟩⟩

variable (f')

/-- The analytification of `g` on the analytification of an affine open `U` of `X`:
the value of any local datum. -/
def localFun (g : X ⟶ Y) (hg : g ≫ f' = f) (U : X.affineOpens) (y : LocalSpace K f U) :
    Space K f' :=
  (Classical.choice (nonempty_localDatum K f g U y)).value g hg

theorem localFun_eq (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens}
    {y : LocalSpace K f U} (d : LocalDatum K f g U y) :
    localFun K f f' g hg U y = d.value g hg :=
  LocalDatum.value_eq g hg _ d

theorem continuous_localFun (g : X ⟶ Y) (hg : g ≫ f' = f) (U : X.affineOpens) :
    Continuous (localFun K f f' g hg U) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨a, V, h, w, rfl⟩ := exists_basicOpen_datum K g U y
  have e : localFun K f f' g hg U ∘ localMap K f (X.affineBasicOpen_le a) =
      ι K f' V ∘ morphismLocalMap K f f' g hg h := by
    funext w'
    exact localFun_eq K f f' g hg
      (⟨X.affineBasicOpen a, V, X.affineBasicOpen_le a, h, w', rfl⟩ :
        LocalDatum K f g U (localMap K f (X.affineBasicOpen_le a) w'))
  rw [← (isOpenEmbedding_localMap_basicOpen K f U a).continuousAt_iff, e]
  exact ((ι K f' V).continuous.comp (morphismLocalMap K f f' g hg h).continuous).continuousAt

theorem localFun_localMap (g : X ⟶ Y) (hg : g ≫ f' = f) {U U' : X.affineOpens}
    (hU : (U' : X.Opens) ≤ U) (y : LocalSpace K f U') :
    localFun K f f' g hg U (localMap K f hU y) = localFun K f f' g hg U' y := by
  let d := Classical.choice (nonempty_localDatum K f g U' y)
  rw [localFun_eq K f f' g hg (U := U)
    ⟨d.D, d.V, d.hDU.trans hU, d.hDV, d.w, by rw [← localMap_localMap K f hU d.hDU, d.hw]⟩]
  exact (localFun_eq K f f' g hg d).symm

/-- The analytification of a morphism `g : X ⟶ Y` over `Spec K`, glued from the local
maps on principal affine opens mapped into affine opens. -/
def analytification (g : X ⟶ Y) (hg : g ≫ f' = f) : C(Space K f, Space K f') :=
  desc K f (fun U => ⟨localFun K f f' g hg U, continuous_localFun K f f' g hg U⟩)
    (fun h y => localFun_localMap K f f' g hg h y)

theorem isAnalytificationMap_analytification (g : X ⟶ Y) (hg : g ≫ f' = f) :
    IsAnalytificationMap K f f' g hg (analytification K f f' g hg) := by
  intro U V h y
  exact localFun_eq K f f' g hg ⟨U, V, le_refl _, h, y, localMap_self K f U y⟩

/-- An analytification of `g` takes at `ι U y` the value of every local datum of `y`. -/
theorem apply_ι_eq_value {g : X ⟶ Y} {hg : g ≫ f' = f} {F : C(Space K f, Space K f')}
    (hF : IsAnalytificationMap K f f' g hg F) {U : X.affineOpens} {y : LocalSpace K f U}
    (d : LocalDatum K f g U y) : F (ι K f U y) = d.value g hg := by
  obtain ⟨D, V, hDU, hDV, w, rfl⟩ := d
  rw [ι_localMap, hF D V hDV w]
  rfl

/-- There is exactly one analytification of `g`. -/
theorem existsUnique_isAnalytificationMap (g : X ⟶ Y) (hg : g ≫ f' = f) :
    ∃! F : C(Space K f, Space K f'), IsAnalytificationMap K f f' g hg F := by
  refine ⟨analytification K f f' g hg, isAnalytificationMap_analytification K f f' g hg, ?_⟩
  intro F hF
  apply desc_unique K f
  intro U y
  let d := Classical.choice (nonempty_localDatum K f g U y)
  exact (apply_ι_eq_value K f f' hF d).trans (localFun_eq K f f' g hg d).symm

/-- The composite of analytifications of `g` and of `g'` is an analytification of
`g ≫ g'`. -/
theorem isAnalytificationMap_comp {Z : Scheme.{u}} (f'' : Z ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f''] (g : X ⟶ Y) (hg : g ≫ f' = f) (g' : Y ⟶ Z)
    (hg' : g' ≫ f'' = f') (F : C(Space K f, Space K f')) (F' : C(Space K f', Space K f''))
    (hF : IsAnalytificationMap K f f' g hg F) (hF' : IsAnalytificationMap K f' f'' g' hg' F') :
    IsAnalytificationMap K f f'' (g ≫ g') (by rw [Category.assoc, hg', hg]) (F'.comp F) := by
  intro U W h y
  have hx : localCenter K f U y ∈ (U : X.Opens) := center_ι_mem K f U y
  have hxW : g (localCenter K f U y) ∈ g' ⁻¹ᵁ (W : Z.Opens) := h hx
  obtain ⟨V, hV, hgxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  obtain ⟨a, haV, hxa⟩ := U.property.exists_basicOpen_le
    (V := g ⁻¹ᵁ V) ⟨localCenter K f U y, hgxV⟩ hx
  obtain ⟨w, rfl⟩ : y ∈ range (localMap K f (X.affineBasicOpen_le a)) := by
    rw [OpenGluing.range_localMap_basicOpen]
    exact hxa
  let V' : Y.affineOpens := ⟨V, hV⟩
  have hVW' : (V' : Y.Opens) ≤ g' ⁻¹ᵁ (W : Z.Opens) := hVW
  have hDV : ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ g ⁻¹ᵁ (V' : Y.Opens) := haV
  rw [ContinuousMap.comp_apply, ι_localMap, hF _ V' hDV, hF' V' W hVW',
    morphismLocalMap_comp K f f' f'' g hg g' hg' hDV hVW' ((show ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ U from
      X.affineBasicOpen_le a).trans h),
    morphismLocalMap_localMap]

end Normed

end MorphismExistence

/-- Berkovich 1990, Theorem 3.4.1 with steps (2)–(3) of its proof, for the Library's
polynomial-locus model: analytifications of morphisms of schemes locally of finite type
over `K` exist, are unique, are compatible with centers and rational points, and
compose. -/
theorem schemeAnalytificationMorphism : SchemeAnalytificationMorphismStatement.{u} := by
  refine ⟨?_, ?_⟩
  · intro K _ _ _ X Y f f' _ _ g hg
    exact ⟨MorphismExistence.existsUnique_isAnalytificationMap K f f' g hg,
      fun F hF => MorphismCompatibility.compatibility K f f' g hg F hF⟩
  · intro K _ _ _ X Y Z f f' f'' _ _ _ g hg g' hg' F F' hF hF'
    exact MorphismExistence.isAnalytificationMap_comp K f f' f'' g hg g' hg' F F' hF hF'

end Langlands.Analytic.SchemeAnalytification
