import Langlands.AlgebraicGeometry.QuasiAffineCoverDescent

/-! # Quasi-affineness descends through arbitrary etale covers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent

/-- Affine-test form of quasi-affine descent through any etale cover of an affine base. -/
theorem isQuasiAffine_of_etaleCover_affine_tests
    {S X : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
    (𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S)
    (h : ∀ (i : 𝒰.I₀) (B : Scheme.{u}) (b : B ⟶ 𝒰.X i)
      [IsAffine B] [IsOpenImmersion b], (pullback f (b ≫ 𝒰.f i)).IsQuasiAffine) :
    X.IsQuasiAffine := by
  let 𝒲 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S := 𝒰.ulift
  have (i : 𝒲.I₀) : Etale (𝒲.f i) := 𝒲.map_prop i
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  have : QuasiCompactCover 𝒲.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun i => (𝒲.f i).isOpenMap
  obtain ⟨𝒱, a, hfin, ha⟩ :
      ∃ (𝒱 : S.AffineCover.{u} @Etale) (a : 𝒱.cover ⟶ 𝒲),
        Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (a.h₀ j) :=
    QuasiCompactCover.exists_hom 𝒲
  have : Finite 𝒱.cover.I₀ := hfin
  have (i : 𝒱.cover.I₀) : IsAffine (𝒱.cover.X i) := by
    infer_instance
  have (i : 𝒱.cover.I₀) : Etale (𝒱.cover.f i) := 𝒱.cover.map_prop i
  have (i : 𝒱.cover.I₀) : Flat (𝒱.cover.f i) := inferInstance
  have (i : 𝒱.cover.I₀) : (pullback f (𝒱.cover.f i)).IsQuasiAffine := by
    have : IsOpenImmersion (a.h₀ i) := ha i
    have hi : (pullback f (a.h₀ i ≫ 𝒲.f (a.s₀ i))).IsQuasiAffine :=
      h (𝒰.idx (a.s₀ i)) (𝒱.cover.X i) (a.h₀ i)
    rwa [a.w₀ i] at hi
  apply QuasiAffineCoverDescent.isQuasiAffine_of_finite_affine_cover f 𝒱.cover.X 𝒱.cover.f
  intro s
  exact 𝒱.cover.exists_eq s

/-- The relative affine-open condition supplies every affine open-immersion test. -/
theorem isQuasiAffine_pullback_affine_open
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ S)
    (h : ∀ V : Y.affineOpens,
      ((pullback.snd f q) ⁻¹ᵁ (V : Y.Opens)).toScheme.IsQuasiAffine)
    (b : B ⟶ Y) [IsAffine B] [IsOpenImmersion b] :
    (pullback f (b ≫ q)).IsQuasiAffine := by
  let V : Y.affineOpens := ⟨b.opensRange, isAffineOpen_opensRange b⟩
  have : ((pullback.snd f q) ⁻¹ᵁ (V : Y.Opens)).toScheme.IsQuasiAffine := h V
  have hb := ((isPullback_morphismRestrict (pullback.snd f q) (V : Y.Opens)).paste_vert
    (IsPullback.of_hasPullback f q).flip).flip
  have : (pullback f (V.1.ι ≫ q)).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom hb.isoPullback.inv
  let e : B ≅ V.1.toScheme := b.isoOpensRange
  let m : pullback f (b ≫ q) ⟶ pullback f (V.1.ι ≫ q) :=
    pullback.map f (b ≫ q) f (V.1.ι ≫ q) (𝟙 X) e.hom (𝟙 S)
      (by simp) (by simp [e, V, ← Category.assoc])
  have : IsIso m := by dsimp [m]; infer_instance
  exact Scheme.IsQuasiAffine.of_isAffineHom m

/-- Quasi-affineness over an affine base can be checked on an arbitrary etale cover. -/
theorem isQuasiAffine_of_etaleCover
    {S X : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
    (𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S)
    (h : ∀ (i : 𝒰.I₀) (V : (𝒰.X i).affineOpens),
      ((pullback.snd f (𝒰.f i)) ⁻¹ᵁ (V : (𝒰.X i).Opens)).toScheme.IsQuasiAffine) :
    X.IsQuasiAffine := by
  apply isQuasiAffine_of_etaleCover_affine_tests f 𝒰
  intro i B b _ _
  exact isQuasiAffine_pullback_affine_open f (𝒰.f i) (h i) b

/-- The all-affine-open condition descends through an arbitrary etale cover. -/
theorem quasiAffineOver_of_etaleCover
    {S X : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S)
    (h : ∀ (i : 𝒰.I₀) (V : (𝒰.X i).affineOpens),
      ((pullback.snd f (𝒰.f i)) ⁻¹ᵁ (V : (𝒰.X i).Opens)).toScheme.IsQuasiAffine) :
    ∀ V : S.affineOpens, (f ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine := by
  intro V
  let fw : (f ⁻¹ᵁ (V : S.Opens)).toScheme ⟶ V.1.toScheme := f ∣_ V.1
  apply isQuasiAffine_of_etaleCover_affine_tests fw (𝒰.pullback₂ V.1.ι)
  intro i B b _ _
  change (pullback fw (b ≫ pullback.snd (𝒰.f i) V.1.ι)).IsQuasiAffine
  let c : B ⟶ 𝒰.X i := b ≫ pullback.fst (𝒰.f i) V.1.ι
  have : IsOpenImmersion c := by dsimp [c]; infer_instance
  have : (pullback f (c ≫ 𝒰.f i)).IsQuasiAffine :=
    isQuasiAffine_pullback_affine_open f (𝒰.f i) (h i) c
  have hb := (IsPullback.of_hasPullback fw
    (b ≫ pullback.snd (𝒰.f i) V.1.ι)).paste_horiz
      (isPullback_morphismRestrict f V.1).flip
  have heq : (b ≫ pullback.snd (𝒰.f i) V.1.ι) ≫ V.1.ι = c ≫ 𝒰.f i := by
    dsimp [c]
    simp only [Category.assoc]
    rw [← pullback.condition]
  rw [heq] at hb
  exact Scheme.IsQuasiAffine.of_isAffineHom hb.isoPullback.hom

/-- Canonical affine-hull open for an affine-base restriction after etale descent. -/
def affineOpenHull
    {S X : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S)
    (h : ∀ (i : 𝒰.I₀) (V : (𝒰.X i).affineOpens),
      ((pullback.snd f (𝒰.f i)) ⁻¹ᵁ (V : (𝒰.X i).Opens)).toScheme.IsQuasiAffine)
    (V : S.affineOpens) : (Spec Γ((f ⁻¹ᵁ (V : S.Opens)).toScheme, ⊤)).Opens := by
  letI := quasiAffineOver_of_etaleCover f 𝒰 h V
  exact (f ⁻¹ᵁ (V : S.Opens)).toScheme.toSpecΓ.opensRange

/-- The canonical open presentation over each affine open of the original base. -/
def affineOpenHullIso
    {S X : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S)
    (h : ∀ (i : 𝒰.I₀) (V : (𝒰.X i).affineOpens),
      ((pullback.snd f (𝒰.f i)) ⁻¹ᵁ (V : (𝒰.X i).Opens)).toScheme.IsQuasiAffine)
    (V : S.affineOpens) :
    (f ⁻¹ᵁ (V : S.Opens)).toScheme ≅ (affineOpenHull f 𝒰 h V).toScheme := by
  letI := quasiAffineOver_of_etaleCover f 𝒰 h V
  exact (f ⁻¹ᵁ (V : S.Opens)).toScheme.toSpecΓ.isoOpensRange

@[reassoc (attr := simp)]
theorem affineOpenHullIso_hom_ι
    {S X : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S)
    (h : ∀ (i : 𝒰.I₀) (V : (𝒰.X i).affineOpens),
      ((pullback.snd f (𝒰.f i)) ⁻¹ᵁ (V : (𝒰.X i).Opens)).toScheme.IsQuasiAffine)
    (V : S.affineOpens) :
    (affineOpenHullIso f 𝒰 h V).hom ≫ (affineOpenHull f 𝒰 h V).ι =
      (f ⁻¹ᵁ (V : S.Opens)).toScheme.toSpecΓ := by
  have := quasiAffineOver_of_etaleCover f 𝒰 h V
  exact (f ⁻¹ᵁ (V : S.Opens)).toScheme.toSpecΓ.isoOpensRange_hom_ι

end Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent
