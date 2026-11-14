import Langlands.AlgebraicGeometry.Picard.ProjectiveGenericExtension
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback
import Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealLocalFreeness
import Langlands.AlgebraicGeometry.AffineGenericScalarUnits

/-! # Line bundles over a valuation ring are determined by their generic fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

namespace CocycleGluing

section Gauge

variable {X : Scheme.{u}} {ι : Type u} {T : ι → X.Opens}

/-- Multiplying a gauge by a family of units that agree on all pairwise overlaps gives a
gauge between the same cocycles. -/
lemma IsGauge.mul_compatible {g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}
    {a c : ∀ i : ι, (Γ(X, T i))ˣ} (ha : IsGauge g h a)
    (hc : ∀ i j : ι,
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (c i : Γ(X, T i)) =
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (c j : Γ(X, T j))) :
    IsGauge g h (fun i ↦ a i * c i) := by
  intro i j
  rw [ha i j]
  have hxy : X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (c i : Γ(X, T i)) *
      X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
        (((c j)⁻¹ : (Γ(X, T j))ˣ) : Γ(X, T j)) = 1 := by
    rw [hc i j, ← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, mul_inv_rev, map_mul]
  linear_combination
    (-(X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i : Γ(X, T i)) *
        (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
          (((a j)⁻¹ : (Γ(X, T j))ˣ) : Γ(X, T j)))) * hxy

end Gauge

section PullbackGauge

variable {X Y : Scheme.{u}} (q : Y ⟶ X) {ι : Type u} {T : ι → X.Opens}

/-- A unit gauge on `X` is detected after pulling back along `q`, provided `q` is injective on
the sections over all pairwise overlaps. -/
lemma isGauge_of_pullback {g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ} {a : ∀ i : ι, (Γ(X, T i))ˣ}
    (hinj : ∀ i j : ι, Function.Injective (q.app (T i ⊓ T j)))
    (ha : IsGauge (pullbackCocycle q g) (pullbackCocycle q h)
      (fun i ↦ Units.map (q.app (T i)).hom.toMonoidHom (a i))) :
    IsGauge g h a := by
  intro i j
  apply hinj i j
  have e := ha i j
  simp only [pullbackCocycle_val, Units.coe_map, Units.coe_map_inv] at e
  rw [Scheme.Hom.app_eq_appLE]
  simp only [map_mul, appLE_res]
  exact e

end PullbackGauge

end CocycleGluing

open CocycleGluing

section Valuation

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (q : Y ⟶ X) (s : Y ⟶ Spec (CommRingCat.of K))
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Smooth p] [GeometricallyConnected p]

include H in
/-- Over a valuation ring, a gauge between the generic pullbacks of two unit cocycles on affine
opens whose pairwise overlaps meet the closed fibre comes from a gauge on the total scheme, provided
the affine section algebras are projective and generic restriction is injective. -/
theorem exists_isGauge_of_generic_isGauge [IsSeparated p] {ι : Type u} (T : ι → X.Opens)
    (hT : ∀ i, IsAffineOpen (T i))
    (hmeet : ∀ i j,
      (p ⁻¹' {IsLocalRing.closedPoint R} ∩ ((T i ⊓ T j : X.Opens) : Set X)).Nonempty)
    (hproj : AffineClosedFibreSectionProjectivity p)
    (hinj : ∀ U : X.Opens, Function.Injective (q.app U))
    {g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}
    (b : ∀ i, (Γ(Y, q ⁻¹ᵁ T i))ˣ)
    (hb : IsGauge (pullbackCocycle q g) (pullbackCocycle q h) b) :
    ∃ a : ∀ i, (Γ(X, T i))ˣ, IsGauge g h a := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun i ↦ isEmptyElim i, fun i ↦ isEmptyElim i⟩
  have hInf : ∀ {U V : X.Opens}, IsAffineOpen U → IsAffineOpen V →
      IsAffineOpen (U ⊓ V) := by
    intro U V hU hV
    exact isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (pullback.diagonal p)) ⊤ (isAffineOpen_top _)
      U (by simp) V (by simp) hU hV
  have hmeet' : ∀ i,
      (p ⁻¹' {IsLocalRing.closedPoint R} ∩ ((T i : X.Opens) : Set X)).Nonempty := by
    intro i
    obtain ⟨x, hx, hxi, -⟩ := hmeet i i
    exact ⟨x, hx, hxi⟩
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨r, d, hr, hd, a₀, hn⟩ : ∃ (r d : R) (hr : r ≠ 0) (hd : d ≠ 0) (a₀ : (Γ(X, T i₀))ˣ),
      b i₀ = affineGenericScalarRatio p K q s H (hT i₀) r d hr hd *
        Units.map (q.app (T i₀)).hom.toMonoidHom a₀ := by
    let := affineSectionAlgebra p (hT i₀)
    let := pullbackSectionAlgebra q (T i₀)
    exact ⟨_, _, _, _, _, affineGenericUnitDecomposition_eq p K q s H (hT i₀) (hmeet' i₀)
      (hproj _ (hT i₀) (hmeet' i₀)) (b i₀)⟩
  let ρ : ∀ i, (Γ(Y, q ⁻¹ᵁ T i))ˣ := fun i ↦
    affineGenericScalarRatio p K q s H (hT i) r d hr hd
  let t : (Γ(Y, q ⁻¹ᵁ T i₀))ˣ := Units.map (q.app (T i₀)).hom.toMonoidHom a₀
  let β : ∀ i, (Γ(Y, q ⁻¹ᵁ T i))ˣ := fun i ↦ b i * (ρ i)⁻¹
  have hρ : ∀ i j,
      Y.presheaf.map (homOfLE (inf_le_left : q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j ≤ q ⁻¹ᵁ T i)).op
          (((ρ i)⁻¹ : (Γ(Y, q ⁻¹ᵁ T i))ˣ) : Γ(Y, q ⁻¹ᵁ T i)) =
        Y.presheaf.map (homOfLE (inf_le_right : q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j ≤ q ⁻¹ᵁ T j)).op
          (((ρ j)⁻¹ : (Γ(Y, q ⁻¹ᵁ T j))ˣ) : Γ(Y, q ⁻¹ᵁ T j)) := by
    intro i j
    have e1 := affineGenericScalarRatio_restrict p K q s H (hT i) (hInf (hT i) (hT j))
      inf_le_left r d hr hd
    have e2 := affineGenericScalarRatio_restrict p K q s H (hT j) (hInf (hT i) (hT j))
      inf_le_right r d hr hd
    have e := congrArg (fun u ↦ ((u⁻¹ : (Γ(Y, q ⁻¹ᵁ (T i ⊓ T j)))ˣ) :
      Γ(Y, q ⁻¹ᵁ (T i ⊓ T j)))) (e1.trans e2.symm)
    simp only [← map_inv, Units.coe_map] at e
    exact e
  have hβ : IsGauge (pullbackCocycle q g) (pullbackCocycle q h) β := hb.mul_compatible hρ
  have hβ₀ : β i₀ = t := by
    change b i₀ * (ρ i₀)⁻¹ = t
    rw [hn, mul_comm, inv_mul_cancel_left]
  let c : ∀ i, (Γ(X, T i₀ ⊓ T i))ˣ := fun i ↦
    (h i₀ i)⁻¹ *
      Units.map (X.presheaf.map (homOfLE (inf_le_left : T i₀ ⊓ T i ≤ T i₀)).op).hom.toMonoidHom
        a₀ * g i₀ i
  have hc : ∀ i, Y.presheaf.map (homOfLE (q.preimage_mono (inf_le_right :
      T i₀ ⊓ T i ≤ T i))).op (β i : Γ(Y, q ⁻¹ᵁ T i)) =
        q.app (T i₀ ⊓ T i) (c i : Γ(X, T i₀ ⊓ T i)) := by
    intro i
    have e : (pullbackCocycle q h i₀ i : Γ(Y, q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i)) =
        Y.presheaf.map (homOfLE (inf_le_left : q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i₀)).op
            (t : Γ(Y, q ⁻¹ᵁ T i₀)) *
          (pullbackCocycle q g i₀ i : Γ(Y, q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i)) *
        Y.presheaf.map (homOfLE (inf_le_right : q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i)).op
          (((β i)⁻¹ : (Γ(Y, q ⁻¹ᵁ T i))ˣ) : Γ(Y, q ⁻¹ᵁ T i)) := by
      rw [← hβ₀]
      exact hβ i₀ i
    have u1 : Y.presheaf.map (homOfLE (inf_le_right :
          q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i)).op (β i : Γ(Y, q ⁻¹ᵁ T i)) *
        Y.presheaf.map (homOfLE (inf_le_right : q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i)).op
          (((β i)⁻¹ : (Γ(Y, q ⁻¹ᵁ T i))ˣ) : Γ(Y, q ⁻¹ᵁ T i)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have u2 : q.appLE (T i₀ ⊓ T i) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) le_rfl
          (h i₀ i : Γ(X, T i₀ ⊓ T i)) *
        q.appLE (T i₀ ⊓ T i) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) le_rfl
          (((h i₀ i)⁻¹ : (Γ(X, T i₀ ⊓ T i))ˣ) : Γ(X, T i₀ ⊓ T i)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have eA : Y.presheaf.map (homOfLE (inf_le_left :
          q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i₀)).op (t : Γ(Y, q ⁻¹ᵁ T i₀)) =
        q.appLE (T i₀) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) inf_le_left (a₀ : Γ(X, T i₀)) :=
      res_app q inf_le_left (a₀ : Γ(X, T i₀))
    have eA' : q.appLE (T i₀ ⊓ T i) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) le_rfl
          ((Units.map (X.presheaf.map (homOfLE (inf_le_left :
            T i₀ ⊓ T i ≤ T i₀)).op).hom.toMonoidHom a₀ : (Γ(X, T i₀ ⊓ T i))ˣ) :
            Γ(X, T i₀ ⊓ T i)) =
        q.appLE (T i₀) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) inf_le_left (a₀ : Γ(X, T i₀)) :=
      appLE_res q inf_le_left le_rfl (a₀ : Γ(X, T i₀))
    rw [eA, pullbackCocycle_val, pullbackCocycle_val] at e
    rw [Scheme.Hom.app_eq_appLE]
    change Y.presheaf.map (homOfLE (inf_le_right :
          q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i)).op (β i : Γ(Y, q ⁻¹ᵁ T i)) =
        q.appLE (T i₀ ⊓ T i) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) le_rfl (c i : Γ(X, T i₀ ⊓ T i))
    simp only [c, Units.val_mul]
    rw [map_mul, map_mul, eA']
    linear_combination
      (-(Y.presheaf.map (homOfLE (inf_le_right :
          q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i)).op (β i : Γ(Y, q ⁻¹ᵁ T i)))) * u2 +
      (q.appLE (T i₀ ⊓ T i) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) le_rfl
          (((h i₀ i)⁻¹ : (Γ(X, T i₀ ⊓ T i))ˣ) : Γ(X, T i₀ ⊓ T i)) *
        Y.presheaf.map (homOfLE (inf_le_right :
          q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i ≤ q ⁻¹ᵁ T i)).op (β i : Γ(Y, q ⁻¹ᵁ T i))) * e +
      (q.appLE (T i₀ ⊓ T i) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) le_rfl
          (((h i₀ i)⁻¹ : (Γ(X, T i₀ ⊓ T i))ˣ) : Γ(X, T i₀ ⊓ T i)) *
        q.appLE (T i₀) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) (inf_le_left)
          (a₀ : Γ(X, T i₀)) *
        q.appLE (T i₀ ⊓ T i) (q ⁻¹ᵁ T i₀ ⊓ q ⁻¹ᵁ T i) le_rfl
          (g i₀ i : Γ(X, T i₀ ⊓ T i))) * u1
  let α : ∀ i, {a : Γ(X, T i)ˣ // q.app (T i) (a : Γ(X, T i)) = (β i : Γ(Y, q ⁻¹ᵁ T i))} :=
    fun i ↦ affineGenericUnitOfRestriction p (hT i) (hInf (hT i₀) (hT i)) inf_le_right K q s H
      (hmeet i₀ i) (hproj _ (hT i) (hmeet' i)) (β i) (c i) (hc i)
  refine ⟨fun i ↦ (α i).1, isGauge_of_pullback q (fun i j ↦ hinj _) ?_⟩
  have hαβ : (fun i ↦ Units.map (q.app (T i)).hom.toMonoidHom (α i).1) = β := by
    funext i
    apply Units.ext
    exact (α i).2
  rw [hαβ]
  exact hβ

include H in
/-- **Generic injectivity for line bundles over a valuation ring.** Let `p : X ⟶ Spec R` be smooth,
universally closed, separated and with geometrically connected fibres over a valuation ring `R`,
with affine closed-fibre section algebras projective, and let `q` be the inclusion of the generic
fibre, injective on sections. Two line bundles on `X` whose generic pullbacks are isomorphic are
isomorphic. -/
theorem nonempty_iso_of_generic_iso [UniversallyClosed p] [IsSeparated p]
    (hproj : AffineClosedFibreSectionProjectivity p)
    (hinj : ∀ U : X.Opens, Function.Injective (q.app U))
    {L M : X.Modules} (hL : IsLocallyFreeRankOne L) (hM : IsLocallyFreeRankOne M)
    (ψ : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback q).obj M) :
    Nonempty (L ≅ M) := by
  have hpt : ∀ x : p.fiber (IsLocalRing.closedPoint R), ∃ U : X.Opens,
      IsAffineOpen U ∧ p.fiberι (IsLocalRing.closedPoint R) x ∈ U ∧
        (∃ e : Γ(L, U), Scheme.Modules.IsFrameOn e U) ∧
        ∃ f : Γ(M, U), Scheme.Modules.IsFrameOn f U := by
    intro x
    obtain ⟨T, hxT, e, he⟩ := OpenImmersionIdeal.exists_isFrameOn_of_isLocallyFreeRankOne hL
      (p.fiberι (IsLocalRing.closedPoint R) x)
    obtain ⟨T', hxT', f, hf⟩ := OpenImmersionIdeal.exists_isFrameOn_of_isLocallyFreeRankOne hM
      (p.fiberι (IsLocalRing.closedPoint R) x)
    obtain ⟨U, hU, hxU, hUT⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show p.fiberι (IsLocalRing.closedPoint R) x ∈ T ⊓ T' from ⟨hxT, hxT'⟩)
    exact ⟨U, hU, hxU, ⟨L.presheaf.map (homOfLE (hUT.trans inf_le_left)).op e,
      (he.map _).mono (hUT.trans inf_le_left)⟩,
      ⟨M.presheaf.map (homOfLE (hUT.trans inf_le_right)).op f,
        (hf.map _).mono (hUT.trans inf_le_right)⟩⟩
  choose T hT hxT hLf hMf using hpt
  choose e he using hLf
  choose f hf using hMf
  have hcover : (⨆ i, T i) = ⊤ := iSup_eq_top_of_closedFibre_neighbourhoods p T hxT
  have hmeet : ∀ i j,
      (p ⁻¹' {IsLocalRing.closedPoint R} ∩ ((T i ⊓ T j : X.Opens) : Set X)).Nonempty := by
    intro i j
    have hT' : ∀ k, closedFibreGenericPoint p ∈ T k := by
      intro k
      apply closedFibreGenericPoint_mem p
      refine ⟨p.fiberι (IsLocalRing.closedPoint R) k, ?_, hxT k⟩
      rw [← p.range_fiberι]
      exact ⟨k, rfl⟩
    exact ⟨closedFibreGenericPoint p, (closedFibreGenericPoint_spec p).mem, hT' i, hT' j⟩
  have hgL := isCocycle_of_isTransition he (isTransition_frameCocycle he)
  have hgM := isCocycle_of_isTransition hf (isTransition_frameCocycle hf)
  let φL := frameIso he (isTransition_frameCocycle he) hcover
  let φM := frameIso hf (isTransition_frameCocycle hf) hcover
  have hgen : Nonempty (glued (pullbackCocycle q (frameCocycle e he)) ≅
      glued (pullbackCocycle q (frameCocycle f hf))) :=
    ⟨(pullbackIso q _ hcover hgL).symm ≪≫ (Scheme.Modules.pullback q).mapIso φL.symm ≪≫ ψ ≪≫
      (Scheme.Modules.pullback q).mapIso φM ≪≫ pullbackIso q _ hcover hgM⟩
  obtain ⟨b, hb⟩ := (nonempty_iso_glued_iff (hgL.pullback q) (hgM.pullback q)).1 hgen
  obtain ⟨a, ha⟩ := exists_isGauge_of_generic_isGauge p K q s H T hT hmeet hproj hinj b hb
  exact ⟨φL ≪≫ gaugeIso a ha ≪≫ φM.symm⟩

end Valuation

end Langlands.AlgebraicGeometry.Picard
