import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointCharts
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Limits of actual points through the valuative criterion

An abstract limit theorem for actual relative points: a field `L` receiving the
coordinate families through `G`, with a valuation subring `O` of convergent germs and a
residue map `ρ : O → K`, lets the existence part of the valuative criterion produce limits.
-/

noncomputable section

universe u

open CategoryTheory Topology Filter
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]

/-- If a family of actual points has images converging to `y`, and coordinate germs can be
evaluated in a field with a valuation subring of convergent germs, then the family converges
to an actual point over `y`, for every universally closed quasi-compact relative morphism. -/
theorem exists_limit_of_valuationSubring
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y)
    [QuasiCompact f.left] [UniversallyClosed f.left]
    {I : Type u} (𝒰 : Ultrafilter I) (p : I → RingPoint K X K) (y : RingPoint K Y K)
    (hy : @Tendsto I (RingPoint K Y K) (fun i => p i ≫ f) 𝒰
      (@nhds _ (schemePointTopology K Y K) y))
    {L : Type u} [Field L] [Algebra K L] (G : (I → K) →ₐ[K] L)
    (hG : ∀ g₁ g₂ : I → K, g₁ =ᶠ[(𝒰 : Filter I)] g₂ → G g₁ = G g₂)
    (O : ValuationSubring L) [Algebra K O] [IsScalarTower K O L] (ρ : O →ₐ[K] K)
    (hO : ∀ (g : I → K) (c : K), Tendsto g 𝒰 (𝓝 c) → G g ∈ O)
    (hρ : ∀ (a : O) (g : I → K), (a : L) = G g → Tendsto g 𝒰 (𝓝 (ρ a))) :
    ∃ x : RingPoint K X K, x ≫ f = y ∧
      @Tendsto I (RingPoint K X K) p 𝒰 (@nhds _ (schemePointTopology K X K) x) := by
  classical
  -- An affine chart `V` of the target at `y`, and the chart coordinates of the images.
  obtain ⟨V, yV, hyV⟩ := exists_affineOpenPoint K Y K y
  have : IsAffine V.val := V.property
  subst hyV
  obtain ⟨r, hr, hrconv⟩ := exists_chart_family_of_tendsto V.val (fun i => p i ≫ f) yV hy
  -- An affine open `W` of the source over `V` containing almost all points.
  obtain ⟨W, hW, hWV, hWev⟩ := exists_affine_eventually_factor f V.val 𝒰 p
    (hr.mono fun i hi => ⟨r i, hi⟩)
  have : IsAffine W := hW
  obtain ⟨qW, hqW⟩ := exists_family_of_eventually hWev
  -- The `L`-point of `W` and the `O`-point of `V` given by coordinate germs.
  let zW : RingPoint K (openOver K X W) L :=
    (affineSchemePointEquiv K (openOver K X W) L).symm (germCoord G (openOver K X W) qW)
  have hzW : affineSchemePointEquiv K (openOver K X W) L zW = germCoord G (openOver K X W) qW :=
    Equiv.apply_symm_apply _ _
  have hmem : ∀ b, germCoord G (openOver K Y V.val) r b ∈ O := fun b => hO _ _ (hrconv b)
  let H : AffineCoordinateRing K (openOver K Y V.val) →ₐ[K] O :=
    { RingHom.codRestrict (germCoord G (openOver K Y V.val) r).toAlgHom.toRingHom O hmem with
      commutes' := fun c => Subtype.ext <| by
        change (germCoord G (openOver K Y V.val) r).toAlgHom (algebraMap K _ c) =
          ((algebraMap K O c : O) : L)
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K O L c]
        rfl }
  let wV : RingPoint K (openOver K Y V.val) O :=
    (affineSchemePointEquiv K (openOver K Y V.val) O).symm (AlgPoint.ofAlgHom H)
  have hwV : affineSchemePointEquiv K (openOver K Y V.val) O wV = AlgPoint.ofAlgHom H :=
    Equiv.apply_symm_apply _ _
  let ι : O →ₐ[K] L := IsScalarTower.toAlgHom K O L
  -- The restriction of `f` to `W → V`.
  have hFr : Set.range (openOverι K X W ≫ f).left ⊆ V.val := by
    rintro _ ⟨t, rfl⟩
    exact hWV t.property
  let F := relativeOpenLift K (openOverι K X W ≫ f) V.val hFr
  have hF : F ≫ openOverι K Y V.val = openOverι K X W ≫ f := relativeOpenLift_fac K _ _ hFr
  -- The two `L`-points of `V` agree.
  have hsq : (zW ≫ F : RingPoint K (openOver K Y V.val) L) = wV.changeRing ι := by
    apply (affineSchemePointEquiv K (openOver K Y V.val) L).injective
    rw [affineSchemePointEquiv_natural, affineSchemePointEquiv_changeRing, hzW, hwV,
      germCoord_comp]
    have hcongr : germCoord G (openOver K Y V.val) (fun i => qW i ≫ F) =
        germCoord G (openOver K Y V.val) r := by
      apply germCoord_congr G hG
      filter_upwards [hqW, hr] with i hqi hri
      apply openPointMap_injective K Y K V.val
      rw [hri, ← hqi]
      change (qW i ≫ F) ≫ openOverι K Y V.val = (qW i ≫ openOverι K X W) ≫ f
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun t => qW i ≫ t) hF).trans (Category.assoc _ _ _).symm)
    rw [hcongr]
    ext b
    rfl
  -- The valuative square.
  let z : RingPoint K X L := openPointMap K X L W zW
  let w : RingPoint K Y O := openPointMap K Y O V.val wV
  have hzw : (z ≫ f : RingPoint K Y L) = w.changeRing ι := by
    change (zW ≫ openOverι K X W) ≫ f = ringTestMap K ι ≫ (wV ≫ openOverι K Y V.val)
    refine ((Category.assoc _ _ _).trans ((congrArg (fun t => zW ≫ t) hF.symm).trans
      (Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg (fun t => t ≫ openOverι K Y V.val) hsq).trans ?_
    exact Category.assoc _ _ _
  have hcomm : z.left ≫ f.left = Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫ w.left :=
    congrArg (fun t : RingPoint K Y L => t.left) hzw
  have hVC : ValuativeCriterion.Existence f.left := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f.left := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let S : ValuativeCommSq f.left :=
    { R := O, K := L, i₁ := z.left, i₂ := w.left, commSq := ⟨hcomm⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hVC S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫ l = z.left := hl₁
  have hl₂' : l ≫ f.left = w.left := hl₂
  -- The `O`-point of `X` and its reduction.
  let lA : RingPoint K X O := Over.homMk l (by
    change l ≫ X.hom = (ringTest K O).hom
    rw [← Over.w f, ← Category.assoc, hl₂']
    exact Over.w w)
  have hlAf : (lA ≫ f : RingPoint K Y O) = w := Over.OverMorphism.ext hl₂'
  have hlAι : lA.changeRing ι = z := Over.OverMorphism.ext hl₁'
  have hwy : wV.changeRing ρ = yV := by
    apply (affineSchemePointEquiv K (openOver K Y V.val) K).injective
    rw [affineSchemePointEquiv_changeRing, hwV]
    ext b
    change ρ (H b) = affineSchemePointEquiv K (openOver K Y V.val) K yV b
    exact tendsto_nhds_unique (hρ (H b) _ rfl) (hrconv b)
  refine ⟨lA.changeRing ρ, ?_, ?_⟩
  · rw [← hwy]
    change (ringTestMap K ρ ≫ lA) ≫ f = (ringTestMap K ρ ≫ wV) ≫ openOverι K Y V.val
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => ringTestMap K ρ ≫ t) hlAf).trans (Category.assoc _ _ _).symm)
  · obtain ⟨U, lU, hlU⟩ := exists_affineOpenPoint K X O lA
    have : IsAffine U.val := U.property
    have hz : openPointMap K X L W zW = openPointMap K X L U.val (lU.changeRing ι) := by
      change z = (ringTestMap K ι ≫ lU) ≫ openOverι K X U.val
      rw [← hlAι, ← hlU]
      exact (Category.assoc _ _ _).symm
    obtain ⟨qU, hqU, hzU⟩ := germ_transfer G 𝒰 hG W U.val p qW hqW zW hzW _ hz
    have hlim := tendsto_schemePoint_of_chart U.val p qU hqU (lU.changeRing ρ) (fun a => by
      rw [affineSchemePointEquiv_changeRing]
      have h1 := congrArg (fun φ => φ a) hzU
      rw [affineSchemePointEquiv_changeRing] at h1
      exact hρ _ _ h1)
    have hx : openPointMap K X K U.val (lU.changeRing ρ) = lA.changeRing ρ := by
      rw [← hlU]
      exact Category.assoc _ _ _
    rw [hx] at hlim
    exact hlim

end Langlands.AlgebraicGeometry.PointTopology
