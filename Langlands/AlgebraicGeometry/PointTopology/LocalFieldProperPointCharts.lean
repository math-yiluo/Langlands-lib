import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Algebra.Field

/-!
# Chart lemmas for limits of actual scheme points

Families of actual relative points, their coordinates on affine charts, and
coordinate germs with values in an arbitrary algebra receiving `I → K`.
-/

noncomputable section

universe u

open CategoryTheory Topology Filter
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A property holding eventually for some value is realized eventually by one family. -/
theorem exists_family_of_eventually {α β : Type*} {l : Filter α} [l.NeBot]
    {P : α → β → Prop} (h : ∀ᶠ i in l, ∃ b, P i b) :
    ∃ F : α → β, ∀ᶠ i in l, P i (F i) := by
  classical
  obtain ⟨i₀, b₀, -⟩ := h.exists
  refine ⟨fun i => if hi : ∃ b, P i b then hi.choose else b₀, h.mono fun i hi => ?_⟩
  simp only [hi, ↓reduceDIte]
  exact hi.choose_spec

section Charts

variable {K : Type u} [Field K] [TopologicalSpace K] {I : Type u}

/-- Coordinatewise convergence on an affine chart gives convergence of actual points. -/
theorem tendsto_schemePoint_of_chart {X : Over (Spec (CommRingCat.of K))}
    (U : X.left.Opens) [IsAffine U] {l : Filter I} (p : I → RingPoint K X K)
    (q : I → RingPoint K (openOver K X U) K)
    (hq : ∀ᶠ i in l, openPointMap K X K U (q i) = p i)
    (x : RingPoint K (openOver K X U) K)
    (hx : ∀ a, Tendsto (fun i => affineSchemePointEquiv K (openOver K X U) K (q i) a) l
      (𝓝 (affineSchemePointEquiv K (openOver K X U) K x a))) :
    @Tendsto I (RingPoint K X K) p l
      (@nhds _ (schemePointTopology K X K) (openPointMap K X K U x)) := by
  let : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
  have hc : Continuous (openPointMap K X K U) :=
    schemePointTopology_continuous_chart K X K ⟨U, ‹IsAffine U›⟩
  have hq' : Tendsto q l (𝓝 x) := by
    rw [(affineSchemePointHomeomorph K (openOver K X U) K).isInducing.tendsto_nhds_iff,
      AlgPoint.isEmbedding_evaluation.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
    exact hx
  exact ((hc.tendsto x).comp hq').congr' hq

variable [IsTopologicalDivisionRing K] [T2Space K]

/-- Convergence to a point of an affine chart is eventually convergence in that chart. -/
theorem exists_chart_family_of_tendsto {Y : Over (Spec (CommRingCat.of K))}
    (V : Y.left.Opens) [IsAffine V] {l : Filter I} (p : I → RingPoint K Y K)
    (y : RingPoint K (openOver K Y V) K)
    (hp : @Tendsto I (RingPoint K Y K) p l
      (@nhds _ (schemePointTopology K Y K) (openPointMap K Y K V y))) :
    ∃ r : I → RingPoint K (openOver K Y V) K,
      (∀ᶠ i in l, openPointMap K Y K V (r i) = p i) ∧
      ∀ b, Tendsto (fun i => affineSchemePointEquiv K (openOver K Y V) K (r i) b) l
        (𝓝 (affineSchemePointEquiv K (openOver K Y V) K y b)) := by
  classical
  let : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
  have he : IsOpenEmbedding (openPointMap K Y K V) :=
    isOpenEmbedding_schemeAffineChart K K Y ⟨V, ‹IsAffine V›⟩
  have hev : ∀ᶠ i in l, p i ∈ Set.range (openPointMap K Y K V) :=
    hp (he.isOpen_range.mem_nhds ⟨y, rfl⟩)
  obtain ⟨r, hr⟩ : ∃ r : I → RingPoint K (openOver K Y V) K,
      ∀ᶠ i in l, openPointMap K Y K V (r i) = p i :=
    ⟨fun i => if h : p i ∈ Set.range (openPointMap K Y K V) then h.choose else y,
      hev.mono fun i hi => by simp only [hi, ↓reduceDIte]; exact hi.choose_spec⟩
  refine ⟨r, hr, fun b => ?_⟩
  have hrt : Tendsto r l (𝓝 y) :=
    he.isInducing.tendsto_nhds_iff.mpr (hp.congr' (hr.mono fun i hi => hi.symm))
  exact (((AlgPoint.continuous_eval b).comp
    (affineSchemePointHomeomorph K (openOver K Y V) K).continuous).tendsto y).comp hrt

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
/-- An ultrafilter of points mapping into an affine open of the target eventually lies in one
affine open of the source over it, by quasi-compactness. -/
theorem exists_affine_eventually_factor {X Y : Over (Spec (CommRingCat.of K))}
    (f : X ⟶ Y) [QuasiCompact f.left] (V : Y.left.Opens) [IsAffine V]
    (𝒰 : Ultrafilter I) (p : I → RingPoint K X K)
    (hp : ∀ᶠ i in 𝒰, ∃ r : RingPoint K (openOver K Y V) K,
      openPointMap K Y K V r = p i ≫ f) :
    ∃ W : X.left.Opens, IsAffineOpen W ∧ W ≤ f.left ⁻¹ᵁ V ∧
      ∀ᶠ i in 𝒰, ∃ q : RingPoint K (openOver K X W) K, openPointMap K X K W q = p i := by
  let c : I → X.left := fun i => (p i).left (IsLocalRing.closedPoint K)
  have hc : ∀ᶠ i in 𝒰, c i ∈ f.left ⁻¹ᵁ V := hp.mono fun i ⟨r, hr⟩ => by
    have h1 : (openPointMap K Y K V r).left (IsLocalRing.closedPoint K) ∈ V :=
      (r.left (IsLocalRing.closedPoint K)).property
    rw [hr] at h1
    exact h1
  have hcomp : IsCompact (f.left ⁻¹ᵁ V : Set X.left) :=
    f.left.isCompact_preimage (show IsAffineOpen V from ‹IsAffine V›).isCompact
  obtain ⟨ξ, hξ, hle⟩ := hcomp.ultrafilter_le_nhds (Ultrafilter.map c 𝒰)
    (le_principal_iff.mpr hc)
  obtain ⟨W, hW, hξW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := ξ)
    (U := f.left ⁻¹ᵁ V) hξ
  refine ⟨W, hW, hWle, ?_⟩
  have hcW : ∀ᶠ i in 𝒰, c i ∈ W := hle (W.isOpen.mem_nhds hξW)
  filter_upwards [hcW] with i hi
  exact ⟨openPointLift K X K W (p i) ((range_subset_open_iff_closedPoint K X K W (p i)).mpr hi),
    openPointMap_lift K X K W (p i) _⟩

end Charts

local instance basicOpenChart_isAffine {K : Type u} [Field K]
    (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left] (g : AffineCoordinateRing K Z) :
    IsAffine (Z.left.basicOpen (U := ⊤) g) :=
  (isAffineOpen_top Z.left).basicOpen g

local instance basicOpenChartAlgebra {K : Type u} [Field K]
    (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left] (g : AffineCoordinateRing K Z) :
    Algebra (AffineCoordinateRing K Z)
      (AffineCoordinateRing K (openOver K Z (Z.left.basicOpen (U := ⊤) g))) :=
  inferInstanceAs (Algebra Γ(Z.left, ⊤) Γ(Z.left.basicOpen (U := ⊤) g, ⊤))

local instance basicOpenChartTower {K : Type u} [Field K]
    (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left] (g : AffineCoordinateRing K Z) :
    IsScalarTower K (AffineCoordinateRing K Z)
      (AffineCoordinateRing K (openOver K Z (Z.left.basicOpen (U := ⊤) g))) :=
  IsScalarTower.of_algebraMap_eq'
    (affineCoordinateMap_natural K (openOverι K Z (Z.left.basicOpen (U := ⊤) g))).symm

local instance basicOpenChartLocalization {K : Type u} [Field K]
    (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left] (g : AffineCoordinateRing K Z) :
    IsLocalization.Away g
      (AffineCoordinateRing K (openOver K Z (Z.left.basicOpen (U := ⊤) g))) :=
  Γ_restrict_isLocalization Z.left (show Γ(Z.left, ⊤) from g)

section BasicOpen

variable {K : Type u} [Field K]
variable (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left]

variable {S : Type u} [CommRing S] [Algebra K S]

/-- Coordinates of a basic-open point are its localization coordinates restricted. -/
theorem basicOpen_coord_openPointMap (g : AffineCoordinateRing K Z)
    (d : RingPoint K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) S) :
    affineSchemePointEquiv K Z S (openPointMap K Z S (Z.left.basicOpen (U := ⊤) g) d) =
      AlgPoint.precomp (Algebra.algHom K (AffineCoordinateRing K Z)
        (AffineCoordinateRing K (openOver K Z (Z.left.basicOpen (U := ⊤) g))))
        (affineSchemePointEquiv K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) S d) := by
  change affineSchemePointEquiv K Z S (d ≫ openOverι K Z (Z.left.basicOpen (U := ⊤) g)) = _
  rw [affineSchemePointEquiv_natural]
  rfl

/-- A point with unit coordinate `g` factors through the basic open of `g`. -/
theorem exists_basicOpen_lift (g : AffineCoordinateRing K Z) (q : RingPoint K Z S)
    (hq : IsUnit (affineSchemePointEquiv K Z S q g)) :
    ∃ d : RingPoint K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) S,
      openPointMap K Z S (Z.left.basicOpen (U := ⊤) g) d = q := by
  have hmem : affineSchemePointEquiv K Z S q ∈ Set.range (AlgPoint.precomp (S := S)
      (Algebra.algHom K (AffineCoordinateRing K Z)
        (AffineCoordinateRing K (openOver K Z (Z.left.basicOpen (U := ⊤) g))))) := by
    rw [AlgPoint.range_precomp_localization (R := K)
      (L := AffineCoordinateRing K (openOver K Z (Z.left.basicOpen (U := ⊤) g)))
      (Submonoid.powers g)]
    exact (AlgPoint.unit_powers_iff g _).mpr hq
  obtain ⟨e, he⟩ := hmem
  refine ⟨(affineSchemePointEquiv K _ S).symm e, ?_⟩
  apply (affineSchemePointEquiv K Z S).injective
  rw [basicOpen_coord_openPointMap, Equiv.apply_symm_apply, he]

/-- A point of a basic open has unit coordinate at its defining function. -/
theorem isUnit_basicOpen_coord (g : AffineCoordinateRing K Z)
    (d : RingPoint K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) S) :
    IsUnit (affineSchemePointEquiv K Z S (openPointMap K Z S (Z.left.basicOpen (U := ⊤) g) d) g) := by
  rw [basicOpen_coord_openPointMap]
  exact (IsLocalization.Away.algebraMap_isUnit g).map
    (affineSchemePointEquiv K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) S d).toAlgHom

end BasicOpen

section Germs

variable {K : Type u} [Field K] {I : Type u} {L : Type u} [CommRing L] [Algebra K L]
variable (G : (I → K) →ₐ[K] L)

/-- The coordinate germ of a family of points of an affine scheme. -/
def germCoord (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left]
    (q : I → RingPoint K Z K) : AlgPoint K (AffineCoordinateRing K Z) L :=
  AlgPoint.ofAlgHom (G.comp (AlgHom.pi fun i => (affineSchemePointEquiv K Z K (q i)).toAlgHom))

@[simp] theorem germCoord_apply (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left]
    (q : I → RingPoint K Z K) (a : AffineCoordinateRing K Z) :
    germCoord G Z q a = G (fun i => affineSchemePointEquiv K Z K (q i) a) := rfl

theorem germCoord_congr {l : Filter I} (hG : ∀ f g : I → K, f =ᶠ[l] g → G f = G g)
    {Z : Over (Spec (CommRingCat.of K))} [IsAffine Z.left] {q q' : I → RingPoint K Z K}
    (h : ∀ᶠ i in l, q i = q' i) : germCoord G Z q = germCoord G Z q' := by
  ext a
  simp only [germCoord_apply]
  exact hG _ _ (h.mono fun i hi => by simp only [hi])

theorem germCoord_comp {Z Z' : Over (Spec (CommRingCat.of K))} [IsAffine Z.left]
    [IsAffine Z'.left] (F : Z ⟶ Z') (q : I → RingPoint K Z K) :
    AlgPoint.precomp (affineCoordinatePullback K F) (germCoord G Z q) =
      germCoord G Z' (fun i => q i ≫ F) := by
  ext a
  change G _ = G _
  congr 1
  funext i
  show affineSchemePointEquiv K Z K (q i) (affineCoordinatePullback K F a) =
    affineSchemePointEquiv K Z' K (q i ≫ F) a
  rw [affineSchemePointEquiv_natural]
  rfl

end Germs

section Transfer

variable {K : Type u} [Field K] {I : Type u} {L : Type u} [Field L] [Algebra K L]
variable (G : (I → K) →ₐ[K] L)

/-- On a basic open, coordinate germs are determined by those on the ambient affine scheme. -/
theorem germCoord_basicOpen (𝒰 : Ultrafilter I)
    (hG : ∀ f g : I → K, f =ᶠ[(𝒰 : Filter I)] g → G f = G g)
    (Z : Over (Spec (CommRingCat.of K))) [IsAffine Z.left] (g : AffineCoordinateRing K Z)
    (q : I → RingPoint K Z K) (z : RingPoint K Z L)
    (hz : affineSchemePointEquiv K Z L z = germCoord G Z q)
    (zD : RingPoint K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) L)
    (hzD : openPointMap K Z L (Z.left.basicOpen (U := ⊤) g) zD = z)
    (d : I → RingPoint K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) K)
    (hd : ∀ᶠ i in 𝒰, openPointMap K Z K (Z.left.basicOpen (U := ⊤) g) (d i) = q i) :
    affineSchemePointEquiv K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) L zD =
      germCoord G (openOver K Z (Z.left.basicOpen (U := ⊤) g)) d := by
  refine IsLocalization.algHom_ext (R := K) (Submonoid.powers g)
    (f := (affineSchemePointEquiv K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) L zD).toAlgHom)
    (g := (germCoord G (openOver K Z (Z.left.basicOpen (U := ⊤) g)) d).toAlgHom) ?_
  apply AlgHom.ext
  intro a
  have e1 : (affineSchemePointEquiv K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) L zD).toAlgHom
      (Algebra.algHom K _ _ a) = affineSchemePointEquiv K Z L z a := by
    rw [← hzD, basicOpen_coord_openPointMap]
    rfl
  have e2 : ∀ i, affineSchemePointEquiv K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) K (d i)
      (Algebra.algHom K _ _ a) =
      affineSchemePointEquiv K Z K (openPointMap K Z K (Z.left.basicOpen (U := ⊤) g) (d i)) a := by
    intro i
    rw [basicOpen_coord_openPointMap]
    rfl
  rw [AlgHom.comp_apply, AlgHom.comp_apply, e1, hz, germCoord_apply]
  change _ = G (fun i => affineSchemePointEquiv K (openOver K Z (Z.left.basicOpen (U := ⊤) g)) K
    (d i) (Algebra.algHom K _ _ a))
  exact hG _ _ (hd.mono fun i hi => by simp only [e2, hi])

/-- Transfer of coordinate germs between two affine opens containing the same point:
if a field-valued point of `W` has the coordinate germ of a family, and the same point
lies in `U`, then the family eventually lies in `U` with the same coordinate germ there. -/
theorem germ_transfer {X : Over (Spec (CommRingCat.of K))} (𝒰 : Ultrafilter I)
    (hG : ∀ f g : I → K, f =ᶠ[(𝒰 : Filter I)] g → G f = G g)
    (W U : X.left.Opens) [IsAffine W] [IsAffine U] (p : I → RingPoint K X K)
    (qW : I → RingPoint K (openOver K X W) K)
    (hqW : ∀ᶠ i in 𝒰, openPointMap K X K W (qW i) = p i)
    (zW : RingPoint K (openOver K X W) L)
    (hzW : affineSchemePointEquiv K (openOver K X W) L zW = germCoord G (openOver K X W) qW)
    (zU : RingPoint K (openOver K X U) L)
    (hz : openPointMap K X L W zW = openPointMap K X L U zU) :
    ∃ qU : I → RingPoint K (openOver K X U) K,
      (∀ᶠ i in 𝒰, openPointMap K X K U (qU i) = p i) ∧
      affineSchemePointEquiv K (openOver K X U) L zU = germCoord G (openOver K X U) qU := by
  have hx₀ : zW.left (IsLocalRing.closedPoint L) ∈ (openOverι K X W).left ⁻¹ᵁ U := by
    have h1 : (openPointMap K X L U zU).left (IsLocalRing.closedPoint L) ∈ U :=
      (zU.left (IsLocalRing.closedPoint L)).property
    rw [← hz] at h1
    exact h1
  obtain ⟨g, hgle, hxg⟩ := (isAffineOpen_top (openOver K X W).left).exists_basicOpen_le
    (V := (openOverι K X W).left ⁻¹ᵁ U) ⟨_, hx₀⟩ trivial
  let g' : AffineCoordinateRing K (openOver K X W) := g
  let D : (openOver K X W).left.Opens := (openOver K X W).left.basicOpen (U := ⊤) g'
  have hrD : Set.range zW.left ⊆ D :=
    (range_subset_open_iff_closedPoint K (openOver K X W) L D zW).mpr hxg
  let zD := openPointLift K (openOver K X W) L D zW hrD
  have hzD : openPointMap K (openOver K X W) L D zD = zW :=
    openPointMap_lift K (openOver K X W) L D zW hrD
  let jW := openOverι K (openOver K X W) D
  have hjrange : Set.range (jW ≫ openOverι K X W).left ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hgle t.property
  let jU := relativeOpenLift K (jW ≫ openOverι K X W) U hjrange
  have hjU : jU ≫ openOverι K X U = jW ≫ openOverι K X W :=
    relativeOpenLift_fac K _ U hjrange
  have hunit : IsUnit (affineSchemePointEquiv K (openOver K X W) L zW g') := by
    rw [← hzD]
    exact isUnit_basicOpen_coord (openOver K X W) g' zD
  rw [hzW, germCoord_apply] at hunit
  have hne : ∀ᶠ i in 𝒰, affineSchemePointEquiv K (openOver K X W) K (qW i) g' ≠ 0 := by
    by_contra hcon
    rw [← Ultrafilter.eventually_not] at hcon
    have h0 : (fun i => affineSchemePointEquiv K (openOver K X W) K (qW i) g') =ᶠ[(𝒰 : Filter I)]
        (0 : I → K) := hcon.mono fun i hi => by simpa using hi
    exact hunit.ne_zero (by rw [hG _ _ h0, map_zero])
  have hlift : ∀ᶠ i in 𝒰, ∃ d : RingPoint K (openOver K (openOver K X W) D) K,
      openPointMap K (openOver K X W) K D d = qW i :=
    hne.mono fun i hi => exists_basicOpen_lift (openOver K X W) g' (qW i) (Ne.isUnit hi)
  obtain ⟨d, hd⟩ := exists_family_of_eventually hlift
  refine ⟨fun i => d i ≫ jU, ?_, ?_⟩
  · filter_upwards [hd, hqW] with i hdi hqi
    have e : openPointMap K X K U (d i ≫ jU) =
        openPointMap K X K W (openPointMap K (openOver K X W) K D (d i)) := by
      change (d i ≫ jU) ≫ openOverι K X U = (d i ≫ jW) ≫ openOverι K X W
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun t => d i ≫ t) hjU).trans (Category.assoc _ _ _).symm)
    refine e.trans ?_
    rw [hdi, hqi]
  · have hzU : zD ≫ jU = zU := by
      apply openPointMap_injective K X L U
      have e : openPointMap K X L U (zD ≫ jU) =
          openPointMap K X L W (openPointMap K (openOver K X W) L D zD) := by
        change (zD ≫ jU) ≫ openOverι K X U = (zD ≫ jW) ≫ openOverι K X W
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun t => zD ≫ t) hjU).trans (Category.assoc _ _ _).symm)
      rw [e, hzD, hz]
    have hcoordD := germCoord_basicOpen G 𝒰 hG (openOver K X W) g' qW zW hzW zD hzD d hd
    rw [← hzU]
    change affineSchemePointEquiv K (openOver K X U) L (zD ≫ jU) = _
    rw [affineSchemePointEquiv_natural, hcoordD, germCoord_comp]

end Transfer

end Langlands.AlgebraicGeometry.PointTopology
