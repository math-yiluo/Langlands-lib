import Langlands.BruhatTits.Unipotent.CompactOpenContainmentStatement
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Langlands.GroupScheme.Dynamic.AffineChart
import Langlands.LocalField.NonzeroParameter

/-! # Compact-open containment in actual dynamic unipotent radicals: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.AffineLine Langlands.GroupScheme.Dynamic
open Langlands.GroupScheme.Dynamic.AffineChart

namespace Langlands.BruhatTits

namespace DynamicUnipotentContainment

section Coordinates

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

omit [TopologicalSpace F] in
/-- The classifying ring map of a rational point is its evaluation in the published
point topology. -/
theorem pointRing_apply (x : RationalPoint F G.X) (b : Γ(G.X.left, ⊤)) :
    pointRing x b = affineSchemePointEquiv F G.X F (rationalPointEquiv F G.X x) b := by
  have h : (𝟙 (ringTest F F) ≫ rationalPointEquiv F G.X x ≫
      (affineSchemeOverIso F G.X).hom).left = x.left ≫ G.X.left.isoSpec.hom := by
    rw [Category.id_comp]
    change (rationalPointEquiv F G.X x).left ≫ G.X.left.isoSpec.hom = _
    rw [rationalPointEquiv_left]
    rfl
  change _ = (Spec.preimage (𝟙 (ringTest F F) ≫ rationalPointEquiv F G.X x ≫
      (affineSchemeOverIso F G.X).hom).left).hom b
  rw [h]
  rfl

theorem continuous_pointRing_apply (b : Γ(G.X.left, ⊤)) :
    Continuous fun x : RationalPoint F G.X => pointRing x b := by
  have h : (fun x : RationalPoint F G.X => pointRing x b) =
      fun x => affineSchemePointHomeomorph F G.X F (rationalPointHomeomorph F G.X x) b :=
    funext fun x => pointRing_apply x b
  rw [h]
  exact (AlgPoint.continuous_eval _).comp
    ((affineSchemePointHomeomorph F G.X F).continuous.comp
      (rationalPointHomeomorph F G.X).continuous)

/-- A map into the rational points is continuous exactly when all its coordinates are. -/
theorem continuous_iff_pointRing {T : Type*} [TopologicalSpace T]
    (g : T → RationalPoint F G.X) :
    Continuous g ↔ ∀ b : Γ(G.X.left, ⊤), Continuous fun t => pointRing (g t) b := by
  let e := (rationalPointHomeomorph F G.X).trans (affineSchemePointHomeomorph F G.X F)
  rw [← e.comp_continuous_iff, AlgPoint.continuous_iff]
  refine forall_congr' fun b => ?_
  have h : (fun t => pointRing (g t) b) = fun t => (e ∘ g) t b :=
    funext fun t => pointRing_apply (g t) b
  rw [h]

end Coordinates

section Points

variable {F : Type u} [Field F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))}
  (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The rational points of `U_G(χ)`. -/
abbrev unipotentPoints : Subgroup (RationalPoint F G.X) :=
  (unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

theorem mem_unipotentPoints_iff [IsAffine G.X.left] (x : RationalPoint F G.X) :
    x ∈ unipotentPoints χ ↔
      (∀ b, ∀ n < 0, pointRing x ((coaction χ b).coeff n) = 0) ∧
        ∀ b, pointRing x ((coaction χ b).coeff 0) = counit G b := by
  rw [mem_unipotent_iff, Spec.preimage_id]
  rfl

end Points

section Closed

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

/-- The rational points of `U_G(χ)` form a closed subset. -/
theorem isClosed_unipotentPoints [T2Space F] : IsClosed (unipotentPoints χ : Set (RationalPoint F G.X)) := by
  have h : (unipotentPoints χ : Set (RationalPoint F G.X)) =
      {x | (∀ b, ∀ n < 0, pointRing x ((coaction χ b).coeff n) = 0) ∧
        ∀ b, pointRing x ((coaction χ b).coeff 0) = counit G b} :=
    Set.ext fun x => mem_unipotentPoints_iff χ x
  rw [h, Set.ofPred_and]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_eq (continuous_pointRing_apply _) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_eq (continuous_pointRing_apply _) continuous_const

end Closed

section Conjugation

variable {F : Type u} [Field F]

/-- Evaluation `F[T, T⁻¹] ⟶ F` at a unit `t`. -/
abbrev laurentEval (t : Fˣ) :
    CommRingCat.of (LaurentPolynomial (CommRingCat.of F)) ⟶ CommRingCat.of F :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id F) t)

theorem polynomialC_comp_laurentEval (t : Fˣ) :
    polynomialC (CommRingCat.of F) ≫ polynomialToLaurent (CommRingCat.of F) ≫
      laurentEval t = 𝟙 _ := by
  ext a
  simp [LaurentPolynomial.eval₂_C]

/-- The `F`-point `t` of `Spec F[T, T⁻¹]`. -/
def laurentSection (t : Fˣ) :
    Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ laurentScheme (𝟙 (Spec (CommRingCat.of F))) :=
  Over.homMk (Spec.map (laurentEval t)) (by
    change Spec.map (laurentEval t) ≫ Spec.map (polynomialToLaurent _) ≫
      Spec.map (polynomialC _) ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, Category.assoc,
      polynomialC_comp_laurentEval, Spec.map_id])

/-- The `F`-point `(1, t)` of `Spec F ×_{Spec F} 𝔾_m`. -/
def unitPoint (t : Fˣ) : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶
    Over.mk (𝟙 (Spec (CommRingCat.of F))) ⊗ (Langlands.GroupScheme.Gm _).X :=
  laurentSection t ≫ laurentPoint (𝟙 _)

/-- Morphisms to the terminal object `Over.mk (𝟙 S)` are unique. -/
theorem hom_overMkId_ext {S : Scheme.{u}} {T : Over S} (a b : T ⟶ Over.mk (𝟙 S)) : a = b :=
  Over.OverMorphism.ext (by simpa using (Over.w a).trans (Over.w b).symm)

variable {G : Langlands.GroupScheme (Spec (CommRingCat.of F))}
  (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The rational point `χ(t)` of `G`. -/
def cocharPoint (t : Fˣ) : RationalPoint F G.X :=
  unitPoint t ≫ snd _ _ ≫ χ.hom.hom

/-- The orbit map at the point `t` is conjugation by `χ(t)`. -/
theorem unitPoint_comp_orbit (t : Fˣ) (x : RationalPoint F G.X) :
    unitPoint t ≫ orbit χ x = cocharPoint χ t * x * (cocharPoint χ t)⁻¹ := by
  have h : unitPoint t ≫ fst _ _ = 𝟙 _ := hom_overMkId_ext _ _
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, reassoc_of% h, cocharPoint]

variable [IsAffine G.X.left]

/-- The coordinates of `χ(t) x χ(t)⁻¹` are given by the coaction evaluated at `t`. -/
theorem pointRing_conj (t : Fˣ) (x : RationalPoint F G.X) :
    pointRing (cocharPoint χ t * x * (cocharPoint χ t)⁻¹) =
      coaction χ ≫ laurentCoeffMap (pointRing x) ≫ laurentEval t := by
  rw [← unitPoint_comp_orbit, unitPoint, Category.assoc, pointRing_comp,
    pointRing_laurentPoint_comp_orbit]
  change _ ≫ Spec.preimage (Spec.map (laurentEval t)) = _
  rw [Spec.preimage_map, Category.assoc]

/-- A bound for the degrees of the coaction value of `b`. -/
def degBound (b : Γ(G.X.left, ⊤)) : ℕ :=
  (coaction χ b).coeff.support.sup Int.toNat

theorem coeff_eq_zero_of_degBound_lt (b : Γ(G.X.left, ⊤)) {N : ℕ} (hN : degBound χ b < N) :
    (coaction χ b).coeff (N : ℤ) = 0 := by
  by_contra h
  have hle := Finset.le_sup (f := Int.toNat) (Finsupp.mem_support_iff.mpr h)
  simp only [Int.toNat_natCast] at hle
  exact absurd hle (not_le.mpr hN)

/-- The polynomial coordinate `∑_{i ≤ M_b} x((c b)ᵢ) tⁱ` of the contraction. -/
def conjCoord (b : Γ(G.X.left, ⊤)) (t : F) (x : RationalPoint F G.X) : F :=
  ∑ i ∈ Finset.range (degBound χ b + 1), pointRing x ((coaction χ b).coeff (i : ℤ)) * t ^ i

theorem pointRing_conj_apply_of_mem (t : Fˣ) {x : RationalPoint F G.X}
    (hx : x ∈ unipotentPoints χ) (b : Γ(G.X.left, ⊤)) :
    pointRing (cocharPoint χ t * x * (cocharPoint χ t)⁻¹) b = conjCoord χ b t x := by
  have hneg := ((mem_unipotent_iff χ x).1 hx).1
  have hq : ∀ n < 0, (laurentCoeffMap (pointRing x) (coaction χ b)).coeff n = 0 :=
    fun n hn => by rw [GroupScheme.Corepresented.coeff_laurentCoeffMap]; exact hneg b n hn
  have hdeg : (LaurentPolynomial.trunc (laurentCoeffMap (pointRing x) (coaction χ b))).natDegree <
      degBound χ b + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_)
    rw [coeff_trunc, GroupScheme.Corepresented.coeff_laurentCoeffMap, coeff_eq_zero_of_degBound_lt χ b hN,
      map_zero]
  rw [pointRing_conj]
  change LaurentPolynomial.eval₂ (RingHom.id F) t
    (laurentCoeffMap (pointRing x) (coaction χ b)) = _
  rw [← toLaurent_trunc hq, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
    Polynomial.eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_trunc, GroupScheme.Corepresented.coeff_laurentCoeffMap]

theorem conjCoord_zero_of_mem {x : RationalPoint F G.X} (hx : x ∈ unipotentPoints χ)
    (b : Γ(G.X.left, ⊤)) : conjCoord χ b 0 x = counit G b := by
  have h0 := ((mem_unipotentPoints_iff χ x).1 hx).2 b
  unfold conjCoord
  rw [Finset.sum_eq_single 0]
  · simpa using h0
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    simp at h

end Conjugation

section Contraction

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

theorem continuous_conjCoord (b : Γ(G.X.left, ⊤)) :
    Continuous fun p : F × RationalPoint F G.X => conjCoord χ b p.1 p.2 := by
  unfold conjCoord
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_pointRing_apply _).comp continuous_snd).mul (continuous_fst.pow i)

open scoped Classical in
/-- The contraction `(t, u) ↦ χ(t) u χ(t)⁻¹` on `U_G(χ)`, extended by `1` at `t = 0`. -/
def contraction (p : F × unipotentPoints χ) : RationalPoint F G.X :=
  if h : p.1 = 0 then 1 else
    cocharPoint χ (Units.mk0 p.1 h) * p.2 * (cocharPoint χ (Units.mk0 p.1 h))⁻¹

omit [TopologicalSpace F] [IsTopologicalRing F] [IsAffine G.X.left] in
theorem contraction_zero (u : unipotentPoints χ) : contraction χ (0, u) = 1 := by
  simp [contraction]

omit [TopologicalSpace F] [IsTopologicalRing F] [IsAffine G.X.left] in
theorem contraction_of_ne_zero {t : F} (ht : t ≠ 0) (u : unipotentPoints χ) :
    contraction χ (t, u) =
      cocharPoint χ (Units.mk0 t ht) * u * (cocharPoint χ (Units.mk0 t ht))⁻¹ := by
  unfold contraction
  split_ifs with h
  · exact absurd h ht
  · rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem pointRing_contraction (p : F × unipotentPoints χ) (b : Γ(G.X.left, ⊤)) :
    pointRing (contraction χ p) b = conjCoord χ b p.1 p.2 := by
  obtain ⟨t, u⟩ := p
  by_cases ht : t = 0
  · subst ht
    rw [contraction_zero, conjCoord_zero_of_mem χ u.2]
    rfl
  · rw [contraction_of_ne_zero χ ht, pointRing_conj_apply_of_mem χ _ u.2]
    rfl

/-- The extended contraction is continuous on `F × U_G(χ)(F)`. -/
theorem continuous_contraction : Continuous (contraction χ) := by
  refine (continuous_iff_pointRing (contraction χ)).2 fun b => ?_
  refine Continuous.congr ((continuous_conjCoord χ b).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) fun p => ?_
  exact (pointRing_contraction χ p b).symm

end Contraction

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

omit [LocallyOfFiniteType G.X.hom] in
/-- A single conjugation `χ(t) · χ(t)⁻¹` moves a compact subset of `U_G(χ)(F)` into a given
open subgroup. -/
theorem exists_conj_mem (K₀ : OpenSubgroup (RationalPoint F G.X))
    (C : Set (unipotentPoints χ)) (hC : IsCompact C) :
    ∃ t : Fˣ, ∀ u ∈ C,
      cocharPoint χ t * (u : RationalPoint F G.X) * (cocharPoint χ t)⁻¹ ∈ K₀ := by
  have := localField_t2Space F
  have hP : ∀ u ∈ C, ∀ᶠ z : F × unipotentPoints χ in 𝓝 ((0 : F), u),
      contraction χ (z.1, z.2) ∈ K₀ := by
    intro u _
    have h1 : (K₀ : Set (RationalPoint F G.X)) ∈ 𝓝 (contraction χ (0, u)) := by
      rw [contraction_zero]
      exact K₀.isOpen.mem_nhds K₀.one_mem
    exact (continuous_contraction χ).continuousAt.preimage_mem_nhds h1
  obtain ⟨t, ht0, htV⟩ :=
    Langlands.LocalField.exists_nonzero_mem_of_mem_nhds_zero F
      (hC.eventually_forall_of_forall_eventually
        (P := fun t v => contraction χ (t, v) ∈ K₀) hP)
  refine ⟨Units.mk0 t ht0, fun u hu => ?_⟩
  have h := htV u hu
  rwa [contraction_of_ne_zero χ ht0] at h

/-- Every compact subset of `U_G(χ)(F)` lies in a compact open subgroup. -/
theorem exists_compactOpenSubgroup (C : Set (unipotentPoints χ)) (hC : IsCompact C) :
    ∃ K : OpenSubgroup (unipotentPoints χ),
      IsCompact (K : Set (unipotentPoints χ)) ∧ C ⊆ (K : Set (unipotentPoints χ)) := by
  have := localField_t2Space F
  have : IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
  obtain ⟨K₀, hK₀⟩ := rationalPoint_exists_compactOpenSubgroup F G
  obtain ⟨t, ht⟩ := exists_conj_mem χ K₀ C hC
  set s := cocharPoint χ t
  let φ : unipotentPoints χ →* RationalPoint F G.X :=
    (MulAut.conj s).toMonoidHom.comp (unipotentPoints χ).subtype
  have hφ : Continuous φ :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  refine ⟨K₀.comap φ hφ, ?_, fun u hu => ht u hu⟩
  rw [Subtype.isCompact_iff]
  have himg : ((↑) : unipotentPoints χ → RationalPoint F G.X) '' (K₀.comap φ hφ : Set _) =
      (fun x => s * x * s⁻¹) ⁻¹' (K₀ : Set (RationalPoint F G.X)) ∩ unipotentPoints χ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.2⟩
    · rintro ⟨hx, hxU⟩
      exact ⟨⟨x, hxU⟩, hx, rfl⟩
  rw [himg]
  refine IsCompact.inter_right ?_ (isClosed_unipotentPoints χ)
  let e : RationalPoint F G.X ≃ₜ RationalPoint F G.X :=
    (Homeomorph.mulLeft s).trans (Homeomorph.mulRight s⁻¹)
  exact e.isCompact_preimage.2 hK₀

end LocalField

end DynamicUnipotentContainment

/-- Every compact subset of the actual dynamic unipotent radical lies in a compact open
subgroup. -/
theorem dynamicUnipotentCompactOpenContainment :
    DynamicUnipotentCompactOpenContainmentStatement.{u} := by
  intro F _ _ _ _ G hG χ
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  intro U C hC
  exact DynamicUnipotentContainment.exists_compactOpenSubgroup χ C hC

end Langlands.BruhatTits
