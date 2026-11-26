import Langlands.Automorphic.GroupSchemeActualDifferential
import Langlands.Automorphic.GroupSchemeArchimedeanHarishChandraFiniteness
import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement
import Langlands.Automorphic.GroupSchemeHarishChandraLeviCompact
import Langlands.Automorphic.GroupSchemeHarishChandraLeviRestriction
import Langlands.Automorphic.GroupSchemeLeviCenterRestriction
import Langlands.Global.AdelicHeightMinimumLeviRestriction

/-! # Reduction of parabolic Harish-Chandra finiteness to arithmetic finiteness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints
  RepresentationGrowth CompactIwasawa

section Pullback

variable {F : Type u} [Field F] [NumberField F]
  {G M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine M.X.left]

private theorem map_pair (j : M ⟶ G) (a : InfiniteAdelicGroupPoints F M)
    (b : FiniteAdelicGroupPoints F M) :
    map F M G j (pair F M a b) =
      pair F G (M.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) a)
        (M.affinePointsTarget j (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) b) := by
  have hi (x : AdelicGroupPoints F M) : infinite F G (map F M G j x) =
      M.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F M x) :=
    DFunLike.congr_fun (M.affinePointsTarget_naturality j (CommAlgCat.ofHom
      (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) x
  apply (split F G).injective
  simp only [split_apply, hi, finite_map, infinite_pair, finite_pair]

private theorem map_finite_inclusion (j : M ⟶ G) (b : FiniteAdelicGroupPoints F M) :
    map F M G j (ofFinite F M b) = ofFinite F G
      (M.affinePointsTarget j (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) b) := by
  simp only [ofFinite_eq_pair, map_pair, map_one]

end Pullback

section ModerateGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G M : GroupScheme (Spec (CommRingCat.of F))}

private theorem moderateGrowth_leviPullback (j : M ⟶ G) {N : ℕ}
    {ρ : MatrixRepresentation G (Fin N)} {f : AdelicGroupPoints F G → ℂ}
    (hf : HasModerateGrowthFunction F G ρ f) (a : AdelicGroupPoints F G) :
    HasModerateGrowthFunction F M (ρ.restrict j) (fun m => f (map F M G j m * a)) := by
  obtain ⟨r, _, h⟩ := RepresentationGrowth.HasModerateGrowthFunction.exists_compact_mul_le_height hf
  obtain ⟨C, hC, hbound⟩ := h {a} isCompact_singleton
  have hb (m : AdelicGroupPoints F M) :
      ‖f (map F M G j m * a)‖ ≤ C * adelicHeightAtLeastOne (ρ.restrict j) m ^ r := by
    simpa only [adelicHeightAtLeastOne, adelicHeight, adelicMatrix_restrict] using
      hbound (map F M G j m) a rfl
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hm (x : AdelicGroupPoints F M) : adelicMatrix F M (ρ.restrict j) x = 1 := by
      apply Units.ext
      ext i k
      exact Fin.elim0 i
    let B := max 1 (AdelicMatrixHeight.height F 0 1)
    have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨C * B ^ r, mul_pos hC (Real.rpow_pos_of_pos hB _), 0, fun m => ?_⟩
    simpa only [Real.rpow_zero, mul_one, adelicHeightAtLeastOne, adelicHeight, hm, B] using hb m
  · let D : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hD : 0 < D := pow_pos (Nat.cast_pos.mpr hN) _
    refine ⟨C * D ^ r, mul_pos hC (Real.rpow_pos_of_pos hD _), r, fun m => ?_⟩
    calc
      _ ≤ C * adelicHeightAtLeastOne (ρ.restrict j) m ^ r := hb m
      _ = _ := by
        rw [adelicHeightAtLeastOne_eq hN, adelicHeight_eq_scalar_mul_sourceNorm,
          Real.mul_rpow hD.le (adelicSourceNorm_pos F M (ρ.restrict j) hN m).le, mul_assoc]

end ModerateGrowth

section Parabolic

variable {F : Type u} [Field F] [NumberField F]
  {G Q M V : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} (iV : V ⟶ Q) (l : M ⟶ Q)

private theorem levi_conj_mem_adeles (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (m : AdelicGroupPoints F M) {y : AdelicGroupPoints F G}
    (hy : y ∈ parabolicUnipotentImage F q iV) :
    map F M G (l ≫ q) m * y * (map F M G (l ≫ q) m)⁻¹ ∈ parabolicUnipotentImage F q iV := by
  obtain ⟨v, rfl⟩ := hy
  let A := CommAlgCat.of F (Adeles F)
  let x : AdelicGroupPoints F Q := map F M Q l m
  let u : AdelicGroupPoints F Q := map F V Q iV v
  have h : x * u * x⁻¹ ∈ (SubgroupFunctor.range iV).carrier ((algSpec (CommRingCat.of F)).obj (op A)) :=
    hV.1.isNormal _ x u (Subgroup.mem_top _) ⟨v, rfl⟩
  obtain ⟨v', hv'⟩ := h
  change map F V Q iV v' = x * u * x⁻¹ at hv'
  have he := congrArg (map F Q G q) hv'
  rw [map_mul, map_mul, map_inv] at he
  refine ⟨v', ?_⟩
  change map F V G (iV ≫ q) v' =
    map F M G (l ≫ q) m * map F V G (iV ≫ q) v * (map F M G (l ≫ q) m)⁻¹
  rw [map_comp_apply_of_hom (p := q) iV v',
    map_comp_apply_of_hom (p := q) l m, map_comp_apply_of_hom (p := q) iV v]
  exact he

variable [IsAffine G.X.left] [IsAffine M.X.left] [IsAffine V.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}

local notation "K∞" => K.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G))

private theorem compact_profile_leviRestriction
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (H : Subgroup (InfiniteAdelicGroupPoints F M)) (v : InfiniteAdelicGroupPoints F V)
    (hv : ∀ m ∈ H,
      let u := V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v
      u * M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) m * u⁻¹ ∈ K∞)
    (E : Submodule ℂ (K∞ → ℂ)) (hE : FiniteDimensional ℂ E)
    (b : FiniteAdelicGroupPoints F G) (a : K∞) :
    ∃ E' : Submodule ℂ (H → ℂ), FiniteDimensional ℂ E' ∧
      ∀ f : AdelicGroupPoints F G → ℂ,
        IsLeftInvariantUnder F G (parabolicQuotientSubgroup F q iV l) f →
        (∀ g, (fun k : K∞ => f (g * ofInfinite F G k)) ∈ E) →
        ∀ m, (fun h : H => translatedLeviRestriction (q := q) l
          (ofFinite F G b * ofInfinite F G a) f (m * ofInfinite F M h)) ∈ E' := by
  let N := parabolicUnipotentImage F q iV
  let u := V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v
  let j := map F M G (l ≫ q)
  let jInf := M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F))
  let c (h : H) : K∞ := ⟨u * jInf h.val * u⁻¹, hv h.val h.property⟩
  let pull (h : H) : K∞ := a⁻¹ * c h * a
  let R : (K∞ → ℂ) →ₗ[ℂ] (H → ℂ) := LinearMap.funLeft ℂ ℂ pull
  refine ⟨E.map R, Module.Finite.map _ _, fun f hInv hProfile m => ?_⟩
  let B := ofFinite F G b
  let A := ofInfinite F G a
  refine ⟨_, hProfile (j m * (B * A)), funext fun h => ?_⟩
  change f (j m * (B * A) * ofInfinite F G (pull h)) =
    f (j (m * ofInfinite F M h.val) * (B * A))
  let U := ofInfinite F G u
  have hU : U ∈ N := ⟨ofInfinite F V v, map_ofInfinite (iV ≫ q) v⟩
  let x := j (m * ofInfinite F M h.val)
  let y := j m * ofInfinite F G (c h)
  have hy : y = j m * (U * j (ofInfinite F M h.val) * U⁻¹) := by
    change j m * ofInfinite F G (u * jInf h.val * u⁻¹) = _
    simp only [map_mul, map_inv, j, map_ofInfinite, U, jInf]
  have hxy : y * x⁻¹ ∈ N := by
    have he : y * x⁻¹ = (j m * U * (j m)⁻¹) * (x * U⁻¹ * x⁻¹) := by
      rw [hy]
      simp only [x, map_mul]
      group
    rw [he]
    exact N.mul_mem (levi_conj_mem_adeles iV l hV m hU)
      (levi_conj_mem_adeles iV l hV _ (N.inv_mem hU))
  have he : j m * (B * A) * ofInfinite F G (pull h) = y * (B * A) := by
    change j m * (B * A) * ofInfinite F G (a.val⁻¹ * (c h).val * a.val) = _
    rw [map_mul, map_mul, map_inv]
    change j m * (B * A) * (A⁻¹ * ofInfinite F G (c h) * A) = _
    calc
      _ = j m * (B * ofInfinite F G (c h)) * A := by group
      _ = j m * (ofInfinite F G (c h) * B) * A := by
        rw [(factors_commute F G (c h).val b).eq]
      _ = y * (B * A) := by simp only [y, mul_assoc]
  rw [he]
  change f (y * (B * A)) = f (x * (B * A))
  rw [show y * (B * A) = (y * x⁻¹) * (x * (B * A)) by group]
  exact hInv _ (Subgroup.mem_sup_left hxy) _

end Parabolic

/-- Arithmetic Harish-Chandra finiteness and finite transfer of enveloping centers imply
the parabolic finiteness statement. -/
def ParabolicHarishChandraFinitenessReductionStatement : Prop :=
  ArithmeticHarishChandraFinitenessStatement.{u} →
    ParabolicLeviCenterRestrictionStatement.{u} →
      ParabolicHarishChandraFinitenessStatement.{u}

set_option maxHeartbeats 1000000 in
theorem parabolicHarishChandraFiniteness_of_arithmetic_and_center :
    ParabolicHarishChandraFinitenessReductionStatement.{u} := by
  classical
  intro hArch hCenter
  have hRational := rationalHarishChandraFiniteness_of_arithmetic hArch
  intro F _ _ G Q M V _ _ _ _ q _ iV l hG hq hV hl hmul K hKmax hK N d ρ hsmooth hcalc hρ
    J hJ L hL E hE
  let : IsIso (subgroupMultiplication l iV) := hmul
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : IsClosedImmersion iV.hom.hom.left := hV.1.isClosedSubgroup
  let : IsAffine V.X.left := isAffine_of_isAffineHom iV.hom.hom.left
  let hsM := hl.isConnectedReductive.smoothDimension_spec
  let hcM := adelicDifferentialCommutator_of_smooth F M hsM
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  obtain ⟨H, hH, v, hv⟩ := exists_leviCompact_conj_by_radical q iV l hG hq hl Kinf
    hKmax.isMaximalCompact_comap_ofInfinite
  let L₀ : OpenSubgroup (FiniteAdelicGroupPoints F G) := ⟨L, hL⟩
  let A : Set (AdelicGroupPoints F G → ℂ) := {f |
    IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l) Kinf ρ f ∧
    (∀ b ∈ L, ∀ g, f (g * ofFinite F G b) = f g) ∧
    (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
      ∀ hf : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G f b, hf⟩ = 0) ∧
    ∀ g, (fun k : Kinf => f (g * ofInfinite F G k)) ∈ E}
  let : FiniteDimensional ℂ E := hE
  refine finiteDimensional_span_of_leviRestrictions iV l hKmax hK L₀ E A ?_ ?_
  · intro f hf
    exact ⟨fun y hy x => hf.1.1 y (Subgroup.mem_sup_left hy) x, hf.2.1, hf.2.2.2⟩
  intro b a
  obtain ⟨E', hE', hProfile⟩ := compact_profile_leviRestriction iV l hV H v hv E hE b a
  obtain ⟨p, hp, hAction⟩ := hCenter F G Q M V q iV l hG hq hV hl hmul hsmooth hsM hcalc hcM a
  obtain ⟨I, hI, hAnn⟩ :=
    exists_cofinite_center_ideal_of_leviRestriction l iV hcalc hcM a p hp hAction J hJ
  let j := map F M G (l ≫ q)
  let jf := M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
  let t := ofFinite F G b * ofInfinite F G a
  let hconj := (MulAut.conj b⁻¹).toMonoidHom.comp jf
  let LM : OpenSubgroup (FiniteAdelicGroupPoints F M) :=
    ⟨L.comap hconj, hL.preimage (show Continuous hconj from
      (IsTopologicalGroup.continuous_conj b⁻¹).comp (M.continuous_affinePointsTarget _ (l ≫ q)))⟩
  let ρM := ρ.restrict (l ≫ q)
  have hρM : IsClosedSubgroup ρM := (hl.isClosedSubgroup.comp hq.isClosedSubgroup).comp hρ
  refine ⟨_, hRational F M hl.isConnectedReductive ρM hρM hsM hcM LM H hH I hI E' hE', ?_⟩
  intro f hf
  let fM := translatedLeviRestriction (q := q) l t f
  have hLevel (bM : FiniteAdelicGroupPoints F M) (hbM : bM ∈ LM)
      (m : AdelicGroupPoints F M) : fM (m * ofFinite F M bM) = fM m := by
    let c := b⁻¹ * jf bM * b
    change b⁻¹ * jf bM * (b⁻¹)⁻¹ ∈ L at hbM
    rw [inv_inv] at hbM
    change f (j (m * ofFinite F M bM) * t) = f (j m * t)
    have hbc : b * c = jf bM * b := by simp only [c, ← mul_assoc, mul_inv_cancel, one_mul]
    have he : j (m * ofFinite F M bM) * t = (j m * t) * ofFinite F G c := by
      rw [map_mul]
      change j m * map F M G (l ≫ q) (ofFinite F M bM) * t = _
      rw [map_finite_inclusion]
      calc
        _ = j m * ofFinite F G (jf bM * b) * ofInfinite F G a := by
          rw [map_mul]
          simp only [t, jf, mul_assoc]
        _ = (j m * t) * ofFinite F G c := by
          rw [← hbc, map_mul]
          simp only [t, mul_assoc, (factors_commute F G a.val c).eq]
    rw [he]
    exact hf.2.1 c hbM _
  have hInv : IsLeftInvariantUnder F M (rationalSubgroup F M) fM := by
    rintro _ ⟨m₀, rfl⟩ m
    change f (j (rational F M m₀ * m) * t) = f (j m * t)
    rw [map_mul, mul_assoc]
    exact hf.1.1 _ (Subgroup.mem_sup_right ⟨m₀, rfl⟩) _
  let fSlice (bM : FiniteAdelicGroupPoints F M) : InfinitePlotSmoothFunctions F G :=
    ⟨functionInfiniteSlice F G f (jf bM * b), hf.1.2.1.2.1 (jf bM * b)⟩
  have hSlice (bM : FiniteAdelicGroupPoints F M) :
      functionInfiniteSlice F M fM bM =
        (infiniteLeviRestriction (q := q) l a (fSlice bM)).val := by
    funext x
    change f (map F M G (l ≫ q) (pair F M x bM) * (ofFinite F G b * ofInfinite F G a)) =
      f (pair F G (M.affinePointsTarget (l ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) x * a.val)
        (jf bM * b))
    rw [← mul_assoc, map_pair, ofFinite_eq_pair, ofInfinite_eq_pair, pair_mul, pair_mul,
      mul_one, mul_one]
  have hSmooth : IsAdelicSmoothFunction F M fM := by
    refine ⟨hf.1.2.1.1.comp (j.continuous.mul continuous_const), fun bM => ?_,
      LM.toSubgroup, LM.isOpen, hLevel⟩
    exact (hSlice bM).symm ▸ (infiniteLeviRestriction (q := q) l a (fSlice bM)).property
  apply Submodule.subset_span
  refine ⟨hInv, hSmooth, moderateGrowth_leviPullback (l ≫ q) hf.1.2.2.2.2 t, hLevel,
    ?_, hProfile f hf.1.1 hf.2.2.2⟩
  intro z hz bM hSmoothSlice
  have he : (⟨functionInfiniteSlice F M fM bM, hSmoothSlice⟩ : InfinitePlotSmoothFunctions F M) =
      infiniteLeviRestriction (q := q) l a (fSlice bM) := Subtype.ext (hSlice bM)
  rw [he]
  refine hAnn (fSlice bM) ?_ (fun z hz => hf.2.2.1 z hz (jf bM * b) _) z hz
  intro v x
  let y := V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v
  have hy : ofInfinite F G y ∈ parabolicQuotientSubgroup F q iV l :=
    Subgroup.mem_sup_left ⟨ofInfinite F V v, map_ofInfinite (iV ≫ q) v⟩
  change f (pair F G (y * x) (jf bM * b)) = f (pair F G x (jf bM * b))
  have hpoint : ofInfinite F G y * pair F G x (jf bM * b) =
      pair F G (y * x) (jf bM * b) := by
    rw [ofInfinite_eq_pair, pair_mul, one_mul]
  rw [← hpoint]
  exact hf.1.1 _ hy _

end Langlands.Automorphic.GroupSchemeFunctions
