import Langlands.Global.AdelicSquareIntegrableCompactChange
import Langlands.Global.AdelicSquareIntegrableHeightExpansion

/-! # Height expansions under a finite change of compact -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

variable {K L : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- A finite square-integrable height expansion can be re-expressed using the height
of another maximal Iwasawa compact with the same infinite projection. -/
theorem HasSquareIntegrableHeightExpansion.of_compact_change
    (hK : IsIwasawaCompact (fam.p J) K) (hL : IsIwasawaCompact (fam.p J) L)
    (hKmax : IsMaximalCompactSubgroup F G K) (hLmax : IsMaximalCompactSubgroup F G L)
    (hinf : K.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom)
    {ψ : AdelicGroupPoints F G → ℂ}
    (hψ : fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hK ψ) :
    fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hL ψ := by
  classical
  let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  let P := fam.P J
  let M := fam.M J
  let U := fam.U J
  let pg := map F P G (fam.p J)
  let Γ := parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
  let Δ (g : AdelicGroupPoints F G) := hK.height g - hL.height g
  let δ (b : FiniteAdelicGroupPoints F G) := Δ (ofFinite F G b)
  let level : OpenSubgroup (FiniteAdelicGroupPoints F G) :=
    ⟨K.map (finite F G).toMonoidHom ⊓ L.map (finite F G).toMonoidHom,
      (IsMaximalCompactSubgroup.isOpen_finite F G K hKmax).inter
        (IsMaximalCompactSubgroup.isOpen_finite F G L hLmax)⟩
  have hOpen := IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G K L hLmax hinf
  have hΔfinite : (range Δ).Finite := hK.finite_range_height_sub hL hOpen
  obtain ⟨_, hFiber, _⟩ := hK.exists_parameterTwist_clopen_decomposition hL hOpen
  have hΔ (g : AdelicGroupPoints F G) : Δ g = δ (finite F G g) := by
    simpa only [pair_projections] using hK.height_sub_pair_eq_of_infinite_eq hL hKmax hLmax hinf
      (infinite F G g) (finite F G g)
  have hLeft (q : AdelicGroupPoints F P) (g : AdelicGroupPoints F G) : Δ (pg q * g) = Δ g := by
    dsimp only [Δ]
    rw [hK.height_map_mul, hL.height_map_mul]
    abel
  have hParabolic : Γ ≤ pg.toMonoidHom.range := by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact ⟨map F U P (fam.iU J) x, (map_comp_apply_of_hom (fam.iU J) x).symm⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨map F M P (fam.l J) (rational F M x),
        (map_comp_apply_of_hom (fam.l J) (rational F M x)).symm⟩
  have ofFinite_mem {C : Subgroup (AdelicGroupPoints F G)}
      (hC : IsMaximalCompactSubgroup F G C) {k : FiniteAdelicGroupPoints F G}
      (hk : k ∈ C.map (finite F G).toMonoidHom) : ofFinite F G k ∈ C := by
    rw [IsMaximalCompactSubgroup.eq_comap_prod F G C hC]
    change infinite F G (ofFinite F G k) ∈ C.map (infinite F G).toMonoidHom ∧
      finite F G (ofFinite F G k) ∈ C.map (finite F G).toMonoidHom
    rw [infinite_ofFinite, finite_ofFinite]
    exact ⟨one_mem _, hk⟩
  let cut (a : RealCharacterDual F P) (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :=
    if Δ g = a then φ g else 0
  have hCut (a : RealCharacterDual F P) {φ : AdelicGroupPoints F G → ℂ}
      (hφ : IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc
        (fam.p J) (fam.iU J) (fam.l J) φ) :
      IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc
        (fam.p J) (fam.iU J) (fam.l J) (cut a φ) := by
    let E : Set (FiniteAdelicGroupPoints F G) := {b | δ b = a}
    have hE : IsClopen E := (hFiber a).preimage (ofFinite F G).continuous
    have hEL (x : AdelicGroupPoints F G) (hx : x ∈ Γ) (g : AdelicGroupPoints F G) :
        finite F G (x * g) ∈ E ↔ finite F G g ∈ E := by
      obtain ⟨q, rfl⟩ := hParabolic hx
      change δ (finite F G (pg q * g)) = a ↔ δ (finite F G g) = a
      rw [← hΔ, ← hΔ, hLeft]
    have hER (k : FiniteAdelicGroupPoints F G) (hk : k ∈ level)
        (b : FiniteAdelicGroupPoints F G) : b * k ∈ E ↔ b ∈ E := by
      have hkK := ofFinite_mem hKmax (show k ∈ K.map (finite F G).toMonoidHom from hk.1)
      have hkL := ofFinite_mem hLmax (show k ∈ L.map (finite F G).toMonoidHom from hk.2)
      change Δ (ofFinite F G (b * k)) = a ↔ Δ (ofFinite F G b) = a
      rw [map_mul]
      dsimp only [Δ]
      rw [hK.height_mul_right _ hkK, hL.height_mul_right _ hkL]
    have hEq : (finite F G ⁻¹' E).indicator φ = cut a φ := by
      funext g
      simp only [Set.indicator, mem_preimage, E, mem_ofPred_eq, ← hΔ, cut]
    refine ⟨hEq ▸ hφ.1.indicator_finite E hE hEL level hER, ?_, ?_⟩
    · intro b hb g
      change cut a φ (pg (map F M P (fam.l J) b) * g) =
        parameterPower F P (halfModulusParameter F P) (map F M P (fam.l J) b) * cut a φ g
      dsimp only [cut]
      rw [hLeft]
      split_ifs with h
      · exact hφ.2.1 b hb g
      · rw [mul_zero]
    · let Q := RestrictionSplitCentre.CanonicalQuotient F M
      let S : Set (L × Q) := {z | Δ z.1.val = a}
      have hS : MeasurableSet S :=
        (hFiber a).2.measurableSet.preimage (measurable_subtype_coe.comp measurable_fst)
      let w (z : L × Q) :=
        ‖parameterPower F P (-modulusParameter F P) (map F M P (fam.l J) z.2.out)‖ *
          ‖φ (pg (map F M P (fam.l J) z.2.out) * z.1.val)‖ ^ 2
      have hw := hφ.2.2.indicator hS
      convert hw using 1
      funext z
      change _ = S.indicator w z
      rw [Set.indicator]
      dsimp only [w, S, mem_ofPred_eq, cut]
      rw [hLeft]
      split_ifs
      · rfl
      · simp
  obtain ⟨n, v, c, hv, heq⟩ := hψ
  let S := hΔfinite.toFinset
  let e := Fintype.equivFin (Fin n × S)
  let coeff (i : Fin n × S) (h : RealCharacterDual F P) := c i.1 (h + i.2.val)
  let form (i : Fin n × S) := cut i.2.val (v i.1)
  refine ⟨Fintype.card (Fin n × S), form ∘ e.symm, coeff ∘ e.symm, ?_, ?_⟩
  · intro i
    exact hCut _ (fam.isSquareIntegrableInducedForm_of_compact_change J rho hsmooth hcalc
      hK hL.isCompact hKmax hLmax hinf (hv (e.symm i).1))
  · intro g
    have hmem : Δ g ∈ S := hΔfinite.mem_toFinset.mpr (mem_range_self g)
    have hheight : hL.height g + Δ g = hK.height g := add_sub_cancel _ _
    rw [← Fintype.sum_equiv e (fun i => coeff i (hL.height g) * form i g) _
      (fun i => by simp [Function.comp_apply])]
    rw [heq, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (⟨Δ g, hmem⟩ : S)]
    · simp [coeff, form, cut, hheight]
    · intro a _ ha
      have hne : Δ g ≠ a.val := fun he => ha (Subtype.ext he.symm)
      simp [form, cut, hne]
    · simp

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- The finite square-integrable height expansion condition is invariant under
changes of maximal Iwasawa compact with a fixed infinite projection. -/
def AdelicSquareIntegrableHeightCompactChangeStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    (K L : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (fam.p J) K) (hL : IsIwasawaCompact (fam.p J) L),
    IsMaximalCompactSubgroup F G K → IsMaximalCompactSubgroup F G L →
    K.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (ψ : AdelicGroupPoints F G → ℂ),
      fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hK ψ ↔
        fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hL ψ

theorem adelicSquareIntegrableHeightCompactChange : AdelicSquareIntegrableHeightCompactChangeStatement := by
  intro F _ _ G _ _ _ fam J K L hK hL hKmax hLmax hinf N d rho hsmooth hcalc ψ
  exact ⟨StandardParabolicFamily.HasSquareIntegrableHeightExpansion.of_compact_change
    fam J rho hsmooth hcalc hK hL hKmax hLmax hinf,
    StandardParabolicFamily.HasSquareIntegrableHeightExpansion.of_compact_change
      fam J rho hsmooth hcalc hL hK hLmax hKmax hinf.symm⟩

end Langlands.Global
