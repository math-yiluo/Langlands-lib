import Langlands.Geometry.FormalGroup.DrinfeldActionChartFormula

/-! # Coefficient extension of Drinfeld's signed Frobenius and source map -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldResidue

open ValuativeRel CentralSimple ModuleLaw

variable {K D κ S T : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] [Field κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
  [CommRing S] [Algebra 𝒪[K] S] [CommRing T] [Algebra 𝒪[K] T]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D} {π : 𝒪[K]}
variable (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (θ : S →ₐ[𝒪[K]] T) {a b : κ →ₐ[𝒪[K]] S}

omit [ExpChar κ p] in
/-- Postcomposing a source and target residue map retains the specified shift equality. -/
theorem shift_comp_eq {n : ℤ} (e : shift n b = a) :
    shift n (θ.comp b) = θ.comp a :=
  (comp_shift θ n b).symm.trans (congrArg θ.comp e)

set_option maxHeartbeats 500000 in
private theorem signedFrameFrobenius_map_of_nonneg (n : ℤ) (hn : 0 ≤ n)
    (e : shift n b = a) :
    (OrderAction.QuasiIsogeny.ofIso (Φ.val.order.mapCompIso a θ)).trans
        (signedFrameFrobenius Φ p hcard hFrob n (shift_comp_eq θ e)) =
      ((signedFrameFrobenius Φ p hcard hFrob n e).map θ).trans
        (OrderAction.QuasiIsogeny.ofIso (Φ.val.order.mapCompIso b θ)) := by
  lift n to ℕ using hn
  subst a
  have hθ : shift_comp_eq θ (rfl : shift (n : ℤ) b = shift (n : ℤ) b) =
      (rfl : shift (n : ℤ) (θ.comp b) = θ.comp (shift (n : ℤ) b)) := rfl
  rw [hθ, signedFrameFrobenius_natCast, signedFrameFrobenius_natCast]
  apply OrderAction.QuasiIsogeny.ext
  change
    (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n (hFrob n) (θ.comp b)).hom.comp
        (OrderAction.RationalHom.ofHom (Φ.val.order.mapCompIso (shift (n : ℤ) b) θ).hom) =
      (OrderAction.RationalHom.ofHom (Φ.val.order.mapCompIso b θ).hom).comp
        (OrderAction.RationalHom.map θ (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n (hFrob n) b).hom)
  rw [shiftedFrameFrobeniusQuasiIsogeny_hom, shiftedFrameFrobeniusQuasiIsogeny_hom,
    OrderAction.RationalHom.map_ofHom, ← OrderAction.RationalHom.ofHom_comp,
    ← OrderAction.RationalHom.ofHom_comp]
  apply congrArg (OrderAction.RationalHom.ofHom (F := K))
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (shiftedFrameFrobeniusHom p hcard Φ.val.order n (θ.comp b)).val.toHom.toCoordinateMap.comp
      CoordinateMap.id =
    CoordinateMap.id.comp
      ((shiftedFrameFrobeniusHom p hcard Φ.val.order n b).val.toHom.toCoordinateMap.map θ.toRingHom)
  rw [CoordinateMap.comp_id, CoordinateMap.id_comp,
    shiftedFrameFrobeniusHom_coordinates p hcard Φ.val.order n (θ.comp b) (θ.comp b).toRingHom,
    shiftedFrameFrobeniusHom_coordinates p hcard Φ.val.order n b b.toRingHom,
    CoordinateMap.map_ringHom_comp]
  rfl

/-- Signed relative Frobenius commutes with coefficient extension through the
canonical comparisons for composite coefficient maps. -/
theorem signedFrameFrobenius_map (n : ℤ) (e : shift n b = a) :
    (OrderAction.QuasiIsogeny.ofIso (Φ.val.order.mapCompIso a θ)).trans
        (signedFrameFrobenius Φ p hcard hFrob n (shift_comp_eq θ e)) =
      ((signedFrameFrobenius Φ p hcard hFrob n e).map θ).trans
        (OrderAction.QuasiIsogeny.ofIso (Φ.val.order.mapCompIso b θ)) := by
  by_cases hn : 0 ≤ n
  · exact signedFrameFrobenius_map_of_nonneg Φ p hcard hFrob θ n hn e
  · have h := signedFrameFrobenius_map_of_nonneg Φ p hcard hFrob θ (-n) (by omega) (shift_reverse e)
    rw [← signedFrameFrobenius_symm Φ p hcard hFrob n e,
      ← signedFrameFrobenius_symm Φ p hcard hFrob n (shift_comp_eq θ e)] at h
    have hr := OrderAction.QuasiIsogeny.square_reverse _ _ _ _ h
    simpa only [← OrderAction.QuasiIsogeny.map_symm, OrderAction.QuasiIsogeny.symm_symm] using hr

variable (g : GL (Fin (reducedDegree K D)) K × Dˣ) (c : Φ.val.MatrixCoordinates)

/-- The inverse division and matrix factors form a rational endomorphism of the original frame. -/
def inverseActionHom : ModuleLaw.RationalHom K Φ.val.formalModule Φ.val.formalModule :=
  ModuleLaw.RationalHom.comp (c.quasiIsogeny g.1⁻¹).hom.val
    (rationalAction K D Φ.val.order ((g.2⁻¹ : Dˣ) : D))

/-- The signed Frobenius is followed by extension of the fixed-frame inverse action. -/
theorem actionSourceHom_eq {a b : κ →ₐ[𝒪[K]] S}
    (e : shift (DrinfeldAction.exponent K D g) b = a) :
    actionSourceHom Φ g p hcard hFrob c e =
      ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.map b (inverseActionHom Φ g c))
        (signedFrameFrobenius Φ p hcard hFrob (DrinfeldAction.exponent K D g) e).hom.val := by
  rw [inverseActionHom, ModuleLaw.RationalHom.map_comp, rationalAction_map_apply,
    ModuleLaw.RationalHom.comp_assoc]
  rfl

open ModuleLaw.RationalHom (comp comp_assoc map map_comp mapCompIso_natural ofHom) in
set_option maxHeartbeats 500000 in
/-- Coefficient extension gives the same whole source composite after identifying both
successive frame base changes with their composites. -/
theorem actionSourceHom_map (e : shift (DrinfeldAction.exponent K D g) b = a) :
    ModuleLaw.RationalHom.comp (actionSourceHom Φ g p hcard hFrob c (shift_comp_eq θ e))
        (ModuleLaw.RationalHom.ofHom (ModuleLaw.mapCompIso Φ.val.formalModule a θ).hom) =
      ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (ModuleLaw.mapCompIso Φ.val.formalModule b θ).hom)
        (ModuleLaw.RationalHom.map θ (actionSourceHom Φ g p hcard hFrob c e)) := by
  let n := DrinfeldAction.exponent K D g
  let newFrob := (signedFrameFrobenius Φ p hcard hFrob n (shift_comp_eq θ e)).hom.val
  let oldFrob := (signedFrameFrobenius Φ p hcard hFrob n e).hom.val
  let j₁ := ofHom (F := K) (ModuleLaw.mapCompIso Φ.val.formalModule a θ).hom
  let j₂ := ofHom (F := K) (ModuleLaw.mapCompIso Φ.val.formalModule b θ).hom
  let r := inverseActionHom Φ g c
  have hF : comp newFrob j₁ = comp j₂ (map θ oldFrob) :=
    congrArg (fun q => q.hom.val) (signedFrameFrobenius_map Φ p hcard hFrob θ n e)
  have hR : comp (map (θ.comp b) r) j₂ = comp j₂ (map θ (map b r)) :=
    mapCompIso_natural r b θ
  rw [actionSourceHom_eq, actionSourceHom_eq, map_comp]
  calc
    comp (comp (map (θ.comp b) r) newFrob) j₁ =
        comp (map (θ.comp b) r) (comp newFrob j₁) := comp_assoc _ _ _
    _ = comp (map (θ.comp b) r) (comp j₂ (map θ oldFrob)) :=
      congrArg (comp (map (θ.comp b) r)) hF
    _ = comp (comp (map (θ.comp b) r) j₂) (map θ oldFrob) := (comp_assoc _ _ _).symm
    _ = comp (comp j₂ (map θ (map b r))) (map θ oldFrob) :=
      congrArg (fun q => comp q (map θ oldFrob)) hR
    _ = comp j₂ (comp (map θ (map b r)) (map θ oldFrob)) := comp_assoc _ _ _

end Langlands.FormalGroup.LocalDivision.DrinfeldResidue
