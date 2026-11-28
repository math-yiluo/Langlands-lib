import Langlands.AlgebraicGeometry.AffineCechDeRhamSquareZeroPullback

/-! # Composition of corrected Čech–de Rham pullbacks on compatible covers -/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham.LocalPullbacks

open RelativeForms

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {h : Z ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}
  {W : Scheme.AffineOpenCover.{u} Z} {I : Ideal R}
  {β : U.I₀ → V.I₀} {δ : V.I₀ → W.I₀}
  (L : LocalPullbacks (f := f) (g := g) I β) (M : LocalPullbacks (f := g) (g := h) I δ)

/-- Compose the local pullbacks at corresponding vertices. -/
def comp : LocalPullbacks (f := f) (g := h) I (δ ∘ β) where
  sections τ i := (L.sections τ i).comp (M.sections (β ∘ τ) i)
  restrict_sections τ θ i := by
    rw [← AlgHom.comp_assoc, L.restrict_sections τ θ i, AlgHom.comp_assoc, AlgHom.comp_assoc]
    exact congrArg ((L.sections τ (θ i)).comp) (M.restrict_sections (β ∘ τ) θ i)
  congruent := by
    intro p τ i j x
    let a := M.sections (β ∘ τ) i x
    let b := M.sections (β ∘ τ) j x
    change L.sections τ i a - L.sections τ j b ∈ _
    rw [show L.sections τ i a - L.sections τ j b =
      (L.sections τ i a - L.sections τ j a) + L.sections τ j (a - b) by rw [map_sub]; abel]
    exact Ideal.add_mem _ (L.congruent τ i j a)
      (map_mem_extendedIdeal (L.sections τ j) (M.congruent (β ∘ τ) i j x))

@[simp]
lemma comp_sections {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :
    (L.comp M).sections τ i = (L.sections τ i).comp (M.sections (β ∘ τ) i) := rfl

variable (hI : I * I = ⊥)

private lemma contraction_comp {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1))
    (ω : Ω[(tupleSections h W ((δ ∘ β) ∘ τ))⁄R]) :
    (L.comp M).contraction hI τ i j ω =
      L.contraction hI τ i j (mapOne (M.sections (β ∘ τ) i) ω) +
        L.sections τ j (M.contraction hI (β ∘ τ) i j ω) := by
  let v := M.sections (β ∘ τ) i
  let a := L.sections τ i
  let b := L.sections τ j
  let w := M.sections (β ∘ τ) j
  let c := a.comp v
  let d := b.comp v
  let e := b.comp w
  have hcd (x : tupleSections h W ((δ ∘ β) ∘ τ)) :
      c x - d x ∈ I.map (algebraMap R (tupleSections f U τ)) := L.congruent τ i j (v x)
  have hde (x : tupleSections h W ((δ ∘ β) ∘ τ)) :
      d x - e x ∈ I.map (algebraMap R (tupleSections f U τ)) := by
    change b (v x) - b (w x) ∈ _
    rw [← map_sub]
    exact map_mem_extendedIdeal b (M.congruent (β ∘ τ) i j x)
  change contractDifferenceOne c e hI ((L.comp M).congruent τ i j) ω = _
  rw [← contractDifferenceOne_telescopes c d hI hcd e hde ((L.comp M).congruent τ i j)]
  exact congrArg₂ (· + ·)
    (contractDifferenceOne_precomp a b hI (L.congruent τ i j) v hcd ω)
    (contractDifferenceOne_postcomp v w hI (M.congruent (β ∘ τ) i j) b hde ω)

/-- Corrected degree-one maps on cochains compose on compatible covers. -/
lemma cochainOne_comp (z : C1 h W) :
    (L.comp M).cochainOne hI z = L.cochainOne hI (M.cochainOne hI z) := by
  refine Prod.ext (funext fun τ => ?_) (funext fun τ => ?_)
  · simp only [cochainOne_fst, comp_sections, AlgHom.comp_apply, map_add]
    have hre : restrictCochain (oneForms g) (M.cochainOne hI z).2 (β ∘ τ) (fun _ => 1) =
        mapOne (M.sections (β ∘ τ) 1)
          (restrictCochain (oneForms h) z.2 ((δ ∘ β) ∘ τ) (fun _ => 1)) := by
      let θ : Fin 1 → Fin 2 := fun _ => 1
      let ρ := restrictSections g V (β ∘ τ) θ
      let η := restrictSections h W ((δ ∘ β) ∘ τ) θ
      let a := M.sections ((β ∘ τ) ∘ θ) 0
      let b := M.sections (β ∘ τ) 1
      let ω : Ω[(tupleSections h W (((δ ∘ β) ∘ τ) ∘ θ))⁄R] := z.2 ((δ ∘ β) ∘ τ ∘ θ)
      change mapOne ρ (mapOne a ω) = mapOne b (mapOne η ω)
      calc
        _ = mapOne (ρ.comp a) ω := (mapOne_comp a ρ ω).symm
        _ = mapOne (b.comp η) ω :=
          congrArg (fun s => mapOne s ω) (M.restrict_sections (β ∘ τ) θ 0)
        _ = _ := mapOne_comp η b ω
    rw [hre]
    have hc := L.contraction_comp M hI τ 1 0
      (restrictCochain (oneForms h) z.2 ((δ ∘ β) ∘ τ) (fun _ => 1))
    let t := L.sections τ 0 (M.sections (β ∘ τ) 0 (z.1 ((δ ∘ β) ∘ τ)))
    refine (congrArg (t + ·) hc).trans ?_
    rw [add_comm (L.contraction hI τ 1 0 _) _]
    exact (add_assoc t _ _).symm
  · simp only [cochainOne_snd, comp_sections, mapOne_comp]
    rfl

variable [Smooth f] [IsSeparated f] [Finite U.I₀]
  [Smooth g] [IsSeparated g] [Finite V.I₀] [Smooth h] [IsSeparated h] [Finite W.I₀]

/-- The degree-one cohomology maps for the composite lift system compose. -/
theorem pullbackH1_comp :
    (L.comp M).pullbackH1 hI = (L.pullbackH1 hI).comp (M.pullbackH1 hI) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (boundaries h W).mkQ_surjective x
  rw [LinearMap.comp_apply, pullbackH1_mk, pullbackH1_mk, pullbackH1_mk]
  apply congrArg ((boundaries f U).mkQ)
  exact Subtype.ext (L.cochainOne_comp M hI z.val)

end Langlands.AlgebraicGeometry.AffineCechDeRham.LocalPullbacks
