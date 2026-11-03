import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

/-! # The gauge complex of two families of transition functions

Let `p : Y ⟶ Spec R` and let `𝒰` be an ordered affine cover of `Y`. For families of transition
functions `α` and `β` on `𝒰`, the gauge differential sends a family `b` of functions on the
opens of `𝒰` to the family
`b (t 0) * α (t 0) (t 1) - β (t 0) (t 1) * b (t 1)` on the intersections `U (t 0) ⊓ U (t 1)`,
indexed by the strictly increasing pairs `t` of `𝒰.Idx 1`. Its kernel consists of the families
intertwining `α` and `β` on the pairs `i < j`. The `R`-module structures on sections come from `p`.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.LineHom

variable {R : Type u} [CommRing R] {Y : Scheme.{u}}

/-- Degree-zero gauge coordinates: a function on each open of the cover. -/
@[nolint unusedArguments]
def GaugeC0 (_p : Y ⟶ Spec (.of R)) (𝒰 : Y.OrderedAffineCover) : Type u :=
  ∀ i : 𝒰.ι, Γ(Y, 𝒰.U i)

/-- Degree-one gauge coordinates: a function on each intersection `U (t 0) ⊓ U (t 1)` of an
increasing pair `t`. -/
@[nolint unusedArguments]
def GaugeC1 (_p : Y ⟶ Spec (.of R)) (𝒰 : Y.OrderedAffineCover) : Type u :=
  ∀ t : 𝒰.Idx 1, Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))

variable (p : Y ⟶ Spec (.of R)) (𝒰 : Y.OrderedAffineCover)

instance instGaugeComplex1 : AddCommGroup (GaugeC0 p 𝒰) :=
  inferInstanceAs (AddCommGroup (∀ i : 𝒰.ι, Γ(Y, 𝒰.U i)))

instance instGaugeComplex2 : AddCommGroup (GaugeC1 p 𝒰) :=
  inferInstanceAs (AddCommGroup (∀ t : 𝒰.Idx 1, Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))))

noncomputable instance instGaugeComplex3 : Module R (GaugeC0 p 𝒰) :=
  letI := fun i : 𝒰.ι ↦ Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U i)
  inferInstanceAs (Module R (∀ i : 𝒰.ι, Γ(Y, 𝒰.U i)))

noncomputable instance instGaugeComplex4 : Module R (GaugeC1 p 𝒰) :=
  letI := fun t : 𝒰.Idx 1 ↦
    Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))
  inferInstanceAs (Module R (∀ t : 𝒰.Idx 1, Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))))

/-- The scalar `r : R` as a function on an open `W`, through `p`. -/
noncomputable def scalarOn {W : Y.Opens} (r : R) : Γ(Y, W) :=
  (p.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)

lemma GaugeC0.add_apply (b c : GaugeC0 p 𝒰) (i : 𝒰.ι) : (b + c) i = b i + c i := rfl

lemma GaugeC0.smul_apply (r : R) (b : GaugeC0 p 𝒰) (i : 𝒰.ι) :
    (r • b) i = scalarOn p r * b i := rfl

lemma GaugeC1.add_apply (b c : GaugeC1 p 𝒰) (t : 𝒰.Idx 1) : (b + c) t = b t + c t := rfl

lemma GaugeC1.smul_apply (r : R) (b : GaugeC1 p 𝒰) (t : 𝒰.Idx 1) :
    (r • b) t = scalarOn p r * b t := rfl

lemma res_scalarOn {W W' : Y.Opens} (h : W' ≤ W) (r : R) :
    Y.presheaf.map (homOfLE h).op (scalarOn p r : Γ(Y, W)) = scalarOn p r := by
  simp only [scalarOn, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map]

variable {𝒰} in
/-- The gauge differential of two families of transition functions. -/
def gaugeD (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ) : GaugeC0 p 𝒰 →ₗ[R] GaugeC1 p 𝒰 where
  toFun b t :=
    Y.presheaf.map (homOfLE (inf_le_left : 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) ≤ 𝒰.U (t.1 0))).op
        (b (t.1 0)) * (α (t.1 0) (t.1 1) : Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) -
      (β (t.1 0) (t.1 1) : Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) *
        Y.presheaf.map (homOfLE (inf_le_right : 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) ≤ 𝒰.U (t.1 1))).op
          (b (t.1 1))
  map_add' b c := by
    funext t
    simp only [GaugeC0.add_apply, map_add]
    erw [GaugeC1.add_apply]
    beta_reduce
    ring
  map_smul' r b := by
    funext t
    simp only [GaugeC0.smul_apply, map_mul, res_scalarOn, RingHom.id_apply]
    erw [GaugeC1.smul_apply]
    beta_reduce
    ring

variable {𝒰} in
lemma gaugeD_apply (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ) (b : GaugeC0 p 𝒰)
    (t : 𝒰.Idx 1) :
    gaugeD p α β b t =
      Y.presheaf.map (homOfLE (inf_le_left : 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) ≤ 𝒰.U (t.1 0))).op
          (b (t.1 0)) * (α (t.1 0) (t.1 1) : Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) -
        (β (t.1 0) (t.1 1) : Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) *
          Y.presheaf.map (homOfLE (inf_le_right : 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) ≤ 𝒰.U (t.1 1))).op
            (b (t.1 1)) := rfl

end Langlands.AlgebraicGeometry.Picard.LineHom
