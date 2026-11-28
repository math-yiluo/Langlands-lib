import Langlands.AlgebraicGeometry.AffineCechDeRhamHodgeFrames
import Langlands.AlgebraicGeometry.AffineCechDeRhamHodgeSummandCocycles
import Langlands.AlgebraicGeometry.AffineCechDeRhamIdealPrimitives
import Langlands.AlgebraicGeometry.AffineSquareZeroDifferentialTwists
import Langlands.Cohomology.CechCup

/-! # Transition maps from cocycle representatives of a Hodge summand -/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp inter_le_apply)
open Langlands.Scheme
open scoped Pointwise

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

namespace Langlands.AlgebraicGeometry.AffineCechDeRham.HodgeSummandCocycles

open RelativeForms

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} [Smooth f] [IsSeparated f] [Finite U.I₀] {κ : Type u}
  {I : Ideal R} {b : κ → closedForms f U} {M : Submodule R (H1 f U)}
  (G : HodgeSummandCocycles I b M)

private abbrev affineSections (W : X.Opens) := (sectionAlgebras f).obj (op W)

private abbrev restrictTo {W W' : X.Opens} (e : W ≤ W') :
    affineSections (f := f) W' →ₐ[R] affineSections (f := f) W :=
  ((sectionAlgebras f).map (homOfLE e).op).hom

omit [Finite U.I₀] in
private lemma le_pair {W : X.Opens} {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) :
    W ≤ inter (coverOpens U) ![i, j] := by
  change W ≤ Langlands.Cohomology.Cech.inter (coverOpens U) ![i, j]
  rw [Langlands.Cohomology.Cech.inter_two]
  exact le_inf hi hj

private abbrev overlapValue {W : X.Opens} {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (k : κ) :
    affineSections (f := f) W :=
  restrictTo (f := f) (le_pair hi hj) ((G.representative k).val.1 ![i, j])

private lemma overlapValue_mem {W : X.Opens} {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (k : κ) :
    G.overlapValue hi hj k ∈ I.map (algebraMap R (affineSections (f := f) W)) :=
  map_mem_extendedIdeal (restrictTo (le_pair hi hj)) (G.representative_overlap_mem k ![i, j])

private lemma overlapValue_restrict {W W' : X.Opens} {i j : U.I₀} (d : W ≤ W')
    (hi : W' ≤ coverOpens U i) (hj : W' ≤ coverOpens U j) (k : κ) :
    restrictTo (f := f) d (G.overlapValue hi hj k) = G.overlapValue (d.trans hi) (d.trans hj) k := by
  change ((sectionAlgebras f).map (homOfLE d).op).hom
      (((sectionAlgebras f).map (homOfLE (le_pair hi hj)).op).hom _) = _
  rw [← AlgHom.comp_apply]
  change (((sectionAlgebras f).map (homOfLE (le_pair hi hj)).op ≫
    (sectionAlgebras f).map (homOfLE d).op).hom) _ = _
  rw [← Functor.map_comp]
  rfl

private lemma overlapValue_add {W : X.Opens} {i j l : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (hl : W ≤ coverOpens U l) (k : κ) :
    G.overlapValue hi hj k + G.overlapValue hj hl k = G.overlapValue hi hl k := by
  let P := (functions f) ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let z := G.representative k
  have hz : Langlands.Cohomology.Cech.d P (coverOpens U) 1 z.val.1 = 0 :=
    congrArg Prod.fst (show D1 f U z.val = 0 from z.property)
  exact Langlands.Cohomology.Cech.cocycle_add (P := P) (U := coverOpens U) (O := W) hz i j l
    (le_pair hi hj) (le_pair hj hl) (le_pair hi hl)

variable [Fintype κ] (E : SheafOfModules.free (R := X.ringCatSheaf) κ ≅ relativeDifferentials f)

private abbrev basisOn {W : X.Opens} (hW : IsAffineOpen W) := hodgeOneBasis f E W hW

/-- The contraction on an affine open in a pair of charts. Its value on
each original frame vector is the corresponding overlap function. -/
def overlapContraction {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) :
    Ω[(affineSections (f := f) W)⁄R] →ₗ[affineSections (f := f) W] affineSections (f := f) W :=
  (basisOn E hW).constr ℕ (G.overlapValue hi hj)

@[simp]
lemma overlapContraction_basis {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (k : κ) :
    G.overlapContraction E hW hi hj (basisOn E hW k) = G.overlapValue hi hj k :=
  Module.Basis.constr_basis _ _ _ _

lemma overlapContraction_mem {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (ω : Ω[(affineSections (f := f) W)⁄R]) :
    G.overlapContraction E hW hi hj ω ∈ I.map (algebraMap R (affineSections (f := f) W)) := by
  conv_rhs => rw [← (basisOn E hW).sum_repr ω, map_sum]
  apply Ideal.sum_mem
  intro k _
  rw [map_smul, overlapContraction_basis]
  exact Ideal.mul_mem_left _ _ (G.overlapValue_mem hi hj k)

lemma overlapContraction_restrict {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    {i j : U.I₀} (d : W ≤ W') (hi : W' ≤ coverOpens U i) (hj : W' ≤ coverOpens U j)
    (ω : Ω[(affineSections (f := f) W')⁄R]) :
    restrictTo (f := f) d (G.overlapContraction E hW' hi hj ω) =
      G.overlapContraction E hW (d.trans hi) (d.trans hj) (mapOne (restrictTo d) ω) := by
  conv_lhs => rw [← (basisOn E hW').sum_repr ω, map_sum, map_sum]
  conv_rhs => rw [← (basisOn E hW').sum_repr ω, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(G.overlapContraction E hW' hi hj).map_smul, overlapContraction_basis,
    (mapOne _).map_smulₛₗ, (G.overlapContraction E hW (d.trans hi) (d.trans hj)).map_smul,
    show mapOne (restrictTo (f := f) d) (basisOn E hW' k) = basisOn E hW k from
      hodgeOneBasis_restrict f E hW' hW d k,
    overlapContraction_basis]
  change restrictTo (f := f) d
    ((basisOn E hW').repr ω k * G.overlapValue hi hj k) = _
  rw [map_mul, overlapValue_restrict]
  rfl

lemma overlapContraction_add {W : X.Opens} (hW : IsAffineOpen W) {i j l : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (hl : W ≤ coverOpens U l) :
    G.overlapContraction E hW hi hj + G.overlapContraction E hW hj hl =
      G.overlapContraction E hW hi hl := by
  apply (basisOn E hW).ext
  intro k
  simp only [LinearMap.add_apply, overlapContraction_basis, overlapValue_add]

lemma overlapContraction_self {W : X.Opens} (hW : IsAffineOpen W) {i : U.I₀}
    (hi : W ≤ coverOpens U i) :
    G.overlapContraction E hW hi hi = 0 := by
  have h := G.overlapContraction_add E hW hi hi hi
  exact add_left_cancel (h.trans (add_zero _).symm)

variable (hI : I * I = ⊥)

/-- The transition on the section algebra of an affine open in two charts. -/
def transition {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) :
    affineSections (f := f) W →ₐ[R] affineSections (f := f) W :=
  addDerivation I hI (G.overlapContraction E hW hi hj) (G.overlapContraction_mem E hW hi hj)

lemma transition_sub_mem {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (x : affineSections (f := f) W) :
    G.transition E hI hW hi hj x - x ∈ I.map (algebraMap R (affineSections (f := f) W)) :=
  addDerivation_sub_mem I hI _ _ x

lemma transition_comp {W : X.Opens} (hW : IsAffineOpen W) {i j l : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) (hl : W ≤ coverOpens U l) :
    (G.transition E hI hW hj hl).comp (G.transition E hI hW hi hj) =
      G.transition E hI hW hi hl := by
  ext x
  change ((addDerivation I hI _ _).comp (addDerivation I hI _ _)) x = _
  rw [addDerivation_comp]
  simp only [transition, addDerivation_apply, LinearMap.add_apply]
  have ha := LinearMap.congr_fun (G.overlapContraction_add E hW hi hj hl) (dZero R _ x)
  rw [LinearMap.add_apply] at ha
  rw [add_comm (G.overlapContraction E hW hj hl (dZero R _ x)) _, ha]

@[simp]
lemma transition_self {W : X.Opens} (hW : IsAffineOpen W) {i : U.I₀}
    (hi : W ≤ coverOpens U i) :
    G.transition E hI hW hi hi = AlgHom.id R _ := by
  ext x
  simp only [transition, addDerivation_apply, overlapContraction_self, LinearMap.zero_apply,
    add_zero, AlgHom.id_apply]

lemma transition_restrict {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    {i j : U.I₀} (d : W ≤ W') (hi : W' ≤ coverOpens U i) (hj : W' ≤ coverOpens U j) :
    (restrictTo (f := f) d).comp (G.transition E hI hW' hi hj) =
      (G.transition E hI hW (d.trans hi) (d.trans hj)).comp (restrictTo d) := by
  ext x
  simp only [transition, AlgHom.comp_apply, addDerivation_apply, map_add]
  rw [G.overlapContraction_restrict E hW hW' d hi hj]
  exact congrArg (fun ω => restrictTo (f := f) d x +
    G.overlapContraction E hW (d.trans hi) (d.trans hj) ω) (mapOne_d (restrictTo d) x)

omit [Fintype κ] in
private lemma overlapValue_pair (k : κ) (τ : Fin 2 → U.I₀) :
    G.overlapValue (inter_le_apply τ 0) (inter_le_apply τ 1) k = (G.representative k).val.1 τ := by
  let P := (functions f) ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let a := (G.representative k).val.1
  have hτ : ![τ 0, τ 1] = τ := funext fun i => by fin_cases i <;> rfl
  change Langlands.Cohomology.Cech.res (P := P)
    (le_pair (inter_le_apply τ 0) (inter_le_apply τ 1)) (a ![τ 0, τ 1]) = a τ
  rw [Langlands.Cohomology.Cech.res_congr P (coverOpens U) hτ a _ le_rfl,
    Langlands.Cohomology.Cech.res_self]

include hI in
private lemma overlapContraction_kills_ideal {W : X.Opens} (hW : IsAffineOpen W) {i j : U.I₀}
    (hi : W ≤ coverOpens U i) (hj : W ≤ coverOpens U j) {ω : Ω[(affineSections (f := f) W)⁄R]}
    (hω : ω ∈ I • (⊤ : Submodule R Ω[(affineSections (f := f) W)⁄R])) :
    G.overlapContraction E hW hi hj ω = 0 := by
  let A := affineSections (f := f) W
  let C := (G.overlapContraction E hW hi hj).restrictScalars R
  change C ω = 0
  refine Submodule.smul_induction_on hω ?_ ?_
  · intro r hr w _
    rw [C.map_smul, Algebra.smul_def]
    have h := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R A) hr)
      (G.overlapContraction_mem E hW hi hj w)
    rwa [← Ideal.map_mul, hI, Ideal.map_bot, Ideal.mem_bot] at h
  · intro w v hw hv
    rw [map_add, hw, hv, add_zero]

variable (hframe : ∀ (k : κ) (σ : Fin 1 → U.I₀),
  (b k).val σ = basisOn E (isAffineOpen_inter f U σ) k)

include hI hframe in
/-- The overlap contraction of the form component of a representative is
its function component. Ideal perturbations of the original form vanish
under this contraction. -/
lemma overlapContraction_representative (k : κ) (τ : Fin 2 → U.I₀) (i : Fin 2) :
    G.overlapContraction E (isAffineOpen_inter f U τ) (inter_le_apply τ 0) (inter_le_apply τ 1)
      (restrictCochain (oneForms f) (G.representative k).val.2 τ (fun _ => i)) =
      (G.representative k).val.1 τ := by
  let θ : Fin 1 → Fin 2 := fun _ => i
  let σ := τ ∘ θ
  let hW := isAffineOpen_inter f U τ
  let hV := isAffineOpen_inter f U σ
  let d := inter_le_comp (U := coverOpens U) τ θ
  let ρ : Ω[(tupleSections f U σ)⁄R] →ₗ[R] Ω[(tupleSections f U τ)⁄R] :=
    ((oneForms f).map (homOfLE d).op).hom
  let C := G.overlapContraction E hW (inter_le_apply τ 0) (inter_le_apply τ 1)
  have h₀ : ρ ((G.representative k).val.2 σ - (b k).val σ) ∈
      I • (⊤ : Submodule R Ω[(tupleSections f U τ)⁄R]) :=
    Submodule.smul_top_le_comap_smul_top I ρ (G.representative_form_sub_mem k σ)
  have h₁ : C (ρ ((G.representative k).val.2 σ - (b k).val σ)) = 0 :=
    G.overlapContraction_kills_ideal E hI hW (inter_le_apply τ 0) (inter_le_apply τ 1) h₀
  rw [map_sub, map_sub, sub_eq_zero] at h₁
  change C (ρ ((G.representative k).val.2 σ)) = _
  rw [h₁]
  have hbase : ρ ((b k).val σ) = basisOn E hW k := by
    rw [hframe]
    exact hodgeOneBasis_restrict f E hV hW d k
  rw [hbase]
  exact (G.overlapContraction_basis E hW (inter_le_apply τ 0) (inter_le_apply τ 1) k).trans
    (G.overlapValue_pair k τ)

omit [Fintype κ] in
lemma representative_closed (k : κ) (σ : Fin 1 → U.I₀) :
    dOne R (tupleSections f U σ) ((G.representative k).val.2 σ) = 0 := by
  let z := G.representative k
  have hz : D1 f U z.val = 0 := z.property
  exact congrArg (fun c : C2 f U => c.2.2 σ) hz

include hframe in
/-- An affine transition carries the first local form of a representative
to the second on their overlap. -/
lemma transition_representative_forms (k : κ) (τ : Fin 2 → U.I₀) :
    mapOne (G.transition E hI (isAffineOpen_inter f U τ) (inter_le_apply τ 0) (inter_le_apply τ 1))
      (restrictCochain (oneForms f) (G.representative k).val.2 τ (fun _ => 0)) =
      restrictCochain (oneForms f) (G.representative k).val.2 τ (fun _ => 1) := by
  let z := G.representative k
  let θ : Fin 1 → Fin 2 := fun _ => 0
  let ω : Ω[(tupleSections f U τ)⁄R] := restrictCochain (oneForms f) z.val.2 τ θ
  let a : tupleSections f U τ := z.val.1 τ
  have hω : dOne R (tupleSections f U τ) ω = 0 := by
    change dOne R (tupleSections f U τ)
      (mapOne (restrictSections f U τ θ) (z.val.2 (τ ∘ θ))) = 0
    rw [dOne_natural, G.representative_closed k, map_zero]
  have hz : D1 f U z.val = 0 := z.property
  have hd := congrArg (fun c : C2 f U => c.2.1 τ) hz
  change (show Ω[(tupleSections f U τ)⁄R] from cechD U (oneForms f) 0 z.val.2 τ) -
    dZero R (tupleSections f U τ) a = 0 at hd
  rw [cechD_zero_eq_sub_restrict, sub_eq_zero, sub_eq_iff_eq_add] at hd
  have he := G.overlapContraction_representative E hI hframe k τ 0
  change mapOne (G.transition E hI _ _ _) ω = _
  rw [transition, mapOne_addDerivation_of_closed _ _ _ _ _ hω]
  rw [show G.overlapContraction E (isAffineOpen_inter f U τ) (inter_le_apply τ 0)
    (inter_le_apply τ 1) ω = a from he]
  exact (hd.trans (add_comm _ _)).symm

end Langlands.AlgebraicGeometry.AffineCechDeRham.HodgeSummandCocycles
