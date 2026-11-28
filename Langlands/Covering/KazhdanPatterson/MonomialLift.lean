import Langlands.Covering.KazhdanPatterson.MonomialCoordinates
import Mathlib.Data.List.OfFn

/-! # Corrected torus lifts and the monomial section -/

namespace Langlands.KazhdanPatterson

open Matrix (SpecialLinearGroup)
open Matrix.SpecialLinearGroup (toGL toGL_injective)
open GeneralLinear.Iwasawa (diagonalUnits)

universe u v

variable {r : ℕ} {F : Type u} [Field F] {W : Type v} [Group W]

/-- Simple Weyl and coroot lifts, with their projections to the actual special linear group. -/
structure MonomialLiftData (q : W →* SpecialLinearGroup (Fin (r + 1)) F) where
  simpleWeyl : Fin r → W
  simpleCoroot : Fin r → Fˣ → W
  simpleWeyl_projects : ∀ i, q (simpleWeyl i) = simpleWeylMatrix i
  simpleCoroot_projects : ∀ i x,
    q (simpleCoroot i x) = (slDiagonalCorootEquiv r F (Pi.mulSingle i x)).val
  simpleCoroot_one : ∀ i, simpleCoroot i 1 = 1

namespace MonomialLiftData

variable {q : W →* SpecialLinearGroup (Fin (r + 1)) F}

private theorem rootWeylMatrix_one_inv (i : Fin r) :
    (rootWeylMatrix (F := F) i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne 1)⁻¹ =
      simpleWeylMatrix i := by
  apply inv_eq_of_mul_eq_one_right
  apply toGL_injective
  rw [simpleWeylMatrix, toGL_rootWeylMatrix_mul_negOne, map_one]
  simp only [ite_self, inv_one]
  change diagonalUnits (1 : Fin (r + 1) → Fˣ) = 1
  exact map_one diagonalUnits

/-- Take the simple Weyl lift at `-1` and form the coroot lift by dividing on the right by
the root Weyl lift at `1`. -/
def ofRootWeylLifts (w : Fin r → Fˣ → W)
    (hw : ∀ i x, q (w i x) =
      rootWeylMatrix i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne x) :
    MonomialLiftData q where
  simpleWeyl i := w i (-1)
  simpleCoroot i x := w i x * (w i 1)⁻¹
  simpleWeyl_projects i := hw i (-1)
  simpleCoroot_projects i x := by
    rw [map_mul, map_inv, hw, hw, rootWeylMatrix_one_inv, simpleWeylMatrix]
    apply toGL_injective
    rw [toGL_rootWeylMatrix_mul_negOne]
    change diagonalUnits _ =
      toGL (slDiagonalMatrix r F ((simpleCorootCoordinates r Fˣ).symm (Pi.mulSingle i x)))
    apply Units.ext
    change Matrix.diagonal (fun j : Fin (r + 1) => (↑(if j = i.castSucc then x
      else if j = i.succ then x⁻¹ else 1) : F)) =
      Matrix.diagonal (fun j => (↑(((simpleCorootCoordinates r Fˣ).symm
        (Pi.mulSingle i x)).val j) : F))
    rw [simpleCorootCoordinates_symm_mulSingle]
    congr 1
    funext j
    have hi := (Fin.castSucc_lt_succ (i := i)).ne
    by_cases hja : j = i.castSucc
    · subst j
      simp [hi.symm]
    · by_cases hjb : j = i.succ
      · subst j
        simp [hi.symm]
      · simp [hja, hjb]
  simpleCoroot_one i := mul_inv_cancel _

variable (L : MonomialLiftData q)

/-- The multiplicative defect of the lift along a simple coroot. -/
def simpleCorootDefect (i : Fin r) (x y : Fˣ) : q.ker :=
  ⟨L.simpleCoroot i x * L.simpleCoroot i y * (L.simpleCoroot i (x * y))⁻¹, by
    change q (L.simpleCoroot i x * L.simpleCoroot i y * (L.simpleCoroot i (x * y))⁻¹) = 1
    rw [map_mul, map_mul, map_inv, L.simpleCoroot_projects, L.simpleCoroot_projects,
      L.simpleCoroot_projects]
    let c := ((slDiagonalTorus r F).subtype.comp
      (slDiagonalCorootEquiv r F).toMonoidHom).comp
        (MonoidHom.mulSingle (fun _ : Fin r => Fˣ) i)
    change c x * c y * (c (x * y))⁻¹ = 1
    rw [← map_mul, mul_inv_cancel]⟩

/-- The Banks–Levy–Sepanski lift of a simple coroot with parameter `x`. -/
def correctedCorootLift (i : Fin r) (x : Fˣ) : W :=
  L.simpleCoroot i x * (L.simpleCorootDefect i x x).val

theorem correctedCorootLift_projects (i : Fin r) (x : Fˣ) :
    q (L.correctedCorootLift i x) = (slDiagonalCorootEquiv r F (Pi.mulSingle i x)).val := by
  rw [correctedCorootLift, map_mul, L.simpleCoroot_projects,
    MonoidHom.mem_ker.mp (L.simpleCorootDefect i x x).property, mul_one]

@[simp]
theorem correctedCorootLift_one (i : Fin r) : L.correctedCorootLift i 1 = 1 := by
  simp [correctedCorootLift, simpleCorootDefect, L.simpleCoroot_one]

private def orderedCorootLift (x : Fin r → Fˣ) : W :=
  (List.ofFn (fun i => L.correctedCorootLift i (x i))).reverse.prod

private theorem orderedCorootLift_projects (x : Fin r → Fˣ) :
    q (L.orderedCorootLift x) = (slDiagonalCorootEquiv r F x).val := by
  let c := (slDiagonalTorus r F).subtype.comp (slDiagonalCorootEquiv r F).toMonoidHom
  change q (L.orderedCorootLift x) = c x
  rw [orderedCorootLift, map_list_prod, List.map_reverse, List.map_ofFn]
  change (List.ofFn (fun i => q (L.correctedCorootLift i (x i)))).reverse.prod = c x
  rw [show (fun i => q (L.correctedCorootLift i (x i))) = fun i => c (Pi.mulSingle i (x i))
    from funext (fun i => L.correctedCorootLift_projects i (x i))]
  rw [List.ofFn_comp', ← List.map_reverse, ← map_list_prod, List.prod_reverse, Fin.prod_ofFn,
    Finset.univ_prod_mulSingle]

/-- Lift a determinant-one diagonal by multiplying the corrected simple coroot lifts in
descending order of their indices. -/
noncomputable def torusLift (t : slDiagonalTorus r F) : W :=
  L.orderedCorootLift ((slDiagonalCorootEquiv r F).symm t)

theorem torusLift_projects (t : slDiagonalTorus r F) : q (L.torusLift t) = t.val := by
  rw [torusLift, L.orderedCorootLift_projects, MulEquiv.apply_symm_apply]

@[simp]
theorem torusLift_one : L.torusLift 1 = 1 := by
  simp [torusLift, orderedCorootLift, List.ofFn_const]

/-- Multiply the simple Weyl lifts along the chosen reduced word. -/
noncomputable def weylLift (w : Equiv.Perm (Fin (r + 1))) : W :=
  ((weylReducedWord w).map L.simpleWeyl).prod

theorem weylLift_projects (w : Equiv.Perm (Fin (r + 1))) :
    q (L.weylLift w) = weylMatrix w := by
  simp only [weylLift, weylMatrix, map_list_prod, List.map_map, Function.comp_def,
    L.simpleWeyl_projects]

@[simp]
theorem weylLift_one : L.weylLift 1 = 1 := by
  simp [weylLift]

/-- Lift the unique diagonal times Weyl decomposition of a special linear monomial. -/
noncomputable def monomialLift
    (m : {m : SpecialLinearGroup (Fin (r + 1)) F // IsSpecialLinearMonomial m}) : W :=
  let p := slMonomialWeylEquiv.symm m
  L.torusLift p.1 * L.weylLift p.2

theorem monomialLift_projects
    (m : {m : SpecialLinearGroup (Fin (r + 1)) F // IsSpecialLinearMonomial m}) :
    q (L.monomialLift m) = m.val := by
  let p := slMonomialWeylEquiv.symm m
  change q (L.torusLift p.1 * L.weylLift p.2) = m.val
  rw [map_mul, L.torusLift_projects, L.weylLift_projects]
  exact congrArg Subtype.val (slMonomialWeylEquiv.apply_symm_apply m)

@[simp]
theorem monomialLift_one : L.monomialLift ⟨1, isSpecialLinearMonomial_one⟩ = 1 := by
  simp [monomialLift]

end MonomialLiftData

end Langlands.KazhdanPatterson
