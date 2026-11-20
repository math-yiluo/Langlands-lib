import Langlands.Geometry.FormalGroup.ScalarTorsionPolarizationBaseChange

/-! # Integral similitudes of actual scalar torsion polarizations -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.GroupScheme Hom.FiniteKernelModel
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {L : ModuleLaw O R υ}
variable {π : O} {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}
variable {hL : L.IsPiDivisible π}

/-- The pulled back pairing is the original pairing with the indicated scalar
in its first argument, at each actual torsion level. -/
def IsTorsionSimilitude (f : Hom M N)
    (P : TorsionPrincipalPolarization hM) (Q : TorsionPrincipalPolarization hN)
    (a : O) : Prop :=
  ∀ (n : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x y : T ⟶ (hM.torsionSchemeInclusions.obj n).X),
      Q.toTorsionCartierDuality.pairing n
          (x ≫ (f.scalarTorsionSchemeMap hM hN n).toMul.hom.hom)
          (y ≫ (f.scalarTorsionSchemeMap hM hN n).toMul.hom.hom) =
        P.toTorsionCartierDuality.pairing n
          (x ≫ ((M.scalarHom a).scalarTorsionSchemeMap hM hM n).toMul.hom.hom) y

namespace IsTorsionSimilitude

variable {f : Hom M N} {g : Hom N L}
variable {P : TorsionPrincipalPolarization hM} {Q : TorsionPrincipalPolarization hN}
variable {W : TorsionPrincipalPolarization hL}
variable {a b : O}

theorem id (P : TorsionPrincipalPolarization hM) :
    (Hom.id M).IsTorsionSimilitude P P 1 := by
  intro n T x y
  rw [scalarHom_one, scalarTorsionSchemeMap_id]
  rfl

/-- Compose two integral maps and multiply their indicated multipliers. -/
theorem comp (hg : g.IsTorsionSimilitude Q W b) (hf : f.IsTorsionSimilitude P Q a) :
    (g.comp f).IsTorsionSimilitude P W (a * b) := by
  intro n T x y
  let A := (M.scalarHom a).scalarTorsionSchemeMap hM hM n
  let B := (M.scalarHom b).scalarTorsionSchemeMap hM hM n
  let C := (N.scalarHom b).scalarTorsionSchemeMap hN hN n
  let mapF := f.scalarTorsionSchemeMap hM hN n
  let mapG := g.scalarTorsionSchemeMap hN hL n
  have hs : B ≫ mapF = mapF ≫ C := by
    change (M.scalarHom b).scalarTorsionSchemeMap hM hM n ≫ f.scalarTorsionSchemeMap hM hN n =
      f.scalarTorsionSchemeMap hM hN n ≫ (N.scalarHom b).scalarTorsionSchemeMap hN hN n
    rw [← scalarTorsionSchemeMap_comp, ← scalarTorsionSchemeMap_comp, Hom.comp_scalarHom]
  have hab : (M.scalarHom (a * b)).scalarTorsionSchemeMap hM hM n = B ≫ A := by
    rw [scalarHom_mul, scalarTorsionSchemeMap_comp]
  have hx : (x ≫ mapF.toMul.hom.hom) ≫ C.toMul.hom.hom =
      (x ≫ B.toMul.hom.hom) ≫ mapF.toMul.hom.hom := by
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun k => x ≫ k.toMul.hom.hom) hs.symm
  rw [scalarTorsionSchemeMap_comp, hab]
  change W.toTorsionCartierDuality.pairing n
      (x ≫ mapF.toMul.hom.hom ≫ mapG.toMul.hom.hom)
      (y ≫ mapF.toMul.hom.hom ≫ mapG.toMul.hom.hom) =
    P.toTorsionCartierDuality.pairing n (x ≫ B.toMul.hom.hom ≫ A.toMul.hom.hom) y
  rw [← Category.assoc x mapF.toMul.hom.hom, ← Category.assoc y mapF.toMul.hom.hom]
  exact (hg n T (x ≫ mapF.toMul.hom.hom) (y ≫ mapF.toMul.hom.hom)).trans
    ((congrArg (fun u => Q.toTorsionCartierDuality.pairing n u (y ≫ mapF.toMul.hom.hom)) hx).trans
      ((hf n T (x ≫ B.toMul.hom.hom) y).trans
        (congrArg (fun u => P.toTorsionCartierDuality.pairing n u y)
          (Category.assoc x B.toMul.hom.hom A.toMul.hom.hom))))

set_option maxHeartbeats 800000 in
/-- The integral multiplier equation is preserved by arbitrary coefficient extension. -/
theorem baseChange (hf : f.IsTorsionSimilitude P Q a) (φ : R →ₐ[O] S) :
    (f.map φ).IsTorsionSimilitude (P.baseChange φ) (Q.baseChange φ) a := by
  intro n T x y
  let T₀ := (Over.map (coefficientSpecMap φ)).obj T
  let x₀ := hM.torsionPointBaseChangeEquiv φ n T x
  let y₀ := hM.torsionPointBaseChangeEquiv φ n T y
  let oldEquiv := Gm.pointsEquiv (Spec (CommRingCat.of R)) T₀
  let newEquiv := Gm.pointsEquiv (Spec (CommRingCat.of S)) T
  let dualP := P.toTorsionCartierDuality
  let dualQ := Q.toTorsionCartierDuality
  let f' := (f.map φ).scalarTorsionSchemeMap (hM.map φ) (hN.map φ) n
  let f₀ := f.scalarTorsionSchemeMap hM hN n
  let s := (M.scalarHom a).scalarTorsionSchemeMap hM hM n
  let s' := ((M.map φ).scalarHom a).scalarTorsionSchemeMap (hM.map φ) (hM.map φ) n
  have hF := hM.torsionPointBaseChangeEquiv_map φ hN (T := T) f₀ f'
    (hM.torsionPullbackIso_naturality φ hN f n)
  have hS : s' ≫ (hM.torsionPullbackIso φ n).hom =
      (hM.torsionPullbackIso φ n).hom ≫ (CommGroupScheme.baseChange (coefficientSpecMap φ)).map s := by
    simpa only [s, s', scalarHom_map] using hM.torsionPullbackIso_naturality φ hM (M.scalarHom a) n
  have hs := hM.torsionPointBaseChangeEquiv_map φ hM s s' hS x
  apply newEquiv.injective
  change newEquiv ((dualQ.baseChange φ).pairing n (x ≫ f'.toMul.hom.hom) (y ≫ f'.toMul.hom.hom)) =
    newEquiv ((dualP.baseChange φ).pairing n (x ≫ s'.toMul.hom.hom) y)
  have hl := dualQ.baseChange_pairing φ n T (x ≫ f'.toMul.hom.hom) (y ≫ f'.toMul.hom.hom)
  have hr := dualP.baseChange_pairing φ n T (x ≫ s'.toMul.hom.hom) y
  exact hl.trans ((congrArg₂ (fun x y => oldEquiv (dualQ.pairing n x y)) (hF x) (hF y)).trans
    ((congrArg oldEquiv (hf n T₀ x₀ y₀)).trans
      ((congrArg (fun x => oldEquiv (dualP.pairing n x y₀)) hs.symm).trans hr.symm)))

end IsTorsionSimilitude

end Langlands.FormalGroup.ModuleLaw.Hom
