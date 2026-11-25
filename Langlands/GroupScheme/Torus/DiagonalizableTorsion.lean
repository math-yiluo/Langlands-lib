import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.FiniteCharacterSeparation
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Langlands.AbelianScheme.Torsion

/-! # Actual integer torsion of diagonalizable groups -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Diagonalizable

section Characters

variable {M : Type u} [AddCommGroup M]

/-- A character is killed by `n` precisely when it kills all `n`-multiples. -/
theorem pow_eq_one_iff_annihilates_multiples {C : Type v} [CommGroup C]
    (χ : Multiplicative M →* C) (n : ℕ) :
    χ ^ n = 1 ↔ ∀ b ∈ FiniteCharacterSeparation.multiples (M := M) n, χ (.ofAdd b) = 1 := by
  constructor
  · intro h b hb
    obtain ⟨a, ha⟩ := hb
    rw [← ha]
    have hχ := congrArg (fun ψ : Multiplicative M →* C => ψ (.ofAdd a)) h
    simpa only [nsmulAddMonoidHom_apply, ofAdd_nsmul,
      map_pow, MonoidHom.pow_apply, MonoidHom.one_apply] using hχ
  · intro h
    apply MonoidHom.ext
    intro a
    have ha := h (n • a.toAdd) ⟨a.toAdd, rfl⟩
    simpa only [ofAdd_nsmul, ofAdd_toAdd, map_pow,
      MonoidHom.pow_apply, MonoidHom.one_apply] using ha

end Characters

variable (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] (n : ℕ)

/-- The character group of the full `n`-torsion, without saturation. -/
abbrev torsionCharacters := M ⧸ FiniteCharacterSeparation.multiples (M := M) n

/-- Characters identify torsion points with the annihilator of all multiples. -/
def torsionPointCharactersEquiv (U : Over (Spec R)) :
    torsionPoints (groupScheme R M).toGrp (n : ℤ) U ≃*
      subgroupAnnihilator (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U.left, ⊤))ˣ where
  toFun x := ⟨characterPointsEquiv R M U x.val, by
    apply (pow_eq_one_iff_annihilates_multiples _ n).mp
    rw [← map_pow, ← map_one (characterPointsEquiv R M U)]
    congr 1
    simpa only [zpow_natCast] using
      (mem_torsionPoints (groupScheme R M).toGrp (n : ℤ) U x.val).mp x.property⟩
  invFun χ := ⟨(characterPointsEquiv R M U).symm χ.val, by
    apply (mem_torsionPoints (groupScheme R M).toGrp (n : ℤ) U _).mpr
    rw [zpow_natCast]
    apply (characterPointsEquiv R M U).injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact (pow_eq_one_iff_annihilates_multiples χ.val n).mpr χ.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (characterPointsEquiv R M U).symm_apply_apply x.val
  right_inv χ := by
    apply Subtype.ext
    exact (characterPointsEquiv R M U).apply_symm_apply χ.val
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (characterPointsEquiv R M U) x.val y.val

/-- Points of the actual torsion scheme as annihilator characters. -/
def torsionCharacterPointsEquiv (U : Over (Spec R)) :
    (U ⟶ (torsion (groupScheme R M).toGrp (n : ℤ)).X) ≃*
      subgroupAnnihilator (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U.left, ⊤))ˣ :=
  (torsionPointsEquiv (groupScheme R M).toGrp (n : ℤ) U).trans
    (torsionPointCharactersEquiv R M n U)

/-- Coefficient restriction preserves the annihilator of integer multiples. -/
def torsionAnnihilatorRestrict {U U' : Over (Spec R)} (a : U' ⟶ U) :
    subgroupAnnihilator (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U.left, ⊤))ˣ →*
      subgroupAnnihilator (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U'.left, ⊤))ˣ where
  toFun χ := ⟨(Units.map a.left.appTop.hom.toMonoidHom).comp χ.val, by
    intro b hb
    change Units.map a.left.appTop.hom.toMonoidHom (χ.val (.ofAdd b)) = 1
    rw [χ.property b hb, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro b
    exact map_one (Units.map a.left.appTop.hom.toMonoidHom)
  map_mul' χ ψ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro b
    exact map_mul (Units.map a.left.appTop.hom.toMonoidHom) (χ.val b) (ψ.val b)

theorem torsionCharacterPointsEquiv_naturality
    {U U' : Over (Spec R)} (a : U' ⟶ U)
    (x : U ⟶ (torsion (groupScheme R M).toGrp (n : ℤ)).X) :
    torsionCharacterPointsEquiv R M n U' (a ≫ x) =
      torsionAnnihilatorRestrict R M n a (torsionCharacterPointsEquiv R M n U x) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  change characterPointsEquiv R M U'
      ((a ≫ x) ≫ (torsionι (groupScheme R M).toGrp (n : ℤ)).hom.hom) b =
    Units.map a.left.appTop.hom.toMonoidHom
      (characterPointsEquiv R M U
        (x ≫ (torsionι (groupScheme R M).toGrp (n : ℤ)).hom.hom) b)
  rw [Category.assoc]
  exact characterPointsEquiv_naturality R M a _ b.toAdd

/-- The quotient diagonalizable group has the same full torsion point model. -/
def torsionQuotientCharacterPointsEquiv (U : Over (Spec R)) :
    (U ⟶ (groupScheme R (torsionCharacters M n)).X) ≃*
      subgroupAnnihilator (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U.left, ⊤))ˣ :=
  (characterPointsEquiv R (torsionCharacters M n) U).trans
    (subgroupQuotientCharactersEquiv (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U.left, ⊤))ˣ)

theorem torsionQuotientCharacterPointsEquiv_naturality
    {U U' : Over (Spec R)} (a : U' ⟶ U)
    (x : U ⟶ (groupScheme R (torsionCharacters M n)).X) :
    torsionQuotientCharacterPointsEquiv R M n U' (a ≫ x) =
      torsionAnnihilatorRestrict R M n a
        (torsionQuotientCharacterPointsEquiv R M n U x) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  change characterPointsEquiv R (torsionCharacters M n) U' (a ≫ x)
      (.ofAdd (subgroupQuotientMap (FiniteCharacterSeparation.multiples (M := M) n) b.toAdd)) = _
  rw [characterPointsEquiv_naturality]
  rfl

/-- The full scheme-theoretic `n`-torsion of `D_R(M)` is `D_R(M/nM)`. -/
def torsionIso :
    torsion (groupScheme R M).toGrp (n : ℤ) ≅
      (groupScheme R (torsionCharacters M n)).toGrp :=
  isoOfPointModels
    (fun U : Over (Spec R) =>
      subgroupAnnihilator (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U.left, ⊤))ˣ)
    (fun a => torsionAnnihilatorRestrict R M n a)
    (torsionCharacterPointsEquiv R M n)
    (torsionQuotientCharacterPointsEquiv R M n)
    (torsionCharacterPointsEquiv_naturality R M n)
    (torsionQuotientCharacterPointsEquiv_naturality R M n)

/-- Positive torsion is finite for every finitely generated character group. -/
theorem torsion_isFinite [AddGroup.FG M] (hn : 0 < n) :
    IsFinite (torsion (groupScheme R M).toGrp (n : ℤ)).X.hom := by
  have : Finite (torsionCharacters M n) :=
    FiniteCharacterSeparation.finite_quotient hn.ne'
  rw [← Over.w (torsionIso R M n).hom.hom.hom]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

end Langlands.GroupScheme.Diagonalizable
